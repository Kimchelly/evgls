package evgls

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"net/url"
	"path/filepath"
	"regexp"
	"strings"
	"sync"

	"github.com/goccy/go-yaml/ast"
	"github.com/goccy/go-yaml/parser"
	"github.com/goccy/go-yaml/token"
	"github.com/santhosh-tekuri/jsonschema"

	"github.com/pkg/errors"

	"github.com/sourcegraph/go-lsp"
	"github.com/sourcegraph/jsonrpc2"
)

//  TODO: get aliases/anchors/merge keys working (low priority)

/*
textDocument/completion
textDocument/definition
textDocument/references

textDocument/didOpen
textDocument/didChange
textDocument/didClose
*/

type LanguageServer struct {
	jsonrpc2.Handler
}

func NewHandler() jsonrpc2.Handler {
	lsh := LanguageServerHandler{}
	return &LanguageServer{Handler: jsonrpc2.HandlerWithError(lsh.Handle)}
}

func (ls *LanguageServer) Handle(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request) {
	if isSynchronousRequest(req.Method) {
		ls.Handler.Handle(ctx, conn, req)
		return
	}
	go ls.Handler.Handle(ctx, conn, req)
}

func isSynchronousRequest(method string) bool {
	return false
}

type LanguageServerHandler struct {
	init      *lsp.ClientCapabilities
	isClosed  bool
	evgSchema *jsonschema.Schema
	mu        sync.RWMutex
}

const (
	codeServerNotInitialized = -32002
)

func (lsh *LanguageServerHandler) Handle(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request) (result interface{}, err error) {
	defer func() {
		if perr := recover(); perr != nil {
			err = errors.Errorf("panic: %s", perr)
		}
	}()
	defer func() {
		if result == nil && err == nil {
			log.Printf("sending nil response")
		}
		if result != nil {
			log.Printf("sending response: %#v", result)
		}
		if err != nil {
			log.Printf("sending err: %s", err)
		}

	}()
	log.Printf("received request: %s\n", req.Method)

	// Check if the language server has been initialized yet.
	lsh.mu.RLock()
	if lsh.init == nil && req.Method != "initialize" && req.Method != "exit" {
		lsh.mu.RUnlock()
		return nil, &jsonrpc2.Error{
			Message: "language server is not initialized",
			Code:    codeServerNotInitialized,
		}
	}
	lsh.mu.RUnlock()

	// Check if the language server has been shut down.
	lsh.mu.RLock()
	if lsh.isClosed {
		lsh.mu.RUnlock()
		return nil, errors.New("server is shut down")
	}
	lsh.mu.RUnlock()

	switch req.Method {
	case "initialize":
		// Request: initialize the language server. Must be sent before any
		// further requests.
		lsh.mu.RLock()
		if lsh.init != nil {
			lsh.mu.RUnlock()
			return nil, errors.New("language server is already initialized")
		}
		lsh.mu.RUnlock()

		if req.Params == nil {
			return nil, &jsonrpc2.Error{Code: jsonrpc2.CodeInvalidParams}
		}
		var params lsp.ClientCapabilities
		if err := json.Unmarshal(*req.Params, &params); err != nil {
			return nil, &jsonrpc2.Error{
				Message: errors.Wrap(err, "reading params").Error(),
				Code:    jsonrpc2.CodeInvalidParams,
			}
		}

		lsh.mu.Lock()
		lsh.init = &params
		lsh.mu.Unlock()

		return lsp.InitializeResult{
			Capabilities: lsp.ServerCapabilities{
				// Support autocompletion.
				// CompletionProvider: &lsp.CompletionOptions{
				//     TriggerCharacters: []string{"."},
				// },
				// Support go to definition.
				DefinitionProvider: true,
				// Support find references.
				ReferencesProvider: true,
				// Support hover (i.e. show documentation).
				HoverProvider: true,
			},
		}, nil
	case "initialized":
		// Notification: the client is initialized and ready to receive
		// requests.
		// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#initialize
		return nil, nil
	case "shutdown":
		// Notification: shut down the server.
		// https://microsoft.github.io/language-server-protocol/specifications/specification-3-14/#shutdown
		lsh.mu.RLock()
		lsh.mu.RUnlock()
		if lsh.isClosed {
			lsh.mu.RUnlock()
			return nil, &jsonrpc2.Error{
				Message: "language server is already shut down",
				Code:    jsonrpc2.CodeInvalidRequest,
			}
		}
		lsh.mu.RUnlock()

		lsh.mu.Lock()
		lsh.isClosed = true
		lsh.mu.Unlock()

		return nil, nil
	case "close":
		// Notification: close the client connection.
		return nil, conn.Close()
	case "textDocument/definition":
		// Request: go to definition.
		// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_definition
		if req.Params == nil {
			return nil, &jsonrpc2.Error{Code: jsonrpc2.CodeInvalidParams}
		}
		var params lsp.TextDocumentPositionParams
		if err := json.Unmarshal(*req.Params, &params); err != nil {
			return nil, &jsonrpc2.Error{
				Message: errors.Wrap(err, "reading params").Error(),
				Code:    jsonrpc2.CodeInvalidParams,
			}
		}

		// return lsh.handleDefinitionDebug(ctx, conn, req, params)
		return lsh.handleDefinition(ctx, conn, req, params)
	case "textDocument/references":
		// Request: find references.
		// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_references
		if req.Params == nil {
			return nil, &jsonrpc2.Error{Code: jsonrpc2.CodeInvalidParams}
		}
		var params lsp.ReferenceParams
		if err := json.Unmarshal(*req.Params, &params); err != nil {
			return nil, &jsonrpc2.Error{
				Message: errors.Wrap(err, "reading params").Error(),
				Code:    jsonrpc2.CodeInvalidParams,
			}
		}

		return lsh.handleReferences(ctx, conn, req, params)
	case "textDocument/hover":
		// Request: hover (i.e. show documentation)
		// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_hover
		if req.Params == nil {
			return nil, &jsonrpc2.Error{Code: jsonrpc2.CodeInvalidParams}
		}
		var params lsp.TextDocumentPositionParams
		if err := json.Unmarshal(*req.Params, &params); err != nil {
			return nil, &jsonrpc2.Error{
				Message: errors.Wrap(err, "reading params").Error(),
				Code:    jsonrpc2.CodeInvalidParams,
			}
		}

		return lsh.handleDocumentation(ctx, conn, req, params)
	default:
		return nil, &jsonrpc2.Error{
			Message: fmt.Sprintf("method '%s' not supported", req.Method),
			Code:    jsonrpc2.CodeMethodNotFound,
		}
	}
}

// evgReferenceKind represents a something that can be referenced within an
// Evergreen YAML (e.g. a name of a task under depends_on).
type evgReferenceKind string

const (
	// Ambiguity, yay?
	referenceKindTaskOrTaskGroup evgReferenceKind = "task_or_task_group"

	// No ambiguity, real yay!
	referenceKindTask         evgReferenceKind = "task"
	referenceKindFunction     evgReferenceKind = "function"
	referenceKindBuildVariant evgReferenceKind = "build_variant"
	referenceKindTaskGroup    evgReferenceKind = "task_group"

	// Things that have identifiers and can be referenced, but have no explicit
	// definition in the YAML.
	referenceKindDistro  evgReferenceKind = "distro"
	referenceKindCommand evgReferenceKind = "command"
	referenceKindTag     evgReferenceKind = "tag"
)

type nodePositionRefFinder struct {
	posToFind   token.Position
	rootVisitor *nodePositionRefVisitor
	found       *nodeRef
}

func (nf *nodePositionRefFinder) Visit(curr ast.Node) ast.Visitor {
	nf.rootVisitor = &nodePositionRefVisitor{
		finder:    nf,
		posToFind: nf.posToFind,
	}
	log.Printf("searching for ref at position: '%s'\n", yamlPosToString(nf.posToFind))
	return nf.rootVisitor
}

type nodePositionRefVisitor struct {
	finder    *nodePositionRefFinder
	posToFind token.Position
}

var (
	// Heh, regexp pain 🙈

	// Task name
	taskPath = regexp.MustCompile(`^\$\.tasks\[\d+\]\.name$`)
	// Task selector (i.e. task, task group, or tag) under BV def
	bvTaskSelectorPath = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.tasks\[\d+\](\.name)?`)
	// Task under task group def
	tgTaskPath = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.tasks\[\d+\]$`)

	// Execution task under display task def
	execTaskPath = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.display_tasks\[\d+\].execution_tasks\[\d+\]$`)

	// Dep name under task def, BV def, or BVTU def
	dependsOnTaskPath = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks\[\d+\]))\.depends_on\[\d+\](\.name)?`)

	// Dep BV under task def, BV def, or BVTU def
	dependsOnBVPath = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks\[\d+\]))\.depends_on\[\d+\]\.variant$`)

	// Task group def
	tgPath = regexp.MustCompile(`^\$\.(task_groups\[\d+\])\.name$`)

	// BV def
	bvPath = regexp.MustCompile(`^\$\.(buildvariants\[\d+\])\.name$`)

	// Func name under pre, post, timeout, task, or task group
	funcPath = regexp.MustCompile(`^\$\.((pre\[\d+\])|(post\[\d+\])|(timeout\[\d+\])|(tasks\[\d+\]\.commands\[\d+\])|(task_groups\[\d+\]\.((setup_group\[\d+\])|(setup_task\[\d+\])|(teardown_task\[\d+\])|(teardown_group\[\d+\])|(timeout\[\d+\]))))\.func$`)
	// Func def
	funcDefPath = regexp.MustCompile(`^\$\.functions\.[^.]+$`)

	// Command name under pre, post, timeout, task, task group, or func
	cmdPath = regexp.MustCompile(`^\$\.((pre\[\d+\])|(post\[\d+\])|(timeout\[\d+\])|(tasks\[\d+\]\.commands\[\d+\])|(functions\.[^.\[\]]+\[\d+\])|(task_groups\[\d+\]\.((setup_group\[\d+\])|(setup_task\[\d+\])|(teardown_task\[\d+\])|(teardown_group\[\d+\])|(timeout\[\d+\]))))\.command`)

	// Distro name under task def, BV def, or BVTU def (note: BVTU distros is
	// deprecated, so don't support it)
	distroPath = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks))\.run_on\[\d+\]$`)

	// Tag names under task def or BV def
	tagPath = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\]))\.tags\[\d+\]$`)
)

func (nv *nodePositionRefVisitor) Visit(curr ast.Node) ast.Visitor {
	if curr == nil {
		// Reached a dead end.
		return nil
	}
	if nv.finder.found != nil {
		// We already located the node.
		return nil
	}

	// Could optimize by skipping over this node tree if it doesn't cover the
	// position to find. Can use position + value to determine its range

	// TODO: a slightly smarter way to go about this could be to parse the
	// Evergreen parser project YAML, but include each value metadata about the
	// relevant line/column.

	currNodePos := curr.GetToken().Position
	// Note: probably should deal with scalars that are map keys instead of
	// values (since references are map values, not keys, minus functions, which
	// are the worst special case).
	_, isScalar := curr.(ast.ScalarNode)

	// Is on the same line and the character to locate is within the current
	// node's string. Furthermore, to disambiguate, we only want the scalar
	// value, not the enclosing sequence or mapping node.
	if isScalar &&
		nv.posToFind.Line == currNodePos.Line &&
		nv.posToFind.Column >= currNodePos.Column && nv.posToFind.Column <= currNodePos.Column+len(curr.String()) {

		nv.finder.found = &nodeRef{node: curr}

		// Use the YAML path (which is a string representing the path of nodes
		// down to this one) to determine the context of the current node being
		// referenced.
		// Reference: https://github.com/vmware-labs/yaml-jsonpath#syntax

		refMatches := refKindToMatchingNode(func(criterion string, col int) bool {
			return nv.posToFind.Column >= col && nv.posToFind.Column < col+len(criterion)
		})
		for refKind, getMatch := range refMatches {
			refID, pos, isMatch := getMatch(curr)
			if isMatch {
				nv.finder.found.refID = refID
				nv.finder.found.refKind = refKind
				nv.finder.found.pos = *pos
				break
			}
		}

		return nil
	}

	// Give up if we've already passed the search position.
	if nv.posToFind.Line < currNodePos.Line {
		return nil
	}

	return &nodePositionRefVisitor{
		finder:    nv.finder,
		posToFind: nv.posToFind,
	}
}

type nodeDefFinder struct {
	refIDToFind   string
	refKindToFind evgReferenceKind
	rootVisitor   *nodeDefVisitor
	found         *nodeRef
}

func (nf *nodeDefFinder) Visit(curr ast.Node) ast.Visitor {
	nf.rootVisitor = &nodeDefVisitor{
		finder:        nf,
		refIDToFind:   nf.refIDToFind,
		refKindToFind: nf.refKindToFind,
	}
	log.Printf("searching for ref: %s %s\n", nf.refKindToFind, nf.refIDToFind)
	return nf.rootVisitor
}

type nodeDefVisitor struct {
	finder        *nodeDefFinder
	refIDToFind   string
	refKindToFind evgReferenceKind
}

func (nv *nodeDefVisitor) Visit(curr ast.Node) ast.Visitor {
	if curr == nil {
		// Reached a dead end.
		return nil
	}
	if nv.finder.found != nil {
		// We already located the node.
		return nil
	}

	path := curr.GetPath()
	log.Printf("checking node path for matching ref: %s\n", path)

	// See if the path matches the necessary path to the definition. If not,
	// skip this node tree entirely.
	pathPrefixOptimization := refKindToDefPrefixOptimization(nv.refKindToFind)
	var hasPathPrefix bool
	splitPath := strings.Split(path, ".")
	if len(pathPrefixOptimization) == 0 {
		// Since this is just an optimization, skip optimizing if we have no
		// prefix to optimize with.
		hasPathPrefix = true
	}

findPrefixPath:
	for _, pathPrefix := range pathPrefixOptimization {
		splitPathPrefix := strings.Split(pathPrefix, ".")

		// Node path is longer than path prefix, so it can't be a match.
		if len(splitPath) > len(splitPathPrefix) {
			continue
		}

		for i := range splitPathPrefix {
			if i > len(splitPath)-1 {
				// Node path is shorter than full pattern, but it still matches
				// the prefix pattern.
				hasPathPrefix = true
				break findPrefixPath
			}
			// TODO: This would be smarter if it was a regexp to handle weird
			// cases like a map key called task_groups_abc instead of
			// task_groups, but I don't care enough to handle that.
			if !strings.HasPrefix(splitPath[i], splitPathPrefix[i]) {
				continue findPrefixPath
			}
		}

		// Didn't find any discontinuities, so it's either a prefix path or the
		// path itself.
		hasPathPrefix = true
		break
	}
	if !hasPathPrefix {
		log.Printf("path '%s' is not a path prefix\n", path)
		return nil
	}

	pathRegexp := refKindToDefPath(nv.refKindToFind)
	if pathRegexp == nil {
		log.Printf("cannot convert ref type '%s' to path regexp\n", nv.refKindToFind)
		return nil
	}
	// Look for a node that matches the expected YAML path to the definition and
	// whose value is the ID.
	// Function names are the black sheep of the YAML and use map keys instead
	// of sequences with name values. Specifically if it's a function, the map
	// key (and therefore the end of the node path) must be the ref ID.
	// Use the string value instead of the literal string to avoid quotation
	// marks (e.g. the YAML string "foo" should match the string value foo
	// without quotation marks).
	if pathRegexp.MatchString(path) && nv.refIDToFind == curr.GetToken().Value &&
		(nv.refKindToFind != referenceKindFunction || strings.HasSuffix(path, nv.refIDToFind)) {
		nv.finder.found = &nodeRef{
			refID:   nv.refIDToFind,
			refKind: nv.refKindToFind,
			node:    curr,
			pos:     *curr.GetToken().Position,
		}
		return nil
	}

	// If we've gone any further into the node tree, there's no match and we've
	// gone too far, so give up on this tree entirely.
	deeperPathRegexp := regexp.MustCompile(pathRegexp.String() + `\.`)
	if deeperPathRegexp.MatchString(path) {
		return nil
	}

	// Specifically for functions, if we've gotten to the functions level and
	// the last element is not the function name, give up.

	return &nodeDefVisitor{
		finder:        nv.finder,
		refIDToFind:   nv.refIDToFind,
		refKindToFind: nv.refKindToFind,
	}
}

var (
	defKindBVMatch       = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.name`)
	defKindFuncMatch     = regexp.MustCompile(`^\$\.functions\.[^.]+`)
	defKindTaskMatch     = regexp.MustCompile(`^\$\.tasks\[\d+\]\.name`)
	defKindTGMatch       = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.name`)
	defKindTaskOrTGMatch = regexp.MustCompile(`^\$\.((tasks\[\d+\]\.name)|(task_groups\[\d+\]\.name))`)
)

// refKindToDefPath returns the YAML definition path pattern for a particular
// reference kind.
// TODO: This doesn't work if there are aliases/anchors, but whatever, this is
// bad code anyways. One potential implementation of go to definition could be
// to jump to the line where the definition dereferences the alias. Then would
// need special separate handling for jumping to an alias/anchor definition if
// the user needs to see the anchor.
func refKindToDefPath(kind evgReferenceKind) *regexp.Regexp {
	switch kind {
	case referenceKindBuildVariant:
		return defKindBVMatch
	case referenceKindFunction:
		// This intentionally doesn't include the function name because the
		// function name could include special characters that mess up the
		// path regexp... Sigh, functions... 😒
		return defKindFuncMatch
	case referenceKindTask:
		return defKindTaskMatch
	case referenceKindTaskOrTaskGroup:
		return defKindTaskOrTGMatch
	case referenceKindTaskGroup:
		return defKindTGMatch
	default:
		return nil
	}
}

// refKindToPrefixOptimization reduces the amount of searching necessary to find
// a matching YAML definition prefix path pattern.
func refKindToDefPrefixOptimization(kind evgReferenceKind) []string {
	switch kind {
	case referenceKindBuildVariant:
		return []string{"$.buildvariants.name"}
	case referenceKindFunction:
		// Functions are actually the worst, so we have to allow matching any
		// arbitrary function name. Because Walk iterates through sibling nodes
		// in order, we'll only know if we can stop traversing the node tree if
		// we've checked all the function names.
		return []string{fmt.Sprintf("$.functions.")}
	case referenceKindTask:
		return []string{"$.tasks.name"}
	case referenceKindTaskGroup:
		return []string{"$.task_groups.name"}
	case referenceKindTaskOrTaskGroup:
		return []string{"$.tasks.name", "$.task_groups.name"}
	default:
		return nil
	}
}

// Dummy implementation of go to definition just to verify that LSP is working
func (lsh *LanguageServerHandler) handleDefinitionDebug(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request, params lsp.TextDocumentPositionParams) ([]lsp.Location, error) {
	return []lsp.Location{
		{
			URI: params.TextDocument.URI,
			Range: lsp.Range{
				Start: lsp.Position{Line: 1, Character: 1},
				End:   lsp.Position{Line: 1, Character: 2},
			},
		},
	}, nil
}

// TODO: For more optimized lookup, could cache files and apply diffs to the
// initial parsing rather than reading the entire thing all over again. Oh well,
// correctness is more important for now.
func (lsh *LanguageServerHandler) handleDefinition(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request, params lsp.TextDocumentPositionParams) ([]lsp.Location, error) {
	filepath, err := uriToFilepath(params.TextDocument.URI)
	if err != nil {
		return nil, errors.Wrapf(err, "getting filepath from URI '%s'", params.TextDocument.URI)
	}

	parsed, err := parser.ParseFile(filepath, 0)
	if err != nil {
		return nil, errors.Wrapf(err, "parsing YAML file '%s'", filepath)
	}

	// Based on the position in the text document, ascertain what the identifier
	// and kind of reference that's being looked up (e.g. task, function, etc).

	yamlPos := convertLSPPositionToYAMLPosition(params.Position)
	refToFind, err := findRefFromPos(*parsed, yamlPos)
	if err != nil {
		return nil, errors.Wrap(err, "finding reference from position")
	}
	if refToFind.refID == "" {
		return nil, errors.Errorf("no ref ID could be extracted from node at position '%s'", yamlPosToString(yamlPos))
	}
	if refToFind.refKind == "" {
		return nil, errors.Errorf("no matching reference kind found for node at position '%s'", yamlPosToString(yamlPos))
	}
	if refToFind.refKind == referenceKindCommand || refToFind.refKind == referenceKindDistro || refToFind.refKind == referenceKindTag {
		return nil, errors.Errorf("cannot get go to definition for type '%s'", refToFind.refKind)
	}

	// Look up the definition in the relevant section of the YAML.

	var locs []lsp.Location
	for _, doc := range parsed.Docs {
		nf := &nodeDefFinder{
			refIDToFind:   refToFind.refID,
			refKindToFind: refToFind.refKind,
		}
		ast.Walk(nf, doc.Body)
		if nf.found == nil {
			log.Printf("no matching ref for ID '%s' of type '%s'", refToFind.refID, refToFind.refKind)
			continue
		}

		log.Printf("found matching ref node: %s at position '%s'\n", nf.found.node.String(), yamlPosToString(*nf.found.node.GetToken().Position))

		// Assuming the reference is on one line.
		start := *nf.found.node.GetToken().Position
		end := *nf.found.node.GetToken().Position
		end.Column = end.Column + len(nf.found.node.String())

		locs = append(locs, lsp.Location{
			// I'm assuming it's in the same file because includes aren't
			// supported.
			URI: params.TextDocument.URI,
			Range: lsp.Range{
				Start: convertYAMLPositionToLSPPosition(start),
				End:   convertYAMLPositionToLSPPosition(end),
			},
		})
	}

	return locs, nil
}

func (lsh *LanguageServerHandler) handleReferences(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request, params lsp.ReferenceParams) ([]lsp.Location, error) {
	filepath, err := uriToFilepath(params.TextDocument.URI)
	if err != nil {
		return nil, errors.Wrapf(err, "getting filepath from URI '%s'", params.TextDocument.URI)
	}

	parsed, err := parser.ParseFile(filepath, 0)
	if err != nil {
		return nil, errors.Wrapf(err, "parsing YAML file '%s'", filepath)
	}

	// Based on the position in the text document, ascertain what the identifier
	// and kind of reference that's being looked up (e.g. task, function, etc).

	yamlPos := convertLSPPositionToYAMLPosition(params.Position)
	refToFind, err := findRefFromPos(*parsed, yamlPos)
	if err != nil {
		return nil, errors.Wrap(err, "finding reference from position")
	}
	if refToFind.refID == "" {
		return nil, errors.Errorf("no ref ID could be extracted from node at position '%s'", yamlPosToString(yamlPos))
	}
	if refToFind.refKind == "" {
		return nil, errors.Errorf("no matching reference kind found for node at position '%s'", yamlPosToString(yamlPos))
	}

	// Find references where that identifier/kind could be used.

	var locs []lsp.Location
	for _, doc := range parsed.Docs {
		nf := &nodeRefFinder{
			refIDToFind:   refToFind.refID,
			refKindToFind: refToFind.refKind,
		}
		ast.Walk(nf, doc.Body)
		if len(nf.found) == 0 {
			log.Printf("no matching ref for ID '%s' of type '%s'", refToFind.refID, refToFind.refKind)
			continue
		}
		for _, found := range nf.found {
			log.Printf("found matching ref node: %s at position '%s'\n", found.node.String(), yamlPosToString(found.pos))

			// Assuming the reference is on one line.
			start := found.pos
			end := found.pos
			end.Column = end.Column + len(found.refID)

			locs = append(locs, lsp.Location{
				// I'm assuming it's in the same file because includes aren't
				// supported.
				URI: params.TextDocument.URI,
				Range: lsp.Range{
					Start: convertYAMLPositionToLSPPosition(start),
					End:   convertYAMLPositionToLSPPosition(end),
				},
			})
		}
	}

	return locs, nil
}

// findRefFromPos finds the reference from the identifier given at the position.
// For example, if given this YAML:
// buildvariants:
// - name: "bv0"
// And the position is at the "b" in "bv0", it will find the AST node
// corresponding to the string "bv0". Note that the position returned with the
// ref is the starting position of the identifier within the node, not the
// starting position of the YAML node itself, so the position starts at the b in
// bv0, not the quotation mark.
func findRefFromPos(parsed ast.File, yamlPos token.Position) (*nodeRef, error) {
	for _, doc := range parsed.Docs {
		nf := &nodePositionRefFinder{
			posToFind: yamlPos,
		}
		ast.Walk(nf, doc.Body)
		if nf.found == nil {
			continue
		}
		log.Printf("found matching positional node: %s at position '%s' with ref %s of type %s\n", nf.found.node.String(), yamlPosToString(*nf.found.node.GetToken().Position), nf.found.refID, nf.found.refKind)

		return nf.found, nil
	}
	return nil, errors.Errorf("no matching node found at position '%s'", yamlPos)
}

type nodeRef struct {
	refID   string
	refKind evgReferenceKind
	node    ast.Node
	pos     token.Position
}

type nodeRefFinder struct {
	refIDToFind   string
	refKindToFind evgReferenceKind
	rootVisitor   *nodeRefVisitor
	found         []nodeRef
}

func (nf *nodeRefFinder) Visit(curr ast.Node) ast.Visitor {
	nf.rootVisitor = &nodeRefVisitor{
		finder:        nf,
		refIDToFind:   nf.refIDToFind,
		refKindToFind: nf.refKindToFind,
	}
	log.Printf("searching for references to ID '%s' of type '%s'", nf.refIDToFind, nf.refKindToFind)
	return nf.rootVisitor
}

type nodeRefVisitor struct {
	finder        *nodeRefFinder
	refIDToFind   string
	refKindToFind evgReferenceKind
}

func (nv *nodeRefVisitor) Visit(curr ast.Node) ast.Visitor {
	if curr == nil {
		// Reached a dead end.
		return nil
	}

	_, isScalar := curr.(ast.ScalarNode)

	if isScalar {
		pos, isMatch := isMatchingRef(nv.refIDToFind, nv.refKindToFind, curr)
		if isMatch {
			nv.finder.found = append(nv.finder.found, nodeRef{
				refID:   nv.refIDToFind,
				refKind: nv.refKindToFind,
				node:    curr,
				pos:     *pos,
			})
		}
	}

	return nv
}

// isMatchingRef determines if a node's value matches a ref ID and kind.
func isMatchingRef(refIDToFind string, refKindToFind evgReferenceKind, node ast.Node) (*token.Position, bool) {
	// Determine what kind of reference this node is, if any.

	refMatches := refKindToMatchingNode(func(criterion string, col int) bool {
		tag := strings.TrimPrefix(strings.TrimPrefix(criterion, "!"), ".")
		return tag == refIDToFind
	})

	var nodeRefID string
	var nodeRefKind evgReferenceKind
	var nodeRefPos token.Position
	for refKind, getMatch := range refMatches {
		refID, pos, isMatch := getMatch(node)
		if isMatch {
			nodeRefID = refID
			nodeRefKind = refKind
			nodeRefPos = *pos
			break
		}
	}
	if nodeRefID == "" || nodeRefKind == "" || nodeRefPos.Line == 0 || nodeRefPos.Column == 0 {
		return nil, false
	}

	if nodeRefID == refIDToFind && nodeRefKind == refKindToFind {
		return &nodeRefPos, true
	}

	isCompatibleRefKind := (refKindToFind == referenceKindTaskOrTaskGroup && (nodeRefKind == referenceKindTask || nodeRefKind == referenceKindTaskGroup)) ||
		(refKindToFind == referenceKindTaskGroup && nodeRefKind == referenceKindTaskOrTaskGroup) ||
		(refKindToFind == referenceKindTask && nodeRefKind == referenceKindTaskOrTaskGroup)
	if nodeRefID == refIDToFind && isCompatibleRefKind {
		return &nodeRefPos, true
	}

	return nil, false
}

// ref kind -> func that returns if node matches or not.
func refKindToMatchingNode(isMatchingTagCriterion func(criterion string, col int) bool) map[evgReferenceKind]func(node ast.Node) (refID string, pos *token.Position, match bool) {
	return map[evgReferenceKind]func(node ast.Node) (refID string, pos *token.Position, match bool){
		referenceKindTaskOrTaskGroup: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if bvTaskSelectorPath.MatchString(path) && !strings.Contains(node.String(), ".") {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
		referenceKindTag: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()

			if tagPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}

			if !bvTaskSelectorPath.MatchString(path) {
				return "", nil, false
			}

			if !strings.Contains(node.String(), ".") {
				return "", nil, false
			}

			// If using tag selector syntax, determine which particular tag
			// it is within the string.
			pos := nodePosForRef(node)
			colWithinSelector := pos.Column
			for _, criterion := range strings.Split(tkn.Value, " ") {
				// Figure out from the position to find which tag is being
				// specifically requested.
				if isMatchingTagCriterion(criterion, colWithinSelector) {
					// Remove tag notation and any negation.
					tag := strings.TrimPrefix(strings.TrimPrefix(criterion, "!"), ".")
					return tag, &token.Position{
						Line:   pos.Line,
						Column: colWithinSelector + len(criterion) - len(tag),
					}, true
				}
				// Skip past criterion and whitespace.
				colWithinSelector = colWithinSelector + len(criterion) + 1
			}
			return "", nil, false
		},
		referenceKindTask: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if taskPath.MatchString(path) || tgTaskPath.MatchString(path) || execTaskPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			// Since the depends on task path can omit the name, it's ambiguous
			// unless you check that it's not a BV.
			if dependsOnTaskPath.MatchString(path) && !dependsOnBVPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
		referenceKindTaskGroup: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if tgPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
		referenceKindBuildVariant: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if bvPath.MatchString(path) || dependsOnBVPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
		referenceKindDistro: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if distroPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
		referenceKindFunction: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if funcPath.MatchString(path) || funcDefPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
		referenceKindCommand: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if cmdPath.MatchString(path) {
				return tkn.Value, nodePosForRef(node), true
			}
			return "", nil, false
		},
	}
}

// convertLSPPositionToYAMLPosition converts a 0-indexed LSP position to a
// 1-indexed YAML position.
func convertLSPPositionToYAMLPosition(pos lsp.Position) token.Position {
	return token.Position{
		Line:   pos.Line + 1,
		Column: pos.Character + 1,
	}
}

// convertLSPPositionToYAMLPosition converts a 1-indexed YAML position to a
// 0-indexed LSP position.
func convertYAMLPositionToLSPPosition(pos token.Position) lsp.Position {
	return lsp.Position{
		Line:      pos.Line - 1,
		Character: pos.Column - 1,
	}
}

func uriToFilepath(uri lsp.DocumentURI) (string, error) {
	if !strings.HasPrefix(string(uri), "file://") {
		return "", errors.Errorf("cannot handle document URIs that are not file paths")
	}

	uriWithoutFilePrefix := strings.TrimPrefix(string(uri), "file://")
	parsed, err := url.Parse(uriWithoutFilePrefix)
	if err != nil {
		return "", errors.Wrap(err, "parsing URI")
	}
	path := parsed.Path
	if !filepath.IsAbs(path) {
		return "", errors.Errorf("document URI must be an absolute path")
	}
	return path, nil
}

// nodePosForRef returns the position of the node's ref, adjusted for literal
// string marks (e.g. the YAML string "foo" should identify the starting
// position as f instead of the quotation mark).
func nodePosForRef(node ast.Node) *token.Position {
	pos := *node.GetToken().Position
	if node.GetToken().Indicator == token.QuotedScalarIndicator {
		// Since we're parsing the string literal, skip the leading quotation
		// mark, if any.
		pos.Column++
	}
	return &pos
}

func (lsh *LanguageServerHandler) handleDocumentation(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request, params lsp.TextDocumentPositionParams) (*lsp.Hover, error) {
	filepath, err := uriToFilepath(params.TextDocument.URI)
	if err != nil {
		return nil, errors.Wrapf(err, "getting filepath from URI '%s'", params.TextDocument.URI)
	}

	parsed, err := parser.ParseFile(filepath, 0)
	if err != nil {
		return nil, errors.Wrapf(err, "parsing YAML file '%s'", filepath)
	}

	// Based on the position in the text document, ascertain what is the scalar
	// being looked up.

	yamlPos := convertLSPPositionToYAMLPosition(params.Position)
	refToDocument, err := findRefFromPos(*parsed, yamlPos)
	if err != nil {
		return nil, errors.Wrap(err, "finding reference from position")
	}
	if refToDocument.node == nil {
		return nil, errors.Errorf("no matching node found")
	}

	// From the node, deduce what documentation to show.

	docs, err := nodeRefToDocs(refToDocument)
	if err != nil {
		return nil, errors.Wrap(err, "converting node path to documentation")
	}

	// Assuming the thing to document is on one line.
	start := *refToDocument.node.GetToken().Position
	end := *refToDocument.node.GetToken().Position
	end.Column = end.Column + len(refToDocument.node.String())

	return &lsp.Hover{
		Range: &lsp.Range{
			Start: convertYAMLPositionToLSPPosition(start),
			End:   convertYAMLPositionToLSPPosition(end),
		},
		Contents: docs,
	}, nil
}

func nodeRefToDocs(ref *nodeRef) ([]lsp.MarkedString, error) {
	allMatchingDocs := getAllMatchingDocs()
	for _, match := range allMatchingDocs {
		if match.isMatch(ref) {
			return match.docs, nil
		}
	}

	return nil, errors.Errorf("no matching docs found")
}

type matchingDocs struct {
	isMatch func(*nodeRef) bool
	docs    []lsp.MarkedString
}

var (
	bvSectionPath              = regexp.MustCompile(`^\$\.buildvariants$`)
	bvTasksSectionPath         = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.tasks$`)
	taskSectionPath            = regexp.MustCompile(`^\$\.tasks$`)
	tgSectionPath              = regexp.MustCompile(`^\$\.task_groups$`)
	tgTasksSectionPath         = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.tasks`)
	runOnSectionPath           = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks))\.run_on$`)
	funcSectionPath            = regexp.MustCompile(`^\$\.functions$`)
	dependsOnSectionPath       = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks\[\d+\]))\.depends_on$`)
	tagsSectionPath            = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\]))\.tags$`)
	cmdParamsPath              = regexp.MustCompile(`^\$\.((pre\[\d+\])|(post\[\d+\])|(timeout\[\d+\])|(tasks\[\d+\]\.commands\[\d+\])|(functions\.[^.\[\]]+\[\d+\])|(task_groups\[\d+\]\.((setup_group\[\d+\])|(setup_task\[\d+\])|(teardown_task\[\d+\])|(teardown_group\[\d+\])|(timeout\[\d+\]))))\.params`)
	displayTaskSectionPath     = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.display_tasks$`)
	displayTaskNamePath        = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.display_tasks\[\d+\]\.name$`)
	executionTasksSectionPath  = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.display_tasks\[\d+\]\.execution_tasks$`)
	preSectionPath             = regexp.MustCompile(`^\$\.pre$`)
	postSectionPath            = regexp.MustCompile(`^\$\.post$`)
	timeoutSectionPath         = regexp.MustCompile(`^\$\.timeout$`)
	tgSetupGroupSectionPath    = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.setup_group$`)
	tgSetupTaskSectionPath     = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.setup_task$`)
	tgTeardownTaskSectionPath  = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.teardown_task$`)
	tgTeardownGroupSectionPath = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.teardown_group$`)
	tgTimeoutSectionPath       = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.timeout$`)
)

const (
	bvExampleYAML = `
buildvariants:
  - name: my-build-variant
    run_on:
      - ubuntu2204-small
    tasks:
      - name: my-task
`
	taskExampleYAML = `
tasks:
  - name: my-task
    commands:
      - command: shell.exec
        params:
          script: echo hello world
`
	runOnExampleYAML = `
run_on:
  - ubuntu2204
`
	tgExampleYAML = `
task_groups:
  - name: my-task-group
    tasks:
      - task-in-task-group0
      - task-in-task-group1
    setup_group:
      - command: shell.exec
        params:
          script: echo setup group
    setup_task:
      - command: shell.exec
        params:
          script: echo setup task
    teardown_task:
      - command: shell.exec
        params:
          script: echo teardown task
    teardown_group:
      - command: shell.exec
        params:
          script: echo teardown group
    timeout:
      - command: shell.exec
        params:
          script: echo timeout
`
	tgSetupGroupExampleYAML = `
setup_group:
  - command: shell.exec
    params:
	  script: echo setup group
`
	tgSetupTaskExampleYAML = `
setup_task:
  - command: shell.exec
    params:
	  script: echo setup task
`
	tgTeardownTaskExampleYAML = `
teardown_task:
  - command: shell.exec
    params:
	  script: echo teardown task
`
	tgTeardownGroupExampleYAML = `
teardown_group:
  - command: shell.exec
    params:
	  script: echo teardown group
`
	tgTimeoutExampleYAML = `
timeout:
  - command: shell.exec
    params:
	  script: echo timeout
`
	dependsOnExampleYAML = `
depends_on:
  - name: task-to-depend-on
    variant: buildvariant-of-task-to-depend-on
  - name: another-task-to-depend-on
`
	tagExampleYAML = `
tags:
  - tag0
  - tag1
`
	funcExampleYAML = `
functions:
  my-function:
    - command: shell.exec
      params:
        script: echo first command in the function
    - command: shell.exec
      params:
        script: echo second command in the function
`
	cmdExampleYAML = `
- command: shell.exec
  params:
    script: echo hello world!
`

	preExampleYAML = `
pre:
  - command: shell.exec
    params:
      script: echo hello world!
`
	postExampleYAML = `
post:
  - command: shell.exec
    params:
      script: echo hello world!
`
	timeoutExampleYAML = `
timeout:
  - command: shell.exec
    params:
      script: echo hello world!
`
	funcRefExampleYAML = `
- func: my-func
  vars:
    my-var: some-value
    my-other-var: some-other-value
`
	displayTaskExampleYAML = `
buildvariants:
  - name: my-build-variant
    tasks:
      - name: my-task
      - name: my-other-task
    display_tasks:
      - name: my-display-task
        execution_tasks:
          - my-task
          - my-other-task
`
)

func getAllMatchingDocs() []matchingDocs {
	// TODO: Smarter and less janky way to do this may be to write a JSON schema
	// and correspond the YAML keys to YAML paths, but it might not work that
	// well given special YAML constructs (looking at you, anchors/aliases/merge
	// keys) and it would be quite complicated to handle conditional logic
	// without the newest version of the JSON schema spec, which is not
	// supported by Go libraries yet... Maybe next Skunkworks lol
	// https://json-schema.org/learn/miscellaneous-examples
	return []matchingDocs{
		{
			// Build variants section
			isMatch: func(ref *nodeRef) bool {
				return bvSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Build variant definitions. Build variants are a set of tasks run on a given platform. Each build variant has control over which tasks it runs, what distro it runs on, and what expansions it uses.",
				},
				{
					Language: "yaml",
					Value:    bvExampleYAML,
				},
			},
		},
		{
			// Build variant name
			isMatch: func(ref *nodeRef) bool {
				return defKindBVMatch.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The name of the build variant.",
				},
				{
					Language: "yaml",
					Value:    bvExampleYAML,
				},
			},
		},
		{
			// Build variant tasks
			isMatch: func(ref *nodeRef) bool {
				return bvTasksSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The selectors for the task(s) to run in the build variant.",
				},
				{
					Language: "yaml",
					Value:    bvExampleYAML,
				},
			},
		},
		{
			// Run on section
			isMatch: func(ref *nodeRef) bool {
				return runOnSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The name(s) of the distro(s) to run on.",
				},
				{
					Language: "yaml",
					Value:    runOnExampleYAML,
				},
			},
		},
		{
			// Tasks section
			isMatch: func(ref *nodeRef) bool {
				return taskSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Task definitions. A task is any discrete job you want Evergreen to run, typically a build, test suite, or deployment of some kind. They are the smallest unit of parallelization within Evergreen. Each task is made up of a list of commands/functions. Currently we include commands for interacting with git, running shell scripts, parsing test results, and manipulating Amazon S3.",
				},
				{
					Language: "yaml",
					Value:    taskExampleYAML,
				},
			},
		},
		{
			// Task name
			isMatch: func(ref *nodeRef) bool {
				return defKindTaskMatch.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The name of the task.",
				},
				{
					Language: "yaml",
					Value:    bvExampleYAML,
				},
			},
		},
		{
			// Task group section
			isMatch: func(ref *nodeRef) bool {
				return tgSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Task groups pin groups of tasks to sets of hosts. When tasks run in a task group, the task directory is not removed between tasks, which allows tasks in the same task group to share state, which can be useful for purposes such as reducing the amount of time running expensive setup and teardown for every single task. A task group contains arguments to set up and tear down both the entire group and each individual task. Tasks in a task group will not run the pre and post blocks in the YAML file; instead, the tasks will run the task group's setup and teardown blocks.",
				},
				{
					Language: "yaml",
					Value:    tgExampleYAML,
				},
			},
		},
		{
			// Task group name
			isMatch: func(ref *nodeRef) bool {
				return defKindTGMatch.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The name of the task group.",
				},
				{
					Language: "yaml",
					Value:    tgExampleYAML,
				},
			},
		},
		{
			// Task group tasks section
			isMatch: func(ref *nodeRef) bool {
				return tgTasksSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The tasks to run in the task group.",
				},
				{
					Language: "yaml",
					Value:    tgExampleYAML,
				},
			},
		},
		{
			// Task group setup group section
			isMatch: func(ref *nodeRef) bool {
				return tgSetupGroupSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Commands to run prior to running this task group. These commands run once per host that's running tasks in the task group.",
				},
				{
					Language: "yaml",
					Value:    tgSetupGroupExampleYAML,
				},
			},
		},
		{
			// Task group setup task section
			isMatch: func(ref *nodeRef) bool {
				return tgSetupTaskSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Commands to run prior to running each task in the task group.",
				},
				{
					Language: "yaml",
					Value:    tgSetupTaskExampleYAML,
				},
			},
		},
		{
			// Task group teardown task section
			isMatch: func(ref *nodeRef) bool {
				return tgTeardownTaskSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Commands to run after running each task in the task group.",
				},
				{
					Language: "yaml",
					Value:    tgTeardownTaskExampleYAML,
				},
			},
		},
		{
			// Task group teardown group section
			isMatch: func(ref *nodeRef) bool {
				return tgTeardownGroupSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Commands to run after running this task group. These commands run once per host that's running tasks in the task group.",
				},
				{
					Language: "yaml",
					Value:    tgTeardownGroupExampleYAML,
				},
			},
		},
		{
			// Task group timeout section
			isMatch: func(ref *nodeRef) bool {
				return tgTimeoutSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Define a list of commands to run when a task in the task group times out.",
				},
				{
					Language: "yaml",
					Value:    tgTimeoutExampleYAML,
				},
			},
		},
		{
			// Depends on section
			isMatch: func(ref *nodeRef) bool {
				return dependsOnSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Dependencies on other tasks. A task can be made to depend on other tasks by adding the depended on tasks to the task.",
				},
				{
					Language: "yaml",
					Value:    dependsOnExampleYAML,
				},
			},
		},
		{
			// Depends on BV (has to come before checking task due to ambiguity
			// if depends on specifies just a task name).
			isMatch: func(ref *nodeRef) bool {
				return dependsOnBVPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Name of the build variant to depend on.",
				},
				{
					Language: "yaml",
					Value:    dependsOnExampleYAML,
				},
			},
		},
		{
			// Depends on task
			isMatch: func(ref *nodeRef) bool {
				return dependsOnTaskPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) Name of the task to depend on.",
				},
				{
					Language: "yaml",
					Value:    dependsOnExampleYAML,
				},
			},
		},
		{
			// Tags section
			isMatch: func(ref *nodeRef) bool {
				return tagsSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Tags for the task. Tags are defined as an array as part of a task or variant definition. Tags should be self-explanatory and human-readable.",
				},
				{
					Language: "yaml",
					Value:    tagExampleYAML,
				},
			},
		},
		{
			// Functions section
			isMatch: func(ref *nodeRef) bool {
				return funcSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Function definitions. Functions are a simple way to group a set of commands together for reuse.",
				},
				{
					Language: "yaml",
					Value:    funcExampleYAML,
				},
			},
		},
		{
			// Command (generic)
			isMatch: func(ref *nodeRef) bool {
				// Since the ref finder only detects scalars and doesn't
				// distinguish between map keys vs. values, this has to check
				// the map key.
				return ref.refID == "command" && cmdPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The name of the command to run.",
				},
				{
					Language: "yaml",
					Value:    cmdExampleYAML,
				},
			},
		},
		{
			// Command params (generic)
			isMatch: func(ref *nodeRef) bool {
				return cmdParamsPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The params to pass to the command.",
				},
				{
					Language: "yaml",
					Value:    cmdExampleYAML,
				},
			},
		},
		{
			// Command (shell.exec)
			isMatch: func(ref *nodeRef) bool {
				return ref.refKind == referenceKindCommand && ref.refID == "shell.exec"
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "The shell.exec command runs a shell script.",
				},
				{
					Language: "yaml",
					Value:    cmdExampleYAML,
				},
			},
		},
		{
			// Function ref
			isMatch: func(ref *nodeRef) bool {
				return funcPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "The name of the function to run.",
				},
				{
					Language: "yaml",
					Value:    funcRefExampleYAML,
				},
			},
		},
		{
			// Pre section
			isMatch: func(ref *nodeRef) bool {
				return preSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Define a list of commands to run at the beginning of every task. Does not run for task groups.",
				},
				{
					Language: "yaml",
					Value:    preExampleYAML,
				},
			},
		},
		{
			// Post section
			isMatch: func(ref *nodeRef) bool {
				return postSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Define a list of commands to run at the end of every task. Does not run for task groups.",
				},
				{
					Language: "yaml",
					Value:    postExampleYAML,
				},
			},
		},
		{
			// Timeout section
			isMatch: func(ref *nodeRef) bool {
				return timeoutSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Define a list of commands to run when the task times out.",
				},
				{
					Language: "yaml",
					Value:    timeoutExampleYAML,
				},
			},
		},
		{
			// Display tasks section
			isMatch: func(ref *nodeRef) bool {
				return displayTaskSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "Display task definitions. Evergreen provides a way of grouping tasks into a single logical unit called a display task. These units are displayed in the UI as a single task. Only display tasks, not their execution tasks, are available to schedule patches against. Individual tasks in a display task are visible on the task page. Display task pages do not include any logs, though execution tasks' test results render on the display task's page. Users can restart the entire display task or only its failed execution tasks, but not individual execution tasks.",
				},
				{
					Language: "yaml",
					Value:    displayTaskExampleYAML,
				},
			},
		},
		{
			// Display task name
			isMatch: func(ref *nodeRef) bool {
				return displayTaskNamePath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) The name of the display task.",
				},
				{
					Language: "yaml",
					Value:    displayTaskExampleYAML,
				},
			},
		},
		{
			// Execution tasks
			isMatch: func(ref *nodeRef) bool {
				return executionTasksSectionPath.MatchString(ref.node.GetPath())
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "(Required) Execution task name(s).",
				},
				{
					Language: "yaml",
					Value:    displayTaskExampleYAML,
				},
			},
		},
		{
			isMatch: func(ref *nodeRef) bool {
				return false
			},
			docs: []lsp.MarkedString{
				{
					Language: "text",
					Value:    "",
				},
				{
					Language: "yaml",
					Value:    ``,
				},
			},
		},
	}
}

func yamlPosToString(pos token.Position) string {
	return fmt.Sprintf("%d:%d", pos.Line, pos.Column)
}

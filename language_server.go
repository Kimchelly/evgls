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

	"github.com/pkg/errors"

	"github.com/sourcegraph/go-lsp"
	"github.com/sourcegraph/jsonrpc2"
)

// kim: TODO: start working on find references
// kim: TODO: start working on documentation (static)
//  TODO: get aliases/anchors/merge keys working with go to definition (low priority)

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
	init     *lsp.ClientCapabilities
	isClosed bool
	mu       sync.RWMutex
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
	// case "textDocument/completion":
	//     // Request: autocomplete
	//     // https://microsoft.github.io/language-server-protocol/specifications/specification-3-14/#textDocument_completion
	//     if req.Params == nil {
	//         return nil, &jsonrpc2.Error{Code: jsonrpc2.CodeInvalidParams}
	//     }
	//     var params lsp.CompletionParams
	//     if err := json.Unmarshal(*req.Params, &params); err != nil {
	//         return nil, &jsonrpc2.Error{
	//             Message: errors.Wrap(err, "reading params").Error(),
	//             Code:    jsonrpc2.CodeInvalidParams,
	//         }
	//     }
	//
	//     return lsh.handleCompletion(ctx, conn, req, params)
	// case "textDocument/didOpen":
	//     return nil, errors.New("TODO: implement")
	// case "textDocument/didChange":
	//     return nil, errors.New("TODO: implement")
	// case "textDocument/didClose":
	//     return nil, errors.New(" TODO: implement")
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

type nodePositionFinder struct {
	posToFind    token.Position
	rootVisitor  *nodePositionVisitor
	found        ast.Node
	foundRefID   string
	foundRefKind evgReferenceKind
}

func (nf *nodePositionFinder) Visit(curr ast.Node) ast.Visitor {
	nf.rootVisitor = &nodePositionVisitor{
		finder:    nf,
		posToFind: nf.posToFind,
	}
	log.Printf("searching for position: '%s'\n", yamlPosToString(nf.posToFind))
	return nf.rootVisitor
}

type nodePositionVisitor struct {
	finder    *nodePositionFinder
	posToFind token.Position
}

var (
	// Heh, regexp pain

	// Task name
	taskPath = regexp.MustCompile(`^\$\.tasks\[\d+\]\.name$`)
	// Task selector (i.e. task, task group, or tag) under BV def
	bvTaskSelectorPath = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.tasks\[\d+\](\.name)?`)
	// Task under task group def
	tgTaskPath = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.tasks\[\d+\]$`)

	// Execution task under display task def
	execTaskPath = regexp.MustCompile(`^\$\.display_tasks\[\d+\].execution_tasks\[\d+\]$`)

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

func (nv *nodePositionVisitor) Visit(curr ast.Node) ast.Visitor {
	if curr == nil {
		// Reached a dead end.
		return nil
	}
	if nv.finder.found != nil {
		// We already located the node.
		return nil
	}

	// Could optimize by skipping over this node if it doesn't cover the
	// position to find. Can use position + value to determine its range

	// TODO: a slightly smarter way to go about this could be to parse the
	// Evergreen parser project YAML, but include each value metadata about the
	// relevant line/column.

	currNodePos := curr.GetToken().Position
	// Note: probably should deal with scalars that are map keys instead of
	// values (since references are always map values, not keys).
	_, isScalar := curr.(ast.ScalarNode)

	// Is on the same line and the character to locate is within the current
	// node's string. Furthermore, to disambiguate, we only want the scalar
	// value, not the enclosing sequence or mapping node.
	if isScalar &&
		nv.posToFind.Line == currNodePos.Line &&
		nv.posToFind.Column >= currNodePos.Column && nv.posToFind.Column <= currNodePos.Column+len(curr.String()) {

		nv.finder.found = curr
		// Use the string value instead of the literal string to avoid quotation
		// marks in refs (e.g. the YAML string "foo" should extract the string
		// value foo without quotation marks).
		nv.finder.foundRefID = curr.GetToken().Value

		// Use the YAML path (which is a string representing the path of nodes
		// down to this one) to determine the context of the current node being
		// referenced.
		// Reference: https://github.com/vmware-labs/yaml-jsonpath#syntax

		refMatches := refKindToMatchingNode(nv.posToFind)
		for refKind, getMatch := range refMatches {
			refID, _, match := getMatch(curr)
			if match {
				nv.finder.foundRefKind = refKind
				nv.finder.foundRefID = refID
				break
			}
		}

		return nil
	}

	// Give up if we've already passed the search position.
	if nv.posToFind.Line < currNodePos.Line {
		return nil
	}

	return &nodePositionVisitor{
		finder:    nv.finder,
		posToFind: nv.posToFind,
	}
}

type nodeDefFinder struct {
	refIDToFind   string
	refKindToFind evgReferenceKind
	rootVisitor   *nodeDefVisitor
	found         ast.Node
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
				// Node path is shorter, but it's a prefix.
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
		log.Println("found matching ref:", curr.Type(), curr.String(), curr.GetPath(), curr.GetToken().Position.Line, curr.GetToken().Position.Column)
		nv.finder.found = curr
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
	refKindBVMatch        = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.name`)
	refKindFunctionMatch  = regexp.MustCompile(`^\$\.functions\.[^.]+`)
	refKindTaskMatch      = regexp.MustCompile(`^\$\.tasks\[\d+\]\.name`)
	refKindTaskGroupMatch = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.name`)
	refKindTaskOrTGMatch  = regexp.MustCompile(`^\$\.((tasks\[\d+\]\.name)|(task_groups\[\d+\]\.name))`)
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
		return refKindBVMatch
	case referenceKindFunction:
		// This intentionally doesn't include the function name because the
		// function name could include special characters that mess up the
		// regexp... Sigh, functions...
		return refKindFunctionMatch
	case referenceKindTask:
		return refKindTaskMatch
	case referenceKindTaskOrTaskGroup:
		return refKindTaskOrTGMatch
	case referenceKindTaskGroup:
		return refKindTaskGroupMatch
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
	if len(parsed.Docs) == 0 {
		return nil, errors.Errorf("file had no YAML documents", filepath)
	}
	doc := parsed.Docs[0]

	// Based on the position in the text document, ascertain what the identifier
	// and kind of reference that's being looked up (e.g. task, function, etc).

	yamlPos := convertLSPPositionToYAMLPosition(params.Position)
	nf := &nodePositionFinder{
		posToFind: yamlPos,
	}
	ast.Walk(nf, doc.Body)
	if nf.found == nil {
		return nil, errors.Errorf("no matching node found at position '%s'", yamlPosToString(yamlPos))
	}
	if nf.foundRefID == "" {
		return nil, errors.Errorf("no ref ID could be extracted from node at position '%s'", yamlPosToString(yamlPos))
	}
	if nf.foundRefKind == "" {
		return nil, errors.Errorf("no matching reference kind found for node at position '%s'", yamlPosToString(yamlPos))
	}
	log.Printf("found matching positional node: '%s' with ID '%s' at position '%s' of type '%s' with path '%s'\n", nf.found.String(), nf.foundRefID, yamlPosToString(*nf.found.GetToken().Position), nf.foundRefKind, nf.found.GetPath())
	refID := nf.foundRefID
	refKind := nf.foundRefKind

	if refKind == referenceKindCommand || refKind == referenceKindDistro || refKind == referenceKindTag {
		return nil, errors.Errorf("cannot get go to definition for type '%s'", refKind)
	}

	// Look up the definition in the relevant section of the YAML.

	var defLocs []lsp.Location
	for _, doc := range parsed.Docs {
		nf := &nodeDefFinder{
			refIDToFind:   refID,
			refKindToFind: refKind,
		}
		ast.Walk(nf, doc.Body)
		if nf.found == nil {
			return nil, errors.Errorf("no matching ref for ID '%s' of type '%s'", refID, refKind)
		}
		log.Printf("found matching ref node: %s at position '%s'\n", nf.found.String(), yamlPosToString(*nf.found.GetToken().Position))

		// Assuming the reference is on one line.
		start := *nf.found.GetToken().Position
		end := *nf.found.GetToken().Position
		end.Column = end.Column + len(nf.found.String())

		defLocs = append(defLocs, lsp.Location{
			// I'm assuming it's in the same file because includes aren't
			// supported.
			URI: params.TextDocument.URI,
			Range: lsp.Range{
				Start: convertYAMLPositionToLSPPosition(start),
				End:   convertYAMLPositionToLSPPosition(end),
			},
		})
	}

	return defLocs, nil
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
	if len(parsed.Docs) == 0 {
		return nil, errors.Errorf("file had no YAML documents", filepath)
	}
	doc := parsed.Docs[0]

	// Based on the position in the text document, ascertain what the identifier
	// and kind of reference that's being looked up (e.g. task, function, etc).

	// TODO: does this even need to handle multiple docs within the same file?
	// You can currently have multiple YAML files using include, but having
	// multiple docs in the same file doesn't seem useful.
	nf := &nodePositionFinder{
		posToFind: convertLSPPositionToYAMLPosition(params.Position),
	}
	ast.Walk(nf, doc.Body)
	if nf.found == nil {
		return nil, errors.Errorf("no matching node found at position '%s'", params.Position.String())
	}
	if nf.foundRefKind == "" {
		return nil, errors.Errorf("element at position '%s' is not a valid reference", params.Position.String())
	}
	log.Printf("found matching positional node: %s at position '%s' of type %s\n", nf.found.String(), yamlPosToString(*nf.found.GetToken().Position), nf.foundRefKind)
	refID := nf.found.String()
	refKind := nf.foundRefKind

	// Find references where that identifier/kind could be used.
	log.Printf(refID, refKind)

	return []lsp.Location{}, nil
}

type nodeRefFinder struct {
	refIDToFind   string
	refKindToFind evgReferenceKind
	rootVisitor   *nodeRefVisitor
	found         []ast.Node
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
		switch nv.refKindToFind {

		}
	}

	return nv
}

// ref kind -> func that returns if node matches or not.
func refKindToMatchingNode(posToFind token.Position) map[evgReferenceKind]func(node ast.Node) (refID string, pos *token.Position, match bool) {
	return map[evgReferenceKind]func(node ast.Node) (refID string, pos *token.Position, match bool){
		referenceKindTaskOrTaskGroup: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if bvTaskSelectorPath.MatchString(path) && !strings.Contains(node.String(), ".") {
				return tkn.Value, tkn.Position, true
			}
			return "", nil, false
		},
		referenceKindTag: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()

			if tagPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
			}

			if !bvTaskSelectorPath.MatchString(path) {
				return "", nil, false
			}

			// If using tag selector syntax, determine which particular tag
			// it is within the string.
			colWithinSelector := tkn.Position.Column
			if tkn.Indicator == token.QuotedScalarIndicator {
				// Since we're parsing the string literal, skip the leading
				// quotation mark, if any.
				colWithinSelector++
			}
			for _, criterion := range strings.Split(tkn.Value, " ") {
				// Figure out from the position to find which tag is being
				// specifically requested.
				if posToFind.Column >= colWithinSelector && posToFind.Column < colWithinSelector+len(criterion) {
					// Remove tag notation and any negation.
					tag := strings.TrimPrefix(strings.TrimPrefix(criterion, "!"), ".")
					return tag, &token.Position{
						Line:   posToFind.Line,
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
				return tkn.Value, tkn.Position, true
			}
			// Since the depends on task path can omit the name, it's ambiguous
			// unless you check that it's not a BV.
			if dependsOnTaskPath.MatchString(path) && !dependsOnBVPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
			}
			return "", nil, false
		},
		referenceKindTaskGroup: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if tgPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
			}
			return "", nil, false
		},
		referenceKindBuildVariant: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if bvPath.MatchString(path) || dependsOnBVPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
			}
			return "", nil, false
		},
		referenceKindDistro: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if distroPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
			}
			return "", nil, false
		},
		referenceKindFunction: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if funcPath.MatchString(path) || funcDefPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
			}
			return "", nil, false
		},
		referenceKindCommand: func(node ast.Node) (string, *token.Position, bool) {
			path := node.GetPath()
			tkn := node.GetToken()
			if cmdPath.MatchString(path) {
				return tkn.Value, tkn.Position, true
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

func (lsh *LanguageServerHandler) handleCompletion(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request, params lsp.CompletionParams) (*lsp.CompletionList, error) {
	// filepath, err := uriToFilepath(params.TextDocument.URI)
	// if err != nil {
	//     return nil, errors.Wrapf(err, "getting filepath from URI '%s'", params.TextDocument.URI)
	// }
	//
	// parsed, err := parser.ParseFile(filepath, 0)
	// if err != nil {
	//     return nil, errors.Wrapf(err, "parsing YAML file '%s'", filepath)
	// }

	// Based on the position in the text document, ascertain what set of names
	// could be filled in (e.g. statically-known key names, valid values
	// including references).

	// for _, doc := range parsed.Docs {
	//     nf := nodeFinder{pos: params.Position}
	//     ast.Walk(nf, doc.Body)
	//     if nf.found == nil {
	//         return nil, errors.Errorf("no matching node found at position '%s'", params.Position.String())
	//     }
	// }

	return nil, errors.New("TODO: implement")
}

func yamlPosToString(pos token.Position) string {
	return fmt.Sprintf("%d:%d", pos.Line, pos.Column)
}

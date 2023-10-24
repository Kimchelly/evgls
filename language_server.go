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

/*
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
		// defer lsh.mu.Unlock()
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
		// https://microsoft.github.io/language-server-protocol/specifications/specification-3-14/#textDocument_definition
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
	//     return lsh.handleTextDocumentCompletion(ctx, conn, req, params)
	// case "textDocument/didOpen":
	//     return nil, errors.New("kim: TODO: implement")
	// case "textDocument/didChange":
	//     return nil, errors.New("kim: TODO: implement")
	// case "textDocument/didClose":
	//     return nil, errors.New("kim: TODO: implement")
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

	// Note that basically all other references (e.g. BV names, task selectors
	// that select by tags) are ambiguous (so they can't go to a particular
	// definition) and/or not used. That kind of thing could be supported by
	// textDocument/references though.
)

type nodePositionFinder struct {
	posToFind    token.Position
	rootVisitor  *nodePositionVisitor
	found        ast.Node
	foundRefKind evgReferenceKind
}

func (nf *nodePositionFinder) Visit(curr ast.Node) ast.Visitor {
	nf.rootVisitor = &nodePositionVisitor{
		finder:    nf,
		posToFind: nf.posToFind,
	}
	log.Printf("searching for position: (%d, %d)\n", nf.posToFind.Line, nf.posToFind.Column)
	return nf.rootVisitor
}

type nodePositionVisitor struct {
	finder    *nodePositionFinder
	posToFind token.Position
	// parents   []ast.Node
}

var (
	bvTaskPath = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.tasks\[\d+\](\.name)?`)
	tgTaskPath = regexp.MustCompile(`^\$\.task_groups\[\d+\]\.tasks\[\d+\]$`)

	execTaskPath = regexp.MustCompile(`^\$\.display_tasks\[\d+\].execution_tasks\[\d+\]$`)

	// Heh, regexp pain

	// Dep name under task def, BV def, or BVTU def
	dependsOnTaskPath = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks\[\d+\]))\.depends_on\[\d+\](\.name)?`)

	// Dep variant under task def, BV def, or BVTU def
	dependsOnVariantPath = regexp.MustCompile(`^\$\.((tasks\[\d+\])|(buildvariants\[\d+\])|(buildvariants\[\d+\]\.tasks\[\d+\]))\.depends_on\[\d+\]\.variant$`)

	// Func ref under pre, post, task, or task group
	funcPath = regexp.MustCompile(`^\$\.((pre\[\d+\])|(post\[\d+\])|(tasks\[\d+\]\.commands\[\d+\]))\.func$`)
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

	// kim: NOTE: a slightly smarter way to go about this could be to parse the
	// Evergreen parser project YAML, but with each value would be the starting
	// line/column.

	currNodePos := curr.GetToken().Position
	// Note: probably should deal with scalars that are map keys instead of
	// values (since references are always map values, not keys).
	_, isScalar := curr.(ast.ScalarNode)
	// log.Printf("checking node: %s\n", curr.String())

	// Is on the same line and the character to locate is within the current
	// node's string. Furthermore, to disambiguate, we only want the scalar
	// value, not the enclosing sequence or mapping node.
	if isScalar &&
		nv.posToFind.Line == currNodePos.Line &&
		nv.posToFind.Column >= currNodePos.Column && nv.posToFind.Column <= currNodePos.Column+len(curr.String()) {

		log.Println("found matching positional node:", curr.Type(), curr.String(), curr.GetPath(), curr.GetToken().Position.Line, curr.GetToken().Position.Column)
		nv.finder.found = curr

		// For definition lookups, need to look for:
		// * tasks (under BV and task group)
		// * depends_on (under BV, task, and BVTU)
		//     * name (i.e. task)
		//     * variant
		// * execution_tasks (under display_tasks)
		// Any other lookup is invalid.

		/*
			buildvariants -> one build variant -> tasks -> one task selector
			task_groups -> one task group -> tasks -> one task selector

			tasks -> one task -> depends_on -> one dependency name
			buildvariants -> one build variant -> depends_on -> one dependency
			name
			buildvariants -> one build variant -> tasks -> one task selector ->
			depends_on -> one dependency name

			display_tasks -> execution_tasks -> one execution task
		*/

		// Use the YAML path (which is a string representing the path of nodes
		// down to this one) to determine the context of the current thing being
		// referenced.
		// Reference: https://github.com/vmware-labs/yaml-jsonpath#syntax

		path := curr.GetPath()

		if bvTaskPath.MatchString(path) {
			nv.finder.foundRefKind = referenceKindTaskOrTaskGroup
		} else if tgTaskPath.MatchString(path) {
			nv.finder.foundRefKind = referenceKindTask
		} else if execTaskPath.MatchString(path) {
			// I'm actually not sure if execution tasks under display task
			// definitions can refer to task groups, but I'm gonna pretend it
			// doesn't for my own sanity.
			nv.finder.foundRefKind = referenceKindTask
		} else if dependsOnVariantPath.MatchString(path) {
			nv.finder.foundRefKind = referenceKindBuildVariant
		} else if dependsOnTaskPath.MatchString(path) {
			// The order of checks for variant/task deps is important because
			// deps can be specified as either just task name or by explicit
			// task name + BV.
			nv.finder.foundRefKind = referenceKindTask
		} else if funcPath.MatchString(path) {
			nv.finder.foundRefKind = referenceKindFunction
		} else {
			// Not a recognized reference.
		}

		return nil
	}

	// Give up if we've already passed the search position.
	if nv.posToFind.Line < currNodePos.Line {
		return nil
	}

	// parentsWithCurr := make([]ast.Node, 0, len(nv.parents)+1)
	// copy(parentsWithCurr, nv.parents)
	// parentsWithCurr = append(parentsWithCurr, curr)
	return &nodePositionVisitor{
		finder:    nv.finder,
		posToFind: nv.posToFind,
		// parents:   parentsWithCurr,
	}
}

type nodeRefFinder struct {
	refIDToFind   string
	refKindToFind evgReferenceKind
	rootVisitor   *nodeRefVisitor
	found         ast.Node
}

func (nf *nodeRefFinder) Visit(curr ast.Node) ast.Visitor {
	nf.rootVisitor = &nodeRefVisitor{
		finder:        nf,
		refIDToFind:   nf.refIDToFind,
		refKindToFind: nf.refKindToFind,
	}
	log.Printf("searching for ref: %s %s\n", nf.refKindToFind, nf.refIDToFind)
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
	if nv.finder.found != nil {
		// We already located the node.
		return nil
	}

	path := curr.GetPath()
	log.Printf("checking node path for matching ref: %s\n", path)
	pathRegexp := refKindToPath(nv.refKindToFind)
	if pathRegexp == nil {
		log.Printf("cannot convert ref kind '%s' to path regexp\n", nv.refKindToFind)
		return nil
	}
	if pathRegexp.MatchString(path) && nv.refIDToFind == curr.String() {
		log.Println("found matching ref:", curr.Type(), curr.String(), curr.GetPath(), curr.GetToken().Position.Line, curr.GetToken().Position.Column)
		nv.finder.found = curr
		return nil
	}

	return &nodeRefVisitor{
		finder:        nv.finder,
		refIDToFind:   nv.refIDToFind,
		refKindToFind: nv.refKindToFind,
	}
}

var (
	refKindBVMatch       = regexp.MustCompile(`^\$\.buildvariants\[\d+\]\.name$`)
	refKindFunctionMatch = regexp.MustCompile(`^\$\.functions\[\d+\]\.name$`)
	refKindTaskMatch     = regexp.MustCompile(`^\$\.tasks\[\d+\]\.name$`)
	refKindTaskOrTGMatch = regexp.MustCompile(`^\$\.((tasks\[\d+\]\.name)|(task_groups\[\d+\]\.name))$`)
)

// refKindToPrefixPath returns the YAML path prefix for a particular reference
// kind.
// TODO: This doesn't work if there are aliases/anchors, but whatever, this is
// bad code anyways. One potential implementation of go to definition could be
// to jump to the line where the definition dereferences the alias. Then would
// need special separate handling for jumping to an alias/anchor definition if
// the user needs to see the anchor.
func refKindToPath(kind evgReferenceKind) *regexp.Regexp {
	switch kind {
	case referenceKindBuildVariant:
		return refKindBVMatch
	case referenceKindFunction:
		return refKindFunctionMatch
	case referenceKindTask:
		return refKindTaskMatch
	case referenceKindTaskOrTaskGroup:
		return refKindTaskOrTGMatch
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

	// Based on the position in the text document, ascertain what the name and
	// kind of reference that's being looked up (e.g. task, function, etc).

	var refID string
	var refKind evgReferenceKind
	// TODO: does this even need to handle multiple docs within the same file?
	// You can currently have multiple YAML files using include, but having
	// multiple docs in the same file doesn't seem useful.
	for _, doc := range parsed.Docs {
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
		log.Printf("found matching positional node: %s at position (%d, %d) of type %s\n", nf.found.String(), nf.found.GetToken().Position.Line, nf.found.GetToken().Position.Column, nf.foundRefKind)
		refID = nf.found.String()
		refKind = nf.foundRefKind
	}

	// Look up the definition in the relevant section of the YAML.
	var defLocs []lsp.Location
	for _, doc := range parsed.Docs {
		nf := &nodeRefFinder{
			refIDToFind:   refID,
			refKindToFind: refKind,
		}
		ast.Walk(nf, doc.Body)
		if nf.found == nil {
			return nil, errors.Errorf("no matching ref for ID '%s' of type '%s'", refID, refKind)
		}
		log.Printf("found matching ref node: %s at position (%d, %d)\n", nf.found.String(), nf.found.GetToken().Position.Line, nf.found.GetToken().Position.Column)

		// Assuming the reference is on one line.
		start := *nf.found.GetToken().Position
		end := *nf.found.GetToken().Position
		end.Column = end.Column + len(nf.found.String())

		defLocs = append(defLocs, lsp.Location{
			// Assuming here it's in the same file.
			URI: params.TextDocument.URI,
			Range: lsp.Range{
				Start: convertYAMLPositionToLSPPosition(start),
				End:   convertYAMLPositionToLSPPosition(end),
			},
		})
	}

	return defLocs, nil
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

func (lsh *LanguageServerHandler) handleTextDocumentCompletion(ctx context.Context, conn *jsonrpc2.Conn, req *jsonrpc2.Request, params lsp.CompletionParams) (*lsp.CompletionList, error) {
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

	return nil, errors.New("kim: TODO: implement")
}

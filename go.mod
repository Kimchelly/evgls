module evgls

go 1.20

require (
	// kim: NOTE: I'm intentionally not using gopkg.in/yaml.v3 since it doesn't provide direct access to
	// lexer/parser/AST in its interface.
	github.com/goccy/go-yaml v1.11.2
	github.com/pkg/errors v0.9.1
	github.com/sourcegraph/go-lsp v0.0.0-20200429204803-219e11d77f5d
	github.com/sourcegraph/jsonrpc2 v0.2.0
)

require github.com/santhosh-tekuri/jsonschema v1.2.4

require (
	github.com/fatih/color v1.10.0 // indirect
	github.com/mattn/go-colorable v0.1.8 // indirect
	github.com/mattn/go-isatty v0.0.12 // indirect
	golang.org/x/sys v0.6.0 // indirect
	golang.org/x/xerrors v0.0.0-20200804184101-5ec99f83aff1 // indirect
)

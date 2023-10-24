package main

import (
	"context"
	"evgls"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"os"

	"github.com/pkg/errors"
	"github.com/sourcegraph/jsonrpc2"
)

type cmdParams struct {
	printVersion *bool
	logFile      *string
	addr         *string
}

func main() {
	params := cmdParams{
		printVersion: flag.Bool("version", false, "print language server version"),
		logFile:      flag.String("logfile", "", "log output file"),
		addr:         flag.String("addr", "localhost:11223", "address to run language server on"),
	}
	flag.Parse()

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	if err := run(ctx, params); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(ctx context.Context, params cmdParams) error {
	if *params.printVersion {
		fmt.Println("no version")
		return nil
	}

	var logger io.Writer
	if params.logFile != nil && *params.logFile != "" {
		logFile, err := os.Create(*params.logFile)
		if err != nil {
			return errors.Wrap(err, "creating log file")
		}
		defer logFile.Close()
		logger = io.MultiWriter(os.Stderr, logFile)
	} else {
		logger = os.Stderr
	}
	log.SetOutput(logger)

	if params.addr == nil || *params.addr == "" {
		return errors.New("server address must be set")
	}
	listener, err := net.Listen("tcp", *params.addr)
	if err != nil {
		return errors.Wrapf(err, "listening on address '%s'", *params.addr)
	}
	defer listener.Close()

	log.Printf("listening at address %s\n", *params.addr)

	connectionCount := 0
	for {
		conn, err := listener.Accept()
		if err != nil {
			log.Println(errors.Wrap(err, "accepting incoming connection"))
			continue
		}

		connectionCount++
		thisConnectionCount := connectionCount
		log.Printf("received incoming connection #%d\n", thisConnectionCount)

		ls := evgls.NewHandler()
		jsonrpcConn := jsonrpc2.NewConn(ctx, jsonrpc2.NewBufferedStream(conn, jsonrpc2.VSCodeObjectCodec{}), ls)
		go func() {
			<-jsonrpcConn.DisconnectNotify()
			if err != nil {
				log.Println(err)
			}
			log.Printf("connection #%d closed\n", thisConnectionCount)
		}()
	}

	// if err := startLanguageServer(ctx, ls); err != nil {
	//     return errors.Wrap(err, "starting language server")
	// }
}

// func startLanguageServer(ctx context.Context, ls evgls.LanguageServer) (addr string, closeSrv func() error, error) {
//     addr := "127.0.0.1:0"
//     l, err := net.Listen("tcp", addr)
//     if err != nil {
//         return "", nil, err
//     }
//
//     go func() {
//         if err := serve(ctx, l, ls.Handler); err != nil {
//         }
//     }()
//
//     return l.Addr().String(), l.Close, nil
// }

func serve(ctx context.Context, listener net.Listener, handler jsonrpc2.Handler) error {
	for {
		conn, err := listener.Accept()
		if err != nil {
			return err
		}
		jsonrpc2.NewConn(ctx, jsonrpc2.NewBufferedStream(conn, jsonrpc2.VSCodeObjectCodec{}), handler)
	}
}

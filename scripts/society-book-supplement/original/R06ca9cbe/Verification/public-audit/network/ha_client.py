"""Pass-through routing to a pinned physical candidate; original client verifies TLS and receipts."""
import selectors
import socket
import socketserver
import threading

from client import exchange as original_exchange


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        try:
            with socket.create_connection(self.server.target, timeout=3) as remote:
                self.request.settimeout(30); remote.settimeout(30)
                with selectors.DefaultSelector() as selector:
                    selector.register(self.request, selectors.EVENT_READ, remote)
                    selector.register(remote, selectors.EVENT_READ, self.request)
                    while True:
                        ready = selector.select(30)
                        if not ready:return
                        for key, _ in ready:
                            data = key.fileobj.recv(65536)
                            if not data:return
                            key.data.sendall(data)
        except (OSError, EOFError):
            return


class Relay(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


def exchange(profile, source, host, port, query, *, lookup=None):
    with Relay(('127.0.0.1', 0), Handler) as relay:
        relay.target = (host, port)
        worker = threading.Thread(target=relay.serve_forever, kwargs={'poll_interval': .1}, daemon=True)
        worker.start()
        try:
            return original_exchange(profile, relay.server_address[1], source, query,
                                     lookup=lookup, expected_stream='recovery')
        finally:
            relay.shutdown(); worker.join(timeout=5)

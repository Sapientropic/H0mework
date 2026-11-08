"""Capture slow original-source exchanges without truncating them at 30 seconds."""
import base64
import gzip
import socket
import socketserver
import threading
import time
from crypto import canonical


class Tap:
    def __init__(self, port, path, timeout=120):
        owner=self;self.lock=threading.Lock();self.index=0;self.output=gzip.open(path,'xt')

        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                with owner.lock:
                    number=owner.index;owner.index+=1
                upstream=socket.create_connection(('127.0.0.1',port),timeout=timeout)
                def relay(source,destination,direction):
                    try:
                        while data:=source.recv(65536):
                            with owner.lock:
                                owner.output.write(canonical({'connection':number,'direction':direction,'phase':'received',
                                    'at_ns':time.monotonic_ns(),'bytes':base64.b64encode(data).decode()}).decode()+'\n');owner.output.flush()
                            destination.sendall(data)
                            with owner.lock:
                                owner.output.write(canonical({'connection':number,'direction':direction,'phase':'forwarded',
                                    'at_ns':time.monotonic_ns(),'length':len(data)}).decode()+'\n');owner.output.flush()
                    except (OSError,EOFError):
                        with owner.lock:
                            owner.output.write(canonical({'connection':number,'direction':direction,'phase':'interrupted',
                                'at_ns':time.monotonic_ns()}).decode()+'\n');owner.output.flush()
                    finally:
                        with owner.lock:
                            owner.output.write(canonical({'connection':number,'direction':direction,'phase':'eof',
                                'at_ns':time.monotonic_ns()}).decode()+'\n');owner.output.flush()
                        try:destination.shutdown(socket.SHUT_WR)
                        except OSError:pass
                worker=threading.Thread(target=relay,args=(upstream,self.request,'server'),daemon=True)
                worker.start();relay(self.request,upstream,'client');worker.join(timeout+5);upstream.close()

        class Server(socketserver.ThreadingTCPServer):
            allow_reuse_address=True
            daemon_threads=False
        self.server=Server(('127.0.0.1',0),Handler);self.port=self.server.server_address[1]
        self.thread=threading.Thread(target=self.server.serve_forever,kwargs={'poll_interval':.05},daemon=True)
        self.thread.start()

    def close(self):
        self.server.shutdown();self.server.server_close();self.thread.join();self.output.close()

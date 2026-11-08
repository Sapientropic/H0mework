"""Anchor-issued one-use RPC freshness, independent of client wall-clock offset."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import secrets
import signal
import socketserver
import time

import anchor
from crypto import connect,digest,peer,receive,send,sign,tls_context,verify
from quorum import Client as OriginalQuorumClient


class Client(anchor.Client):
    def call(self, operation, **values):
        endpoint=self.endpoint
        with connect(self.profile,endpoint['port'],host=endpoint['host'],hostname=endpoint['hostname']) as connection:
            uri,fingerprint,key=peer(connection)
            if uri!='urn:public-audit:anchor' or fingerprint!=endpoint['identity']['fingerprint'] or key.public_bytes_raw().hex()!=endpoint['identity']['app']:
                raise ValueError('ANCHOR_IDENTITY')
            challenge=receive(connection)
            body=verify(key,'anchor-challenge',challenge)
            if set(body)!={'nonce','valid_for','cluster'} or body['valid_for']!=30 or body['cluster']!=endpoint.get('cluster'):
                raise ValueError('ANCHOR_CHALLENGE_SCOPE')
            request_body=dict(op=operation,source=self.config['source'],stream=self.config['stream'],
                              nonce=secrets.token_hex(32),challenge=digest(challenge),**values)
            request=sign(self.key,'anchor-request',request_body)
            send(connection,request)
            result=verify(key,'anchor-response',receive(connection))
            if result['request']!=digest(request) or result['nonce']!=request_body['nonce']:
                raise ValueError('ANCHOR_FRESHNESS')
            if 'error' in result:raise ValueError(result['error'])
            return result['result']


class QuorumClient(OriginalQuorumClient):
    def __init__(self,config):
        super().__init__(config)
        self.nodes={name:Client({**config,'anchor':{**entry,'identity':self.trust['members'][name],'cluster':self.cluster}})
                    for name,entry in config['anchors']['endpoints'].items()}


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        journal=self.server.journal
        request=None
        try:
            uri,fingerprint,key=peer(self.request)
            writer=journal.config['transport_writer']
            if uri!='urn:public-audit:server' or fingerprint!=writer['fingerprint'] or key.public_bytes_raw().hex()!=writer['app']:
                raise ValueError('ANCHOR_WRITER')
            challenge=sign(journal.key,'anchor-challenge',dict(nonce=secrets.token_hex(32),valid_for=30,cluster=journal.config.get('cluster')))
            deadline=time.monotonic()+30
            send(self.request,challenge)
            request=receive(self.request)
            body=verify(key,'anchor-request',request)
            if body.get('challenge')!=digest(challenge):raise ValueError('ANCHOR_CHALLENGE_BINDING')
            if time.monotonic()>deadline:raise ValueError('ANCHOR_CHALLENGE_EXPIRED')
            if hasattr(journal,'execute_request'):
                result=journal.execute_request(body)
            else:
                with journal.lock:result=journal.execute(body)
            response={'result':result}
        except Exception as error:
            response={'error':str(error) if isinstance(error,(ValueError,KeyError)) else type(error).__name__}
        if request is not None:
            response.update(request=digest(request),nonce=request.get('body',{}).get('nonce'))
            send(self.request,sign(journal.key,'anchor-response',response))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('config',type=Path)
    parser.add_argument('--initialize',action='store_true')
    args=parser.parse_args()
    config=json.loads(args.config.read_text())
    signal.signal(signal.SIGTERM,lambda *_:(_ for _ in ()).throw(SystemExit(0)))
    journal=anchor.Journal(config,args.initialize)
    try:
        with anchor.Server((config.get('bind','127.0.0.1'),config.get('port',0)),Handler) as server:
            server.journal=journal
            server.context=tls_context(Path(config['pki'])/'anchor',server=True)
            print(json.dumps({'port':server.server_address[1],'role':'anchor-issued-challenge'}),flush=True)
            server.serve_forever(poll_interval=.1)
    finally:journal.db.close()


if __name__=='__main__':main()

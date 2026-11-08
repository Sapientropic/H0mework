"""Durable observations of an application attempt, separate from the service ledger."""
from __future__ import annotations
import fcntl
import json
import os
from pathlib import Path
import secrets
import threading
import time
from crypto import canonical, digest, sign, verify

KIND='application-receipt/v1'
ZERO='0'*64


class Journal:
    def __init__(self,path,key,source,stream,side):
        if side not in ('client','server'):raise ValueError('APPLICATION_SIDE')
        self.path=Path(path);self.path.parent.mkdir(parents=True,exist_ok=True)
        self.key=key;self.source=source;self.stream=stream;self.side=side;self.lock=threading.Lock()

    def append(self,attempt,stage,data):
        with self.lock,self.path.open('a+b') as file:
            fcntl.flock(file,fcntl.LOCK_EX);file.seek(0,os.SEEK_END);size=file.tell()
            previous=ZERO;index=0
            if size:
                width=min(size,65536)
                while True:
                    file.seek(size-width);raw=file.read(width)
                    if not raw.endswith(b'\n'):raise ValueError('APPLICATION_TORN_TAIL')
                    if width==size or b'\n' in raw[:-1]:break
                    width=min(size,width*2)
                last=json.loads(raw.splitlines()[-1]);body=verify(self.key.public_key(),KIND,last)
                if (body['source'],body['stream'],body['side'])!=(self.source,self.stream,self.side):raise ValueError('APPLICATION_CURSOR')
                previous=digest(last);index=body['index']+1
            value=sign(self.key,KIND,dict(index=index,previous=previous,source=self.source,
                stream=self.stream,side=self.side,attempt=attempt,stage=stage,at_ns=time.monotonic_ns(),data=data))
            file.write(canonical(value)+b'\n');file.flush();os.fsync(file.fileno())
            return value

    def start(self,data):
        attempt=secrets.token_hex(16);self.append(attempt,'opened',data);return Attempt(self,attempt)


class Attempt:
    def __init__(self,journal,identity):self.journal=journal;self.identity=identity;self.closed=False
    def add(self,stage,data):
        if self.closed:raise ValueError('APPLICATION_ALREADY_CLOSED')
        result=self.journal.append(self.identity,stage,data)
        if stage=='closed':self.closed=True
        return result
    def close(self,error=None):
        if not self.closed:self.add('closed',dict(error=error))

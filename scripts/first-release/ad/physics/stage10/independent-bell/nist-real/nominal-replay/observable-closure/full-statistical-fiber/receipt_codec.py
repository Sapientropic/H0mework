"""Lossless typed JSON storage for large exact-rational proof receipts."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import lzma
from pathlib import Path
import re
import struct

MAGIC = b"P23-FIBER-JSON-1\n"
FACTORS = {(2**a)*(5**b): (a, b) for a in range(100) for b in range(70)}
CANONICAL = re.compile(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")


def uint(n):
    if n < 0: raise ValueError("negative_length")
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128); n >>= 7
    out.append(n)
    return bytes(out)


def bigint(n):
    raw = abs(n).to_bytes(max(1, (abs(n).bit_length() + 7)//8), "big")
    return bytes([n < 0]) + uint(len(raw)) + raw


def encode(value):
    if value is None: return b"n"
    if value is False: return b"f"
    if value is True: return b"t"
    if isinstance(value, int): return b"i" + bigint(value)
    if isinstance(value, float): return b"d" + struct.pack(">d", value)
    if isinstance(value, str):
        if CANONICAL.fullmatch(value):
            parts = value.split("/")
            numerator = int(parts[0])
            if len(parts) == 1 and str(numerator) == value:
                return b"z" + bigint(numerator)
            if len(parts) == 2:
                denominator = int(parts[1])
                pair = FACTORS.get(denominator)
                return (b"q" + bigint(numerator) + uint(pair[0]) + uint(pair[1]) if pair is not None
                        else b"r" + bigint(numerator) + bigint(denominator))
        raw = value.encode()
        return b"s" + uint(len(raw)) + raw
    if isinstance(value, list):
        return b"a" + uint(len(value)) + b"".join(encode(x) for x in value)
    if isinstance(value, dict):
        return b"o" + uint(len(value)) + b"".join(encode(k) + encode(v) for k,v in value.items())
    raise ValueError("unsupported_JSON_type")


class Reader:
    def __init__(self, raw):
        self.raw, self.offset = raw, 0

    def take(self, n):
        if n < 0 or self.offset+n > len(self.raw): raise ValueError("truncated_receipt")
        v=self.raw[self.offset:self.offset+n]; self.offset+=n
        return v

    def uint(self):
        result, shift = 0, 0
        while True:
            b = self.take(1)[0]
            result |= (b & 127) << shift
            if b < 128: return result
            shift += 7
            if shift > 64: raise ValueError("receipt_length_overflow")

    def big(self):
        sign=self.take(1)[0]
        if sign not in (0,1): raise ValueError("invalid_integer_sign")
        n=self.uint()
        if n>8192: raise ValueError("receipt_integer_too_large")
        value=int.from_bytes(self.take(n),"big")
        return -value if sign else value

    def read(self, depth=0):
        if depth>64: raise ValueError("receipt_depth_limit")
        kind=self.take(1)
        if kind==b"n":return None
        if kind==b"f":return False
        if kind==b"t":return True
        if kind==b"i":return self.big()
        if kind==b"d":return struct.unpack(">d",self.take(8))[0]
        if kind==b"z":return str(self.big())
        if kind==b"q":
            numerator=self.big(); a,b=self.uint(),self.uint()
            if a>10000 or b>10000:raise ValueError("denominator_exponent_limit")
            return str(numerator)+"/"+str(2**a*5**b)
        if kind==b"r":return str(self.big())+"/"+str(self.big())
        if kind==b"s":return self.take(self.uint()).decode()
        if kind in (b"a",b"o"):
            n=self.uint()
            if n>10000000:raise ValueError("receipt_container_limit")
            if kind==b"a":return [self.read(depth+1) for _ in range(n)]
            result={}
            for _ in range(n):
                key=self.read(depth+1)
                if not isinstance(key,str) or key in result:raise ValueError("invalid_JSON_key")
                result[key]=self.read(depth+1)
            return result
        raise ValueError("unknown_receipt_token")


def canonical_bytes(value):
    return (json.dumps(value,sort_keys=True,separators=(",",":"),allow_nan=False)+"\n").encode()


def compress(raw):
    value=json.loads(raw)
    if canonical_bytes(value)!=raw:raise ValueError("noncanonical_source_JSON")
    return lzma.compress(MAGIC+encode(value),format=lzma.FORMAT_XZ,preset=6)


def decompress(raw):
    unpacked=lzma.decompress(raw,format=lzma.FORMAT_XZ,memlimit=512*1024*1024)
    if not unpacked.startswith(MAGIC):raise ValueError("unknown_receipt_codec")
    r=Reader(unpacked[len(MAGIC):])
    value=r.read()
    if r.offset!=len(r.raw):raise ValueError("trailing_receipt_data")
    return canonical_bytes(value)


def load(path):
    path=Path(path)
    data=path.read_bytes()
    return json.loads(decompress(data) if path.suffix==".xz" else gzip.decompress(data))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input",type=Path)
    parser.add_argument("output",type=Path)
    args=parser.parse_args()
    if args.output.exists():raise ValueError("protected_existing_receipt_storage")
    raw=gzip.decompress(args.input.read_bytes())
    stored=compress(raw)
    if decompress(stored)!=raw:raise ValueError("receipt_roundtrip_changed")
    args.output.write_bytes(stored)
    meta={"schema":"p23-typed-rational-JSON-storage/v1","codec":"receipt_codec.py",
          "codec_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          "logical_sha256":hashlib.sha256(raw).hexdigest(),"stored_sha256":hashlib.sha256(stored).hexdigest(),
          "original_gzip_sha256":hashlib.sha256(args.input.read_bytes()).hexdigest(),
          "logical_bytes":len(raw),"stored_bytes":len(stored),"original_JSON_bytes_preserved":True}
    args.output.with_name(args.output.name+".json").write_text(json.dumps(meta,indent=2)+"\n")
    print(json.dumps(meta),flush=True)


if __name__=="__main__":main()

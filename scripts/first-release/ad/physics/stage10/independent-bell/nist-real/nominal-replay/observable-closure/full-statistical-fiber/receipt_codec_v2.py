"""Layout-preserving extension of the frozen exact-rational receipt codec."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import lzma
from pathlib import Path

import receipt_codec as base

MAGIC=b"P23-FIBER-JSON-2\n"


def layout_bytes(value, pretty):
    return ((json.dumps(value,sort_keys=True,indent=2,allow_nan=False) if pretty else
             json.dumps(value,sort_keys=True,separators=(",",":"),allow_nan=False))+"\n").encode()


def compress(raw):
    value=json.loads(raw)
    if layout_bytes(value,False)==raw:pretty=False
    elif layout_bytes(value,True)==raw:pretty=True
    else:raise ValueError("unsupported_original_JSON_layout")
    return lzma.compress(MAGIC+bytes([pretty])+base.encode(value),format=lzma.FORMAT_XZ,preset=6)


def decompress(raw):
    unpacked=lzma.decompress(raw,format=lzma.FORMAT_XZ,memlimit=512*1024*1024)
    if unpacked.startswith(base.MAGIC):return base.decompress(raw)
    if not unpacked.startswith(MAGIC):raise ValueError("unknown_receipt_codec")
    offset=len(MAGIC)
    pretty=unpacked[offset]
    if pretty not in (0,1):raise ValueError("invalid_JSON_layout")
    reader=base.Reader(unpacked[offset+1:])
    value=reader.read()
    if reader.offset!=len(reader.raw):raise ValueError("trailing_receipt_data")
    return layout_bytes(value,pretty)


def load(path):
    path=Path(path);raw=path.read_bytes()
    return json.loads(decompress(raw) if path.suffix==".xz" else gzip.decompress(raw))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input",type=Path);parser.add_argument("output",type=Path)
    args=parser.parse_args()
    if args.output.exists():raise ValueError("protected_existing_receipt_storage")
    raw=gzip.decompress(args.input.read_bytes())
    stored=compress(raw)
    if decompress(stored)!=raw:raise ValueError("receipt_roundtrip_changed")
    args.output.write_bytes(stored)
    meta={"schema":"p23-typed-rational-JSON-storage/v2","codec":"receipt_codec_v2.py",
          "codec_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          "base_codec_sha256":hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
          "logical_sha256":hashlib.sha256(raw).hexdigest(),"stored_sha256":hashlib.sha256(stored).hexdigest(),
          "original_gzip_sha256":hashlib.sha256(args.input.read_bytes()).hexdigest(),
          "logical_bytes":len(raw),"stored_bytes":len(stored),"original_JSON_bytes_preserved":True}
    args.output.with_name(args.output.name+".json").write_text(json.dumps(meta,indent=2)+"\n")
    print(json.dumps(meta),flush=True)


if __name__=="__main__":main()

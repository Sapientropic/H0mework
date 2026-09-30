#!/usr/bin/env python3
"""Replay the frozen matrix producer, redirecting their sole receipt write into this audit."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent


def main():
    results=[]
    for module_name,source_name,receipt_name in [('prepared_loops_replay','compute.py','receipt.json')]:
        path=HERE.parent/source_name
        spec=importlib.util.spec_from_file_location(module_name,path)
        module=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        original=Path.write_text
        expected=(HERE.parent/receipt_name).resolve()
        redirected=HERE/('replay-'+receipt_name)
        def write(file,data,*args,**kwargs):
            assert file.resolve()==expected, f'unexpected producer write: {file}'
            return original(redirected,data,*args,**kwargs)
        Path.write_text=write
        try:
            module.main()
        finally:
            Path.write_text=original
        current=json.loads(redirected.read_text())
        frozen=json.loads(expected.read_text())
        for key in ['elapsed_seconds','seconds']:
            current.pop(key,None)
            frozen.pop(key,None)
        assert current==frozen
        results.append({'program':source_name,'all_data_equal_except_elapsed_seconds':True,
            'frozen_source_unchanged':True,'receipt_write_redirected':str(redirected.name)})
    (HERE/'replay-summary.json').write_text(json.dumps({'status':'PASS','checks':results},indent=2)+'\n')


if __name__=='__main__':main()

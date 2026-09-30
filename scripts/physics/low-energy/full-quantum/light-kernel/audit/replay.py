#!/usr/bin/env python3
"""Replay frozen scripts, including top-level producers, with every write confined to this audit."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
OUTPUTS={'compute.py':'receipt.json','propagation.py':'propagation-receipt.json','direct.py':'direct-receipt.json','modes.py':'modes-receipt.json','coefficients.py':'coefficient-receipt.json'}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--program',action='append',required=True,choices=OUTPUTS)
    args=parser.parse_args();results=[]
    for index,filename in enumerate(args.program):
        path=HERE.parent/filename;receipt=OUTPUTS[filename]
        expected=(HERE.parent/receipt).resolve();redirected=HERE/('replay-'+receipt)
        original=Path.write_text
        def write(file,data,*args,**kwargs):
            assert file.resolve()==expected, f'unexpected producer write: {file}'
            return original(redirected,data,*args,**kwargs)
        started=time.monotonic();Path.write_text=write
        try:
            spec=importlib.util.spec_from_file_location('boson_audit_'+path.stem,path)
            module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
            if hasattr(module,'main'):module.main()
        finally:Path.write_text=original
        current=json.loads(redirected.read_text());frozen=json.loads(expected.read_text())
        for key in ['elapsed_seconds','seconds']:current.pop(key,None);frozen.pop(key,None)
        assert current==frozen,filename
        result={'program':filename,'all_data_equal_except_elapsed_seconds':True,'frozen_source_unchanged':True,
            'receipt_write_redirected':redirected.name,'seconds':round(time.monotonic()-started,3)}
        results.append(result);print(json.dumps(result),flush=True)
        (HERE/('replay-'+Path(args.program[0]).stem+'-summary.json')).write_text(json.dumps({'status':'PASS','checks':results},indent=2)+'\n')


if __name__=='__main__':main()

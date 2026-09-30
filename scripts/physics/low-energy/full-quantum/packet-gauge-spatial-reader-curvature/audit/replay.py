#!/usr/bin/env python3
"""Replay frozen source bounds and shape consumers in an owned directory."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
CANDIDATE=HERE.parent
ROOT=CANDIDATE.parents[4]


def clean(data):
    if isinstance(data,dict):return {k:clean(v) for k,v in data.items() if k not in ['elapsed_seconds','input_sha256']}
    if isinstance(data,list):return list(map(clean,data))
    return data


def main():
    manifest=json.loads((CANDIDATE/'construction.json').read_text())
    for group,base in [('candidate_sha256',CANDIDATE),('source_inputs',ROOT),('source_sha256',ROOT)]:
        for name,expected in manifest[group].items():
            assert hashlib.sha256((base/name).read_bytes()).hexdigest()==expected,name
    output=HERE/'replay';output.mkdir(exist_ok=True)
    checks=[]
    for name in ['bounds','shape']:
        spec=importlib.util.spec_from_file_location('frozen_'+name,CANDIDATE/(name+'.py'))
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        module.HERE=output;module.main()
        result=json.loads((output/(name+'.json')).read_text())
        expected=json.loads((CANDIDATE/(name+'.json')).read_text())
        assert clean(result)==clean(expected),name
        checks.append({'stage':name,'exit_code':0,'seconds':result['elapsed_seconds'],'mathematical_receipt_identical':True})
    for name,digest in manifest['candidate_sha256'].items():
        assert hashlib.sha256((CANDIDATE/name).read_bytes()).hexdigest()==digest,name
    (HERE/'replay.json').write_text(json.dumps({'passed':True,'all_input_bindings_checked':True,
        'candidate_unchanged':True,'checks':checks},indent=2)+'\n')
    for name in ['bounds.json','shape.json']:(output/name).unlink()
    output.rmdir()
    print('PASS independent isolated source bounds and shape replay',flush=True)


if __name__=='__main__':main()

"""Stage a paid-prefix donor view on the original four participants.

This command leaves services, configuration, requests and original owner permits
untouched. A prepared view is not a running native verifier.
"""
import argparse
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'Verification/public-audit/network'))
import anchor
from crypto import canonical, digest, verify
from donor_source_view import SCHEMA

ADDED = {'supply_disposition.py', 'donor_owner_continuation.py', 'donor_paid_prefix.py', 'donor_source_view.py',
         'donor_current_store.py', 'supply_interface_fault.py'}
CHANGED = {'source_semantics.py', 'ha_anchor.py', 'donor_arrival_live.py', 'live_timing.py'}
DOMAIN = 'original-supply-view-prepared'


def load(path):
    return json.loads(Path(path).read_text())


def once(path, value):
    raw = canonical(value)
    if path.exists():
        if path.read_bytes() != raw:
            raise ValueError('SUPPLY_VIEW_ARTIFACT_CHANGED:'+path.name)
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(raw)


def stage(box, work, checkpoint):
    checkpoint = subprocess.check_output(['git', 'rev-parse', checkpoint+'^{commit}'], cwd=ROOT, text=True).strip()
    manifest = load(box/'ha/deployment.json'); prepared = load(work/'prepared.json')
    request = load(work/'authorized-request.json'); permission = load(work/'owner-packet.json')['permission']
    argument = load(work/'authorized-source-input.json')
    payload = {}; hashes = {}
    for name in sorted(set(manifest['protocol']) | ADDED):
        raw = subprocess.check_output(['git', 'show', checkpoint+':Verification/public-audit/network/'+name], cwd=ROOT)
        hashed = hashlib.sha256(raw).hexdigest()
        if name not in CHANGED | ADDED and manifest['protocol'][name] != hashed:
            raise ValueError('SUPPLY_VIEW_UNRELATED_PROTOCOL_CHANGED:'+name)
        payload[name] = base64.b64encode(raw).decode(); hashes[name] = hashed
    revision = digest(hashes); home = work/'source-view'/revision
    once(home/'profile.json', dict(checkpoint=checkpoint, revision=revision, files=hashes))
    proofs = load(work/'source-view-fences.json')
    paid = Path('runtime/retained/iqa-actual77-donor-admission-20261106')
    specification = importlib.util.spec_from_file_location('original_supply_deploy', Path(__file__).with_name('public-donor-live-deploy.py'))
    deploy = importlib.util.module_from_spec(specification); specification.loader.exec_module(deploy)
    reports = {}
    for member in 'abcd':
        saved = home/('prepared-'+member+'.json')
        cfgpath = str(box/'local-anchor/config.json') if member == 'a' else manifest['nodes'][member]['home']+'/config.json'
        root = str(home/member) if member == 'a' else manifest['nodes'][member]['home']+'/supply-disposition/'+revision
        code = root+'/code/Verification/public-audit/network'
        paid_home = load(paid/('node-'+member+'.json'))['home']
        script = f'''import base64,hashlib,json,os,sys
from pathlib import Path
root=Path({root!r});code=Path({code!r});cfgpath=Path({cfgpath!r});paid=Path({paid_home!r})
space=os.statvfs(cfgpath.parent)
assert space.f_bavail*space.f_frsize>16*1024*1024,'SUPPLY_VIEW_STORAGE'
for name,encoded in {payload!r}.items():
 p=code/name;raw=base64.b64decode(encoded);p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw,'SUPPLY_VIEW_CODE_CHANGED'
 else:
  with p.open('xb') as stream:stream.write(raw)
assert {{n:hashlib.sha256((code/n).read_bytes()).hexdigest() for n in {list(hashes)!r}}}=={hashes!r}
sys.path.insert(0,str(code))
import donor_arrival_live as donor,source_readiness,supply_disposition
from donor_source_view import Engine
from crypto import app_private,canonical,digest,sign,verify
from anchor import public_key
from recovery_loop import birth,boot_identity
c=json.loads(cfgpath.read_text());me,signed,prefix=source_readiness.snapshot(c)
assert me=={member!r} and prefix=={prepared['prefix']!r},'SUPPLY_VIEW_CURRENT_PREFIX'
rows=[list(row[:4]) for row in signed]
evidence={{n:json.loads((paid/(n+'.json')).read_text()) for n in ['settings','input','output','facts','native','rows','vote']}}
evidence.update(member=me,current=prefix,objects={{n:source_readiness.sha(paid/'lib'/n) for n in evidence['native']['objects']}})
def once(path,value):
 raw=canonical(value)
 if path.exists():assert path.read_bytes()==raw,'SUPPLY_VIEW_FROZEN_INPUT_CHANGED'
 else:
  with path.open('xb') as stream:stream.write(raw)
once(root/'evidence.json',evidence);once(root/'fences.json',{proofs!r})
view=dict(schema={SCHEMA!r},producer=me,prefix=prefix,evidence=str(root/'evidence.json'),
 evidence_sha256=source_readiness.sha(root/'evidence.json'),proofs=str(root/'fences.json'),
 proofs_sha256=source_readiness.sha(root/'fences.json'))
c['donor_history']=view
engine=Engine(c)
try:
 engine.sync(rows);status=engine.status()
 assert status['prefix']==prefix and engine.process is None and status['backend'] is None,'SUPPLY_VIEW_UNEXPECTED_WORKER'
 actual=donor.argument(supply_disposition.context_at(c),rows,dict(type=donor.ACTION,source={request['body']['source']!r},
  stream={request['body']['stream']!r},request={request!r},peer=c['registry']['auditor1']['fingerprint'],scope={request['body']['scope']!r}))
 assert canonical(actual)==canonical({argument!r}),'SUPPLY_VIEW_NEW_INPUT_CHANGED'
 assert evidence['objects']=={prepared['reused_native_objects']!r},'SUPPLY_VIEW_NATIVE_OBJECTS'
 point=dict(schema='original-supply-view-prepared/v1',member=me,prefix=prefix,protocol={revision!r},
  current_configuration=digest(json.loads(cfgpath.read_text())),candidate_configuration=digest(c),
  view=view,request=digest({request!r}),owner_permission=digest({permission!r}),source_input=digest(actual),
  native_objects=evidence['objects'],native_preparations=0,native_computations=0,journal_writes=0,economic_requests=0)
 vote_path=root/'prepared.json'
 if vote_path.exists():
  vote=json.loads(vote_path.read_text());assert verify(public_key(c['registry']['anchor']),{DOMAIN!r},vote)['point']==point
 else:
  vote=sign(app_private(Path(c['pki'])/'anchor'),{DOMAIN!r},dict(point=point,boot=boot_identity(),pid=os.getpid(),birth=birth(os.getpid()),uid=os.getuid()))
  once(vote_path,vote)
 once(root/'candidate.json',c)
 assert source_readiness.snapshot(c)[2]==prefix,'SUPPLY_VIEW_PREFIX_MOVED'
 print(json.dumps(dict(vote=vote,code=str(code),candidate=str(root/'candidate.json'),original_config=str(cfgpath))))
finally:engine.close()
'''
        if not saved.exists():
            once(saved, json.loads(deploy.execute(member, script, manifest, 180)))
        report = load(saved)
        receipt = verify(anchor.public_key(manifest['trust']['members'][member]), DOMAIN, report['vote'])
        point = receipt['point']
        if (point['member'] != member or point['prefix'] != prepared['prefix'] or point['protocol'] != revision or
                point['view']['schema'] != SCHEMA or point['request'] != digest(request) or
                point['owner_permission'] != digest(permission) or point['source_input'] != digest(argument) or
                point['native_objects'] != prepared['reused_native_objects'] or
                any(point[n] != 0 for n in ('native_preparations', 'native_computations', 'journal_writes', 'economic_requests'))):
            raise ValueError('SUPPLY_VIEW_MEMBER_BINDING')
        reports[member] = report
        print('ORIGINAL_PAID_VIEW_PREPARED', member, flush=True)
    once(home/'prepared.json', dict(checkpoint=checkpoint, protocol=revision, prefix=prepared['prefix'], nodes=reports,
        owner_permission=digest(permission), installed=False, native_preparations=0, native_computations=0, economic_requests=0))
    print(json.dumps(dict(exit=0, original_members=list(reports), installed=False, receipt=str(home/'prepared.json'))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--box', type=Path, default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--checkpoint', required=True)
    args = parser.parse_args()
    stage(args.box.resolve(), args.work.resolve(), args.checkpoint)


if __name__ == '__main__':
    main()

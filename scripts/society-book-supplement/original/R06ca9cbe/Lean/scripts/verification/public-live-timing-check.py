"""Independent original-line timing/ledger/own-next consumer."""
import argparse
import base64
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import public_key
from crypto import canonical, digest, verify
from online_privacy import source_input
from online_privacy_check import wire_observations, tls_streams
from quorum import verify_certificate
from recovery_loop import save
from ha_timing_check import MOUTHS, MODULE, no_private


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


roll = module('live_timing_consumer_transport', 'public-live-timing.py')
load, sha = roll.load, roll.sha


def public_closed(box, home):
    """A historical closure cannot authorize private work in a reopened epoch."""
    manifest = load(box/'ha/deployment.json')
    closed = load(home/'closed.json')
    assert set(closed) == set('abcd')
    for member, signed in closed.items():
        report = verify(public_key(manifest['trust']['members'][member]), 'public-epoch-closed', signed)
        assert report['member'] == member and not report['remaining']
        assert report['source'] == manifest['source']
        code = f'''import json,sys
sys.path.insert(0,{str(NETWORK) if member=='a' else manifest['nodes'][member]['code']!r})
from recovery_loop import birth,boot_identity
from pathlib import Path
r={report!r};assert r['boot']==boot_identity()
assert all(birth(p['pid'])!=p['birth'] for p in r['processes'])
home=Path({str(box/'local-anchor') if member=='a' else manifest['nodes'][member]['home']!r})
if {member in 'ac'!r}:
 state=Path({str(box/'runtime') if member=='a' else manifest['nodes'][member]['home']+'/ha/runtime'!r})
 assert (state/'STOP').is_file(),'PUBLIC_EPOCH_REOPENED'
 current=json.loads((state/'ha-status.json').read_text())['body']
 assert birth(current['pid'])!=current['birth'],'PUBLIC_COORDINATOR_STILL_ALIVE'
if {member!='a'!r}:
 current=json.loads((home/'status.json').read_text())['body']['process']
 assert birth(current['pid'])!=current['birth'],'PUBLIC_ANCHOR_STILL_ALIVE'
print('PUBLIC_EPOCH_CLOSED')
'''
        assert roll.execute(member, code, manifest, 40).strip() == 'PUBLIC_EPOCH_CLOSED'
    return manifest


def frames(box):
    """Invoke only while every observed original public role is stopped."""
    home = box/'ha/live-timing'
    manifest = public_closed(box, home)
    started = time.monotonic_ns()
    literal = load(home/'original-events.json')
    cfg = manifest['mac']['service']
    inputs = [source_input(cfg, literal[:i], json.loads(literal[i][3])['body']) for i in range(24, 27)]
    source = ROOT/'Lean/scripts/verification/ha-timing-owner-source.lean'
    lean = cfg['backend'][0]
    env = os.environ.copy()
    env['LEAN_PATH'] = str(box.parent/'privacy/timing-01/lib')
    output = {}
    for lane, variant in (('one', 'private-one'), ('two', 'private-two')):
        command = [lean, '--trust=0', '-j1', '-DElab.async=false', '-DwarningAsError=true', '--run', str(source), variant]
        run = subprocess.run(command, cwd=ROOT/'Lean', env=env, text=True, capture_output=True,
                             input=''.join(canonical(x).decode()+'\n' for x in inputs), timeout=120)
        assert run.returncode == 0 and not run.stderr, run.stderr
        answers = [json.loads(line) for line in run.stdout.splitlines()]
        assert len(answers) == 3
        for i, answer in enumerate(answers):
            native = json.loads(literal[i+24][3])['body']['native']
            assert answer['native'] == native
            assert answer['actualPublic'] == answer['rebuiltPublic'] == native['next']
            assert answer['consumedRequests'] == i+1
            assert all(p['sourceInitial'] == p['actualNext'] == p['rebuiltNext'] for p in answer['frame'])
            assert answer['frame'][3]['actualNext'] == ('39' if lane == 'one' else '38')
        output[lane] = {'argv': command, 'answers': answers}
    save(home/'owner-nexts.json', {'closed': sha(home/'closed.json'), 'started_ns': started,
        'finished_ns': time.monotonic_ns(), 'source': sha(source), 'inputs': inputs, 'lanes': output,
        'proof_artifacts': {name: sha(Path(env['LEAN_PATH'])/(MODULE+name+'.olean')) for name in ('Timing', 'Timing/Source')}})
    print('INDEPENDENT LIVE OWN-NEXT PASS: original inputs; 2 source-generated frames; 6 exact whole nexts; public roles closed', flush=True)


def current_runtime(box, manifest):
    home = box/'ha/continuous'
    home.mkdir(exist_ok=True)
    literal = roll.spare.rows(manifest['mac']['service']['database'])
    result = {}
    for owner, member in (('mac', 'a'), ('spark', 'c')):
        cfg = manifest[owner]['service']
        no_private(cfg)
        state = str(box/'runtime') if member == 'a' else manifest['nodes'][member]['home']+'/ha/runtime'
        codepath = str(NETWORK) if member == 'a' else manifest['nodes'][member]['code']
        code = f'''import json,sys,subprocess,os
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
from crypto import digest
p=Path({state!r});s=json.loads((p/'ha-status.json').read_text());b=s['body']
assert birth(b['pid'])==b['birth'] and b['boot']==boot_identity()
argv=shlex.split(subprocess.check_output(['ps','-ww','-p',str(b['pid']),'-o','command='],text=True))
assert argv[-3:]==[{codepath+'/live_timing.py'!r},'coordinator',{manifest[owner]['controller']['service'].replace('/service.json','/controller.json')!r}]
v={{'status':s,'argv':argv}}
if b['phase']=='leader':
 r=json.loads(Path({str(Path(cfg['database']).parent/'ha-service-ready.json')!r}).read_text());rb=r['body'];w=rb['public_timing']['worker']
 assert rb['grant']['point']==b['grant']['point'] and birth(rb['pid'])==rb['birth']
 assert birth(w['pid'])==w['birth'] and os.getpgid(w['pid'])==b['service']['pgid']
 assert rb['public_timing']['entrypoint']=='live_timing.py'
 current=json.loads((p/'ha-service.json').read_text());current['recover_from_anchor']=True
 assert rb['public_timing']['configuration']==digest(current)
 actual=shlex.split(subprocess.check_output(['ps','-ww','-p',str(w['pid']),'-o','command='],text=True))
 assert actual==w['argv']==current['online_privacy']['worker']['command']
 assert w['argv'][-1]=='public'
 v['ready']=r
print(json.dumps(v))
'''
        code = 'import shlex\n'+code
        value = json.loads(roll.execute(member, code, manifest, 45))
        body = verify(public_key(manifest['owners'][owner]), 'ha-coordinator', value['status'])
        assert time.time()-body['at'] < 20
        assert body['configuration'] == digest(manifest[owner]['controller'])
        if 'ready' in value:
            ready = verify(public_key(cfg['registry']['server']), 'ha-service-ready', value['ready'])
            assert ready['head'] in {row[2] for row in literal}, 'PUBLIC_STARTUP_HEAD_IS_NOT_AN_ACTUAL_PREFIX'
        result[owner] = value
        if member == 'c':
            library = box.parent/'privacy/network-accepted-03/lib'
            base_inventory = load(manifest['semantic']['configurations']['a']['closure'])
            extra = {str(p.relative_to(library)): sha(p) for p in library.rglob('*')
                     if p.is_file() and str(p.relative_to(library)) not in base_inventory}
            worker = cfg['online_privacy']['worker']
            script = f'''import hashlib,json,os
from pathlib import Path
s=Path({cfg['public_base_source']['lean_path']!r});p=Path({worker['lean_path'].split(':')[0]!r})
base={list(base_inventory)!r};extra={extra!r}
assert {{str(f.relative_to(p)) for f in p.rglob('*') if f.is_file()}}==set(base)|set(extra)
for n in base:
 a=(s/n).stat();b=(p/n).stat();assert (a.st_dev,a.st_ino)==(b.st_dev,b.st_ino)
for n,w in extra.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==w
assert hashlib.sha256(Path({worker['command'][0]!r}).read_bytes()).hexdigest()=={worker['compiler_sha256']!r}
assert hashlib.sha256((Path({worker['cwd']!r})/'scripts/verification/public-network-privacy-source.lean').read_bytes()).hexdigest()=={sha(ROOT/'Lean/scripts/verification/public-network-privacy-source.lean')!r}
print('EXACT_PUBLIC_LIBRARY_VIEW')
'''
            assert roll.execute(member, script, manifest, 60).strip() == 'EXACT_PUBLIC_LIBRARY_VIEW'
    assert sum(v['status']['body']['phase'] == 'leader' for v in result.values()) == 1
    save(home/'runtime-independent.json', result)
    return result


def runtime(box, manifest):
    assert len(roll.spare.rows(manifest['mac']['service']['database'])) == 27
    return current_runtime(box, manifest)


def audit(box, check_main=False, native_runtime=None):
    home = box/'ha/live-timing'
    manifest = load(box/'ha/deployment.json')
    if native_runtime is None:
        native_runtime = module('live_timing_native_consumer', 'public-native-spare-check.py').runtime(box, manifest)
    assert native_runtime['members'] == 'abcd' and native_runtime['events'] == 27
    installed = load(home/'installed.json')
    assert manifest['public_timing']['release'] == installed['release'] == digest(manifest['protocol'])
    for name, wanted in manifest['protocol'].items():
        assert sha(NETWORK/name) == wanted
    literal = load(home/'original-events.json')
    assert len(literal) == 27 and [list(r) for r in roll.spare.rows(manifest['mac']['service']['database'])] == literal
    own = load(home/'owner-nexts.json')
    assert own['source'] == sha(ROOT/'Lean/scripts/verification/ha-timing-owner-source.lean')
    assert own['closed'] == sha(home/'closed.json') and own['started_ns'] < own['finished_ns']
    privacy = load(home/'privacy-independent/accepted.json')
    assert privacy['mode'] == 'source-network-online-and-timing'
    assert privacy['audit_source_sha256'] == sha(Path(__file__).with_name('public-privacy-audit.py'))
    for name in ('source', 'network', 'online', 'timing'):
        assert privacy[name+'_receipt_sha256'] == sha(home/'privacy-independent'/name/'accepted.json')
        assert privacy[name] == load(home/'privacy-independent'/name/'accepted.json')
    assert privacy['timing']['standard_axiom_mouths'] == len(MOUTHS)
    assert privacy['timing']['owner_source_sha256'] == own['source']
    for name, wanted in privacy['timing']['proof_sources'].items():
        assert sha(ROOT/'Lean'/(MODULE+name+'.lean')) == wanted
        assert sha(home/'privacy-independent/timing/lib'/(MODULE+name+'.olean')) == own['proof_artifacts'][name]
        assert sha(box.parent/'privacy/timing-01/lib'/(MODULE+name+'.olean')) == own['proof_artifacts'][name]
    cfg = manifest['mac']['service']
    expected = [source_input(cfg, literal[:i], json.loads(literal[i][3])['body']) for i in range(24, 27)]
    assert own['inputs'] == expected
    for lane in ('one', 'two'):
        for i, answer in enumerate(own['lanes'][lane]['answers']):
            native = json.loads(literal[i+24][3])['body']['native']
            assert answer['native'] == native and answer['actualPublic'] == answer['rebuiltPublic'] == native['next']
            assert all(p['sourceInitial'] == p['actualNext'] == p['rebuiltNext'] for p in answer['frame'])
            assert answer['frame'][3]['actualNext'] == ('39' if lane == 'one' else '38')
    inventories = load(home/'public-inventories.json')
    if isinstance(inventories, dict):inventories = [inventories]
    assert inventories
    closed = load(home/'closed.json')
    assert set(closed) == set('abcd')
    for member in 'abcd':
        reports = [verify(public_key(manifest['trust']['members'][member]), 'public-epoch-inventory', r[member]) for r in inventories]
        report = verify(public_key(manifest['trust']['members'][member]), 'public-epoch-closed', closed[member])
        assert report['member'] == member and report['source'] == manifest['source'] and not report['remaining']
        wanted = {(p['pid'],p['birth']) for r in reports for p in r['processes']}
        assert wanted and wanted == {(p['pid'],p['birth']) for p in report['processes']}
        assert all('private-two' not in p['command'] and '__private_audit' not in p['command'] for p in report['processes'])
    epochs = load(home/'epochs.json')
    assert {e['owner'] for e in epochs} == {'mac', 'spark'} and len(epochs) == 2
    key = public_key(cfg['registry']['server'])
    for epoch in epochs:
        owner = epoch['owner']
        state = verify(public_key(manifest['owners'][owner]), 'ha-coordinator', epoch['state'])
        ready = verify(key, 'ha-service-ready', epoch['ready'])
        assert state['phase'] == 'leader' and state['head']['seq'] == 27
        assert state['grant']['point'] == ready['grant']['point'] and ready['public_timing']['entrypoint'] == 'live_timing.py'
        assert ready['public_timing']['worker']['argv'] == manifest[owner]['service']['online_privacy']['worker']['command']
        directory = home/('epoch-'+owner)
        public = {n: {'app': v['app']} for n, v in cfg['registry'].items()}
        boundaries, wires = wire_observations(directory/'boundary.jsonl', public)
        observations = load(directory/'observations.json')
        assert len(observations) == 6 and len(wires) >= 6
        selected = []
        for i, observation in enumerate(observations):
            raw = observation['body'];actor = raw['request']['body']['actor']
            client = verify(public_key(cfg['registry']['auditor'+actor]), 'online-client-observation', observation)
            verify(public_key(cfg['registry']['auditor'+actor]), 'lookup', client['request'])
            verify(key, 'challenge', client['challenge'])
            response = verify(key, 'lookup-response', client['response'])
            assert response['request'] == digest(client['request']) and client['tls'] == 'TLSv1.3'
            actual = response['result'];row = literal[i//2+24];event = json.loads(row[3])['body']
            assert actual['ledger'] == json.loads(row[3]) and actual['event'] == event and actual['head'] == row[2]
            verify_certificate(manifest['trust'], actual['anchor'], source=cfg['source'], stream=cfg['stream'],
                               seq=row[0], previous=row[1], head=row[2], message=actual['ledger'])
            clock = [client['times'][n] for n in ('connect_start_ns','connected_ns','challenge_received_ns','request_sent_ns','response_received_ns')]
            assert clock == sorted(clock)
            matches = [(w, c, r, s) for w, c, r, s in wires if (c, r, s) == (client['challenge'], client['request'], client['response'])]
            assert len(matches) == 1
            selected.append(matches[0][0]['index'])
            assert any(b['seq'] == row[0] and b['phase'] == 'reply' and b['input'] == expected[i//2]
                       and b['event'] == digest(event) and b['native'] == digest(event['native']) for b in boundaries)
        assert len(set(selected)) == 6
        assert len(tls_streams(directory)) == 12
    assert epochs[1]['state']['body']['grant']['point']['epoch'] > epochs[0]['state']['body']['grant']['point']['epoch']
    runtime(box, manifest)
    paths = ['Verification/public-audit/network/live_timing.py',
             *['Lean/scripts/verification/public-live-timing'+s+'.py' for s in ('', '-actual', '-check')]]
    inputs = {p: sha(ROOT/p) for p in paths}
    if check_main:
        for p, wanted in inputs.items():
            assert hashlib.sha256(subprocess.check_output(['git', 'show', 'refs/heads/main:'+p], cwd=ROOT)).hexdigest() == wanted
    result = {'source_inputs': inputs, 'original_events': 27, 'head': literal[-1][2], 'candidate_epochs': 2,
              'native_members': 'abcd', 'complete_tls_lookups': 12, 'whole_own_nexts': 6,
              'closed': sha(home/'closed.json'), 'owner_nexts': sha(home/'owner-nexts.json'),
              'main_verified': check_main, 'at': time.time()}
    save(home/'independent.json', result)
    print('INDEPENDENT ORIGINAL LIVE TIMING PASS: 2 physical candidates; 4 native voters; original27; 12 full TLS lookups; 6 own-root nexts; no duplicate payment', flush=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    parser.add_argument('--frames', action='store_true')
    parser.add_argument('--check-main', action='store_true')
    args = parser.parse_args()
    (frames if args.frames else audit)(args.box.resolve(), **({} if args.frames else {'check_main': args.check_main}))

"""Independent consumer of fourth-verifier admission and physical partition journals."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shlex
import sqlite3
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import public_key, ledger_hash, verify_commit
from crypto import canonical, digest, verify
from ha_anchor import verify_quorum
from ha_quorum import Quorum
from recovery_loop import save
from source_semantics import Engine
import governance
import energy

spec = importlib.util.spec_from_file_location('spare_check_transport', Path(__file__).with_name('public-ha-deploy.py'))
transport = importlib.util.module_from_spec(spec)
spec.loader.exec_module(transport)


def load(path):
    return json.loads(Path(path).read_text())


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def certificate(cert, trust):
    point = cert['point']
    assert point['previous'] == list('abc') and point['current'] == list('abcd')
    assert point['cluster'] == digest(trust)
    assert [v['member'] for v in cert['votes']] == list('abcd')
    for vote in cert['votes']:
        value = verify(public_key(trust['members'][vote['member']]), 'native-source-ready', vote['receipt'])
        assert value['point'] == point and value['member'] == vote['member']
        assert value['compiler'] == point['descriptors']['base']['compiler']
    return point


def admitted_runtime(box, manifest):
    cert = manifest['native_admission']
    point = certificate(cert, manifest['trust'])
    with sqlite3.connect(Path(manifest['mac']['service']['database']).as_uri()+'?mode=ro', uri=True) as db:
        committed = db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
    assert len(committed) >= point['prefix']['seq']
    assert committed[point['prefix']['seq']-1][2] == point['prefix']['head']
    current = {'seq': len(committed), 'head': committed[-1][2]}
    assert manifest['semantic']['native_members'] == 'abcd'
    assert all(manifest[o]['service']['governance_members'] == list('abcd') for o in ('mac', 'spark'))
    q = Quorum(manifest['mac']['service'])
    checked = {}
    entrypoint = 'live_timing.py' if manifest.get('public_timing') else 'native_spare.py'
    for member in 'abcd':
        state = q.nodes[member].call('semantic-status')
        assert state['prefix'] == current and state['descriptor'] == point['descriptors']['base'] and state['backend'], 'NATIVE_COMMITTED_PREFIX_NOT_READY'
        if member == 'a':
            codepath, home = str(NETWORK), str(box/'local-anchor')
            process = load(box/'runtime/ha-status.json')['body']['members']['a']
            status = None
        else:
            item = manifest['nodes'][member]
            codepath, home = item['code'], item['home']
            status = load(box/'ha/native-spare/installed.json')['admission']
            process = None
        script = f'''import hashlib,json,os,shlex,sqlite3,subprocess,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
from crypto import digest
c=json.loads(Path({home+'/config.json'!r}).read_text());w={state['backend']!r}
assert c['governance_members']==list('abcd') and digest(c['native_admission'])=={digest(cert)!r}
assert birth(w['pid'])==w['birth'] and w['boot']==boot_identity() and os.getpgid(w['pid'])==w['pgid']==w['pid']
assert shlex.split(subprocess.check_output(['ps','-ww','-p',str(w['pid']),'-o','command='],text=True).strip())==c['semantic']['backend']
for feature in ('semantic','governance','energy','continuation','handoff'):
 s=c[feature];inventory=json.loads(Path(s['closure']).read_text())
 assert hashlib.sha256(Path(s['closure']).read_bytes()).hexdigest()==s['descriptor']['closure_sha256']
 assert hashlib.sha256(Path(s['exporter']).read_bytes()).hexdigest()==s['descriptor']['exporter_sha256']
 assert all(hashlib.sha256((Path(s['lean_path'])/n).read_bytes()).hexdigest()==h for n,h in inventory.items())
 assert subprocess.check_output([s['backend'][0],'--githash'],text=True).strip()==s['descriptor']['compiler']
 assert s['backend'][1:]==['--trust=0','-j1','--run',s['exporter'],'private-one']
with sqlite3.connect(Path(c['database']).as_uri()+'?mode=ro',uri=True) as db:
 policies={{n:json.loads(db.execute('SELECT value FROM '+n).fetchone()[0]) for n in ('ha_governance_policy','ha_energy_policy','ha_continuation_policy','ha_handoff_policy')}}
 assert all(v['members']==list('abc') and v['descriptor']==c[n]['descriptor']
            for n,v in zip(('governance','energy','continuation','handoff'),policies.values()))
 persisted=json.loads(db.execute('SELECT value FROM native_admission').fetchone()[0]);assert persisted==c['native_admission']
 rows=db.execute('SELECT seq,previous,hash,message FROM entries ORDER BY seq').fetchall()
 assert len(rows)=={current['seq']!r} and rows[-1][2]=={current['head']!r}
 assert rows[{point['prefix']['seq']-1!r}][2]=={point['prefix']['head']!r}
host=json.loads(Path({home+'/status.json'!r}).read_text()) if {member!='a'!r} else None
r=host['body']['process'] if host else {process!r}
assert birth(r['pid'])==r['birth'] and r['argv'][1:]==[{codepath+'/'+entrypoint!r},'anchor',{home+'/config.json'!r}]
assert hashlib.sha256(Path({codepath+'/native_spare.py'!r}).read_bytes()).hexdigest()=={sha(NETWORK/'native_spare.py')!r}
assert hashlib.sha256(Path({codepath+'/'+entrypoint!r}).read_bytes()).hexdigest()=={sha(NETWORK/entrypoint)!r}
print(json.dumps({{'policies':policies,'admission':persisted,'process':r,'host':host,'worker':w,'configuration':c,'events':len(rows)}}))
'''
        if member == 'a':
            value = json.loads(subprocess.check_output([sys.executable, '-c', script], text=True))
        else:
            value = json.loads(transport.remote(member, script, timeout=90, python=manifest['nodes'][member]['python']))
            host = verify(public_key(manifest['trust']['members'][member]), 'recovery-host-status', value['host'])
            assert host['entrypoint'] == entrypoint and host['admission'] == digest(cert)
        checked[member] = value
    ready = load(box/'ha/native-spare/ready-studio.json')
    inventory_path = box/'ha/native-spare/payload/inventory.json'
    assert sha(inventory_path) == ready['inventory_sha256']
    inventory = load(inventory_path)
    root = ready['root']
    item = manifest['nodes']['d']
    # Check the bound runtime inventory in bounded transport batches.
    count = 0
    for offset in range(0, len(inventory), 1000):
        batch = dict(list(inventory.items())[offset:offset+1000])
        code = f"import hashlib,json\nfrom pathlib import Path\np=Path({root!r});v={batch!r}\nassert all(hashlib.sha256((p/n).read_bytes()).hexdigest()==h for n,h in v.items())\nprint(len(v))\n"
        count += int(transport.remote('d', code, timeout=45, python=item['python']))
    assert count == ready['files'] == len(inventory) and ready['machine'] == 'arm64'
    save(box/'ha/native-spare/current-independent.json', checked)
    print('INDEPENDENT FOUR NATIVE RUNTIME PASS: actual abcd workers; original admission prefix retained; current'+str(current['seq'])+'; historical abc policies unchanged', flush=True)
    return {'members': 'abcd', 'events': current['seq'], 'head': current['head'], 'admission': digest(cert), 'studio_files': count,
            'source_inputs': {path: sha(ROOT/path) for path in
                ['Verification/public-audit/network/native_spare.py']+
                ['Lean/scripts/verification/public-native-spare'+suffix+'.py' for suffix in ('', '-node', '-actual', '-rpc', '-check')]+
                ['Lean/scripts/verification/public-semantic-check.py', 'Lean/scripts/verification/public-governance-check.py']}}


def runtime(box, manifest):
    result = admitted_runtime(box, manifest)
    assert result['events'] == 27, 'USE_CURRENT_ADMITTED_RUNTIME_FOR_A_LATER_PREFIX'
    return result


def original_cases(box):
    manifest = load(box/'ha/deployment.json')
    home = box/'ha/native-spare/actual-01'
    required = ('trust.json', 'admission.json', 'prefix.json', 'produced.json', 'pending.json',
                'crash.json', 'forged.json', 'before-restore.json', 'after-restore.json', 'duplicate.json')
    if not all((home/('missing-'+m)/name).is_file() for m in 'abcd' for name in required):
        raise RuntimeError('PHYSICAL_NATIVE_SPARE_EVIDENCE_REQUIRED')
    original = manifest['mac']['service']
    with sqlite3.connect(Path(original['database']).as_uri()+'?mode=ro', uri=True) as db:
        literal = db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
    assert len(literal) >= 27
    literal = literal[:27]
    result = []
    for missing in 'abcd':
        directory = home/('missing-'+missing)
        trust = load(directory/'trust.json')
        point = certificate(load(directory/'admission.json'), trust)
        assert point['prefix'] == {'seq': 24, 'head': literal[23][2]}
        prefix = load(directory/'prefix.json')
        assert [tuple(row) for row in prefix] == literal[:24]
        produced = load(directory/'produced.json')
        assert produced == [json.loads(row[3]) for row in literal[24:]]
        pending = load(directory/'pending.json')
        intent = pending['intent']
        assert [v['member'] for v in intent['votes']] == [m for m in 'abcd' if m != missing]
        expected = dict(token=intent['point']['token'], seq=25, previous=point['prefix']['head'],
                        head=literal[24][2], message=digest(produced[0]), operation_id=produced[0]['body']['request']['body']['request_id'])
        verify_quorum({'ha': {'trust': trust}}, intent, 'ha-intent', expected)
        assert pending['message'] == produced[0] and pending['previous'] == point['prefix']['head']
        crash = load(directory/'crash.json')
        assert crash['exit'] == 73 and crash['pending_sha256'] == sha(directory/'pending.json')
        counts = {member: {'false': 0, 'isolation': 0} for member in 'abcd'}
        appended = {member: set() for member in 'abcd'}
        for path in (directory/'rpc').glob('*.json'):
            signed = load(path)
            member = signed['body']['member']
            value = verify(public_key(trust['members'][member]), 'native-spare-rpc', signed)
            assert value['helper_sha256'] == sha(Path(__file__).with_name('public-native-spare-rpc.py'))
            assert value['journal_sha256'] == sha(NETWORK/'native_spare.py')
            assert value['started_ns'] <= value['finished_ns']
            if value['operation'] != 'call':
                continue
            body = value['input']
            if body['op'] in {'ha-grant', 'ha-stage', 'append'}:
                proof = body['owner_proof']
                assert verify(public_key(manifest['owners'][body['owner']]), 'ha-owner-request', proof) == {'request': digest({k:v for k,v in body.items() if k != 'owner_proof'})}
            error = value['answer'].get('error')
            if body['op'] == 'append' and error is None:
                seq = body['seq']
                assert 25 <= seq <= 27 and body['message'] == produced[seq-25]
                intent_point = body['intent']['point']
                assert intent_point == dict(token=body['grant']['point'], seq=seq, previous=literal[seq-1][1],
                                     head=literal[seq-1][2], message=digest(body['message']),
                                     operation_id=body['message']['body']['request']['body']['request_id'])
                verify_quorum({'ha': {'trust': trust}}, body['intent'], 'ha-intent', intent_point)
                verify_quorum({'ha': {'trust': trust}}, body['grant'], 'ha-grant', intent_point['token'])
                if value['source_status']['backend']:
                    assert value['source_status']['prefix'] == {'seq': seq-1, 'head': literal[seq-1][1]}
                    appended[member].add(seq)
            if body['op'] == 'ha-stage' and body.get('message') == load(directory/'forged.json'):
                if member == missing:
                    assert error == 'TASK_NODE_ISOLATED'
                    counts[member]['isolation'] += 1
                else:
                    assert error == 'HANDOFF_SOURCE_MISMATCH' and value['source_status']['backend']
                    assert len(value['tables']['entries']) == 24 and not value['tables']['ha_intents']
                    counts[member]['false'] += 1
        assert all(counts[m]['false'] >= 1 for m in 'abcd' if m != missing) and counts[missing]['isolation'] >= 1
        assert all(appended[m] == {25, 26, 27} for m in 'abcd')
        for stage in ('before-restore', 'after-restore'):
            snapshots = load(directory/(stage+'.json'))
            for member in 'abcd':
                value = verify(public_key(trust['members'][member]), 'native-spare-rpc', snapshots[member])
                entries = value['tables']['entries']
                expected_count = 24 if member == missing and stage == 'before-restore' else 27
                assert len(entries) == expected_count
                assert [(row[1], row[2], row[3], row[4]) for row in entries] == literal[:expected_count]
                for row in entries:
                    verify_commit(trust['members'][member], json.loads(row[5]), source=original['source'], stream='recovery',
                                  seq=row[1], previous=row[2], head=row[3], message=json.loads(row[4]), cluster=digest(trust))
                for policy in ('ha_governance_policy', 'ha_energy_policy', 'ha_continuation_policy', 'ha_handoff_policy'):
                    assert len(value['tables'][policy]) == 1
                    old_policy = json.loads(value['tables'][policy][0][0])
                    family = policy.removeprefix('ha_').removesuffix('_policy')
                    assert old_policy == {'members': list('abc'), 'descriptor': point['descriptors'][family]}
                assert json.loads(value['tables']['native_admission'][0][0]) == load(directory/'admission.json')
                if stage == 'after-restore':
                    assert load(directory/'duplicate.json')[member] == json.loads(entries[24][5])
                    assert len({json.loads(row[4])['body']['request']['body']['request_id'] for row in entries}) == 27
        assert produced[0]['body']['native']['reason'] == 'DELIVERED'
        assert produced[0]['body']['native']['before']['energy'] == ['2','0','0','3']
        assert produced[0]['body']['native']['next']['energy'] == ['0']*4
        assert [p['body']['native']['reason'] for p in produced[1:]] == ['UNAUTHORIZED', 'UNFUNDED']
        result.append({'missing': missing, 'intent_members': [v['member'] for v in intent['votes']], 'paid_energy': 5})
    engine = Engine({**manifest['semantic']['configurations']['a'], 'replay_seconds': 180})
    try:
        engine.sync(literal)
    finally:
        engine.close()
        governance.close_readers()
        energy.close_readers()
    save(home/'independent.json', {'cases': result, 'original_events': 27, 'transport': 'Guarded SSH control with original owner proofs; original Journal votes and commits'})
    print('INDEPENDENT PHYSICAL SPARE PASS: all four missing-member sets; 12 real source refusals; four crash/recovery paths; paid5 once per replica history; exact fourth-member catch-up', flush=True)
    return result


def actual(box):
    manifest = load(box/'ha/deployment.json')
    with sqlite3.connect(Path(manifest['mac']['service']['database']).as_uri()+'?mode=ro', uri=True) as db:
        assert db.execute('SELECT count(*) FROM events').fetchone()[0] == 27
    return original_cases(box)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    parser.add_argument('--runtime-only', action='store_true')
    args = parser.parse_args()
    box = args.box.resolve()
    machine = runtime(box, load(box/'ha/deployment.json'))
    cases = [] if args.runtime_only else actual(box)
    save(box/'ha/native-spare/independent.json', {'runtime': machine, 'cases': cases, 'audit_sha256': sha(__file__)})

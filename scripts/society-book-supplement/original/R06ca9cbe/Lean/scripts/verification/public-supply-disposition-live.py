"""Prepare the actual90 successor using the original owner and paid native source."""
import argparse
import base64
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
import anchor
from crypto import app_private, canonical, digest, sign, verify
import donor_arrival_live as donor
import donor_owner_continuation as continuation
import source_readiness
import supply_disposition

CHECKPOINT = 'e48b74c6fca71124cc2e0f32b94586e8be311ff8'
CHANGED = {'source_semantics.py', 'ha_anchor.py', 'donor_arrival_live.py'}
ADDED = {'supply_disposition.py', 'donor_owner_continuation.py'}


def load(path):
    return json.loads(Path(path).read_text())


def once(path, value):
    raw = canonical(value)
    if path.exists():
        if path.read_bytes() != raw:
            raise ValueError('SUPPLY_PREPARED_ARTIFACT_CHANGED:'+path.name)
    else:
        with path.open('xb') as stream:
            stream.write(raw)


def transport():
    path = Path(__file__).with_name('public-donor-live-deploy.py')
    spec = importlib.util.spec_from_file_location('supply_original_deploy', path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def profile(manifest):
    payload = {}; hashes = {}
    for name in sorted(set(manifest['protocol']) | ADDED):
        raw = subprocess.check_output(['git', 'show', CHECKPOINT+':Verification/public-audit/network/'+name], cwd=ROOT)
        hashed = hashlib.sha256(raw).hexdigest()
        if name not in CHANGED | ADDED and manifest['protocol'][name] != hashed:
            raise ValueError('SUPPLY_UNRELATED_PROTOCOL_CHANGED:'+name)
        payload[name] = base64.b64encode(raw).decode(); hashes[name] = hashed
    return payload, hashes


def owner(box, work):
    prepared = load(work/'prepared.json'); expected = prepared['prefix']
    intent = load(work/'intent.json'); wanted = load(work/'owner-point.json')
    if prepared['checkpoint'] != CHECKPOINT or digest(intent) != prepared['intent'] or digest(wanted) != prepared['owner_point']:
        raise ValueError('SUPPLY_ORIGINAL_REQUEST_CHANGED')
    manifest = load(box/'ha/deployment.json'); config = load(box/'local-anchor/config.json')
    _, signed, current = source_readiness.snapshot(config)
    if current != expected:
        raise ValueError('SUPPLY_ORIGINAL_PREFIX_MOVED')
    rows = [list(row[:4]) for row in signed]
    payload, hashes = profile(manifest); revision = digest(hashes)
    entry = manifest['nodes']['c']; code = entry['home']+'/code/'+revision+'/Verification/public-audit/network'
    remote_work = entry['home']+'/supply-disposition/'+revision
    owner_profile = manifest['spark']['service']['ha']['owner_profile']
    objects = prepared['reused_native_objects']
    resource = dict(schema='original-supply-protocol-resource/v1', owner='actual90-supply-disposition',
        node='c', state='ComputeNode/state/public-anchor-spark-20261102', remote=remote_work,
        consumer='original-owner-permit and actual90 same-request continuation',
        source_bytes=sum(len(base64.b64decode(raw)) for raw in payload.values()),
        max_growth_bytes=16*1024*1024, native_preparation=0, archive_root=str(work))
    once(work/'protocol.json', dict(checkpoint=CHECKPOINT, revision=revision, files=hashes))
    once(work/'resource-plan.json', resource)
    script = f'''import base64,hashlib,json,os,sys
from pathlib import Path
code=Path({code!r});home=Path({entry['home']!r});work=Path({remote_work!r})
space=os.statvfs(home);needed={resource['max_growth_bytes']!r}
assert space.f_bavail*space.f_frsize>needed,'SUPPLY_PROTOCOL_STORAGE'
for name,encoded in {payload!r}.items():
 p=code/name;raw=base64.b64decode(encoded);p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw,'SUPPLY_PROTOCOL_BYTES'
 else:
  with p.open('xb') as stream:stream.write(raw)
assert {{name:hashlib.sha256((code/name).read_bytes()).hexdigest() for name in {list(hashes)!r}}}=={hashes!r}
sys.path.insert(0,str(code))
import source_readiness,supply_disposition,donor_owner_continuation as own
from crypto import app_private,canonical,digest,sign,verify
from anchor import public_key
from recovery_loop import birth,boot_identity
c=json.loads((home/'config.json').read_text());member,signed,prefix=source_readiness.snapshot(c)
assert member=='c' and prefix=={expected!r},'SUPPLY_OWNER_PREFIX'
ctx=supply_disposition.context_at(c);rows=[list(row[:4]) for row in signed]
assert {{name:hashlib.sha256((Path(c['donor']['lean_path'])/name).read_bytes()).hexdigest() for name in {list(objects)!r}}}=={objects!r},'SUPPLY_PAID_OBJECTS_CHANGED'
intent={intent!r};value,scope,current,plan=own.donor.context(ctx,rows)
point=own._point(ctx,rows,intent,value,scope,current,plan)
assert point=={wanted!r},'SUPPLY_OWNER_POINT'
work.mkdir(parents=True,exist_ok=True);packet=work/'owner-packet.json'
reused=packet.exists()
if reused:
 result=json.loads(packet.read_text())
 assert result['point']==point and result['protocol']=={hashes!r},'SUPPLY_OWNER_SAVED_POINT'
else:
 key=app_private(Path({owner_profile!r}));permit=own.approve(ctx,rows,intent,key)
 receipt=sign(key,'original-donor-continuation-prepared',dict(point=digest(point),permission=digest(permit),
  prefix=prefix,protocol=digest({hashes!r}),native_objects={objects!r},
  boot=boot_identity(),pid=os.getpid(),birth=birth(os.getpid()),uid=os.getuid(),
  native_computations=0,journal_writes=0,economic_requests=0))
 result=dict(point=point,permission=permit,receipt=receipt,protocol={hashes!r},code=str(code))
 with packet.open('xb') as stream:stream.write(canonical(result))
assert verify(public_key(c['ha']['owners']['spark']),own.PERMIT,result['permission'])==point
assert source_readiness.snapshot(c)[2]==prefix,'SUPPLY_OWNER_PREFIX_MOVED'
print(json.dumps(dict(packet=result,reused=reused,available_bytes=space.f_bavail*space.f_frsize)))
'''
    deploy = transport()
    output = json.loads(deploy.execute('c', script, manifest, 90))
    packet = output['packet']
    owner_key = anchor.public_key(config['ha']['owners']['spark'])
    if (packet['point'] != wanted or packet['protocol'] != hashes or
            verify(owner_key, continuation.PERMIT, packet['permission']) != wanted):
        raise ValueError('SUPPLY_OWNER_RETURNED_POINT')
    receipt = verify(owner_key, 'original-donor-continuation-prepared', packet['receipt'])
    if (receipt['point'] != digest(wanted) or receipt['permission'] != digest(packet['permission']) or
            receipt['prefix'] != expected or receipt['protocol'] != revision or receipt['native_objects'] != objects or
            any(receipt[name] != 0 for name in ('native_computations', 'journal_writes', 'economic_requests'))):
        raise ValueError('SUPPLY_OWNER_RETURNED_RECEIPT')
    body = {**deepcopy(intent['body']), 'continuation': packet['permission']}
    actor = app_private(box/'service-pki/auditor1')
    request = sign(actor, donor.ACTION, body)
    event = dict(type=donor.ACTION, source=body['source'], stream=body['stream'], request=request,
                 peer=config['registry']['auditor1']['fingerprint'], scope=body['scope'])
    argument = donor.argument(supply_disposition.context_at(config), rows, event)
    if argument['commands'][-1] != intent['body']['command'] or len(argument['commands']) != body['index']+1:
        raise ValueError('SUPPLY_OWNER_SOURCE_CONTINUATION')
    once(work/'owner-packet.json', packet)
    once(work/'authorized-request.json', request)
    once(work/'authorized-source-input.json', argument)
    summary = dict(schema='actual90-original-owner-continuation/v1', checkpoint=CHECKPOINT,
        prefix=expected, permission=digest(packet['permission']), request=digest(request),
        request_id=body['request_id'], protocol=revision, native_objects=objects,
        native_preparations=0, native_computations=0, economic_requests=0, live_deployment=False)
    once(work/'owner-accepted.json', summary)
    print(json.dumps(dict(exit=0, owner='spark', prefix=expected, reused=output['reused'],
        original_request_preserved=body['request_id']==intent['body']['request_id'],
        reused_native_objects=len(objects), native_computations=0, economic_requests=0,
        receipt=str(work/'owner-accepted.json'))))


def stage(box, work):
    prepared = load(work/'prepared.json'); permission = load(work/'owner-packet.json')['permission']
    request = load(work/'authorized-request.json'); argument = load(work/'authorized-source-input.json')
    manifest = load(box/'ha/deployment.json'); payload, hashes = profile(manifest); revision = digest(hashes)
    if load(work/'protocol.json') != dict(checkpoint=CHECKPOINT, revision=revision, files=hashes):
        raise ValueError('SUPPLY_PROTOCOL_PROFILE_CHANGED')
    deploy = transport(); reports = {}
    for member in 'abcd':
        local = member == 'a'
        cfgpath = str(box/'local-anchor/config.json') if local else manifest['nodes'][member]['home']+'/config.json'
        code = (str(work/'code'/revision/'Verification/public-audit/network') if local else
                manifest['nodes'][member]['home']+'/code/'+revision+'/Verification/public-audit/network')
        remote_work = str(work/'local-readiness') if local else manifest['nodes'][member]['home']+'/supply-disposition/'+revision
        script = f'''import base64,hashlib,json,os,sys
from pathlib import Path
code=Path({code!r});cfgpath=Path({cfgpath!r});work=Path({remote_work!r})
space=os.statvfs(cfgpath.parent)
assert space.f_bavail*space.f_frsize>16*1024*1024,'SUPPLY_PROTOCOL_STORAGE'
for name,encoded in {payload!r}.items():
 p=code/name;raw=base64.b64decode(encoded);p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw,'SUPPLY_PROTOCOL_BYTES'
 else:
  with p.open('xb') as stream:stream.write(raw)
assert {{name:hashlib.sha256((code/name).read_bytes()).hexdigest() for name in {list(hashes)!r}}}=={hashes!r}
sys.path.insert(0,str(code))
import source_readiness,supply_disposition,donor_arrival_live as donor
from crypto import app_private,canonical,digest,sign,verify
from anchor import public_key
c=json.loads(cfgpath.read_text());member,rows,prefix=source_readiness.snapshot(c)
assert member=={member!r} and prefix=={prepared['prefix']!r},'SUPPLY_PROTOCOL_SOURCE_PREFIX'
ctx=supply_disposition.context_at(c);literal=[list(row[:4]) for row in rows];request={request!r}
body=request['body'];event=dict(type=donor.ACTION,source=body['source'],stream=body['stream'],request=request,
 peer=c['registry']['auditor1']['fingerprint'],scope=body['scope'])
actual=donor.argument(ctx,literal,event)
assert actual=={argument!r},'SUPPLY_PROTOCOL_SOURCE_INPUT'
objects={{name:hashlib.sha256((Path(c['donor']['lean_path'])/name).read_bytes()).hexdigest() for name in {list(prepared['reused_native_objects'])!r}}}
assert objects=={prepared['reused_native_objects']!r},'SUPPLY_PROTOCOL_PAID_OBJECTS'
point=dict(schema='original-supply-protocol-ready/v1',member=member,source=body['source'],stream=body['stream'],prefix=prefix,
 protocol={revision!r},request=digest(request),owner_permission=digest({permission!r}),source_input=digest(actual),
 source_program=digest(supply_disposition.program(ctx['donor'])),semantic_policy=c['semantic_policy'],native_objects=objects,
 native_preparations=0,native_computations=0,journal_writes=0,economic_requests=0)
work.mkdir(parents=True,exist_ok=True);path=work/'protocol-ready.json'
if path.exists():
 vote=json.loads(path.read_text());assert verify(public_key(c['registry']['anchor']),'original-supply-protocol-ready',vote)==point
else:
 vote=sign(app_private(Path(c['pki'])/'anchor'),'original-supply-protocol-ready',point)
 with path.open('xb') as stream:stream.write(canonical(vote))
assert source_readiness.snapshot(c)[2]==prefix,'SUPPLY_PROTOCOL_PREFIX_MOVED'
print(json.dumps(dict(vote=vote,code=str(code),config=str(cfgpath),home=str(work),available_bytes=space.f_bavail*space.f_frsize)))
'''
        item = json.loads(deploy.execute(member, script, manifest, 90))
        point = verify(anchor.public_key(manifest['trust']['members'][member]),
                       'original-supply-protocol-ready', item['vote'])
        if (point['member'] != member or point['prefix'] != prepared['prefix'] or point['protocol'] != revision or
                point['request'] != digest(request) or point['owner_permission'] != digest(permission) or
                point['source_input'] != digest(argument) or point['native_objects'] != prepared['reused_native_objects'] or
                any(point[name] != 0 for name in ('native_preparations', 'native_computations', 'journal_writes', 'economic_requests'))):
            raise ValueError('SUPPLY_PROTOCOL_VOTE_BINDING')
        saved = work/('protocol-ready-'+member+'.json')
        if saved.exists():
            original = load(saved)
            if ({k: v for k, v in original.items() if k != 'available_bytes'} !=
                    {k: v for k, v in item.items() if k != 'available_bytes'}):
                raise ValueError('SUPPLY_PROTOCOL_SAVED_VOTE_CHANGED')
            item = original
        once(saved, item)
        reports[member] = item
        print('ORIGINAL_PROTOCOL_STAGED', member, flush=True)
    common = [{key: value for key, value in report['vote']['body'].items() if key != 'member'} for report in reports.values()]
    if any(point != common[0] for point in common[1:]):
        raise ValueError('SUPPLY_PROTOCOL_SOURCE_FORK')
    once(work/'staged.json', dict(schema='actual90-supply-protocol-staged/v1', checkpoint=CHECKPOINT,
        protocol=revision, prefix=prepared['prefix'], nodes=reports, native_preparations=0,
        native_computations=0, economic_requests=0, installed=False))
    print(json.dumps(dict(exit=0, original_members=list(reports), native_preparations=0,
        native_computations=0, economic_requests=0, installed=False, receipt=str(work/'staged.json'))))


def check_prepared(box, work):
    """Independent literal-signature consumption; never invokes stage or approve."""
    manifest = load(box/'ha/deployment.json'); config = load(box/'local-anchor/config.json')
    prepared = load(work/'prepared.json'); packet = load(work/'owner-packet.json')
    request = load(work/'authorized-request.json'); intent = load(work/'intent.json')
    staged = load(work/'staged.json'); _, hashes = profile(manifest); revision = digest(hashes)
    _, signed, prefix = source_readiness.snapshot(config); rows = [list(row[:4]) for row in signed]
    if prefix != prepared['prefix'] or staged['protocol'] != revision:
        raise ValueError('SUPPLY_PREPARED_PREFIX')
    actor_key = anchor.public_key(config['registry']['auditor1'])
    body = verify(actor_key, donor.ACTION, request)
    original = verify(actor_key, donor.ACTION, intent)
    if body != {**original, 'continuation': packet['permission']}:
        raise ValueError('SUPPLY_PREPARED_ORIGINAL_REQUEST')
    context = supply_disposition.context_at(config)
    value, scope, current, plan = donor.context(context, rows)
    point = continuation._consume_at(context, rows, request, value, scope, current, plan)
    if point != packet['point'] or point != load(work/'owner-point.json'):
        raise ValueError('SUPPLY_PREPARED_PERMISSION')
    accepted = verify(anchor.public_key(config['ha']['owners']['spark']),
                      'original-donor-continuation-prepared', packet['receipt'])
    if accepted['point'] != digest(point) or accepted['permission'] != digest(packet['permission']) or accepted['protocol'] != revision:
        raise ValueError('SUPPLY_PREPARED_OWNER_RECEIPT')
    argument = load(work/'authorized-source-input.json'); common = None
    if set(staged['nodes']) != set('abcd'):
        raise ValueError('SUPPLY_PREPARED_FOUR_MEMBERS')
    for member, report in staged['nodes'].items():
        native = verify(anchor.public_key(manifest['trust']['members'][member]),
                        'original-supply-protocol-ready', report['vote'])
        if (native['member'] != member or native['prefix'] != prefix or native['protocol'] != revision or
                native['request'] != digest(request) or native['owner_permission'] != digest(packet['permission']) or
                native['source_input'] != digest(argument) or native['native_objects'] != prepared['reused_native_objects'] or
                any(native[name] != 0 for name in ('native_preparations', 'native_computations', 'journal_writes', 'economic_requests'))):
            raise ValueError('SUPPLY_PREPARED_NATIVE_BINDING')
        shared = {k: v for k, v in native.items() if k != 'member'}
        if common is not None and common != shared:
            raise ValueError('SUPPLY_PREPARED_NATIVE_FORK')
        common = shared
    controls = []
    from cryptography.exceptions import InvalidSignature
    for member in 'abcd':
        forged = deepcopy(staged['nodes'][member]['vote']); forged['body']['protocol'] = '0'*64
        try: verify(anchor.public_key(manifest['trust']['members'][member]), 'original-supply-protocol-ready', forged)
        except InvalidSignature: controls.append('forged-profile-'+member)
        else: raise ValueError('SUPPLY_PREPARED_FORGERY_ACCEPTED')
    modified = deepcopy(body); modified['request_id'] = 'another-original-request'
    changed = sign(app_private(box/'service-pki/auditor1'), donor.ACTION, modified)
    try: continuation._consume_at(context, rows, changed, value, scope, current, plan)
    except ValueError as problem:
        if str(problem) != 'DONOR_CONTINUATION_BINDING': raise
        controls.append('valid-actor-cannot-rebind-owner-permission')
    else: raise ValueError('SUPPLY_PREPARED_REQUEST_SUBSTITUTION')
    result = dict(schema='actual90-supply-preparation-independent/v1', verdict='accepted', prefix=prefix,
        owner='spark', original_request=digest(intent), authorized_request=digest(request),
        permission=digest(packet['permission']), native_members=list(staged['nodes']), protocol=revision,
        negative_controls=controls, rpc=0, native_preparations=0, native_computations=0,
        economic_requests=0, installed=False)
    once(work/'prepared-independent.json', result)
    print(json.dumps(result))


def check_paid_prefix(box, work):
    """Consume the four already paid producers and original fenced commits."""
    import donor_paid_prefix
    from cryptography.exceptions import InvalidSignature
    config = load(box/'local-anchor/config.json'); _, signed, prefix = source_readiness.snapshot(config)
    rows = [list(row[:4]) for row in signed]
    original = Path(load(work/'prepared.json')['prior_paid_work'])
    paid = Path('runtime/retained/iqa-actual77-donor-admission-20261106')
    proofs = {str(index): load(original/'actual'/('ha-proof-'+str(index)+'.json')) for index in range(78, 91)}
    reports = {}
    for member in 'abcd':
        consumer = deepcopy(config)
        consumer['registry']['anchor'] = consumer['ha']['trust']['members'][member]
        reports[member] = donor_paid_prefix.consume(consumer, rows, load(paid/('evidence-'+member+'.json')), proofs)
    if any(report != reports['a'] for report in reports.values()) or reports['a']['prefix'] != prefix:
        raise ValueError('SUPPLY_PAID_HISTORY_FORK')
    controls = []
    def refusal(name, action, reason=None):
        try:
            action()
        except (ValueError, InvalidSignature, KeyError) as problem:
            if reason is not None and str(problem) != reason:
                raise
            controls.append(name)
        else:
            raise ValueError('SUPPLY_PAID_HISTORY_NEGATIVE_ACCEPTED:'+name)
    evidence = load(paid/'evidence-a.json')
    changed = deepcopy(evidence); changed['output']['left']['output'][3]['next']['clock'] = '999999'
    refusal('changed-paid-native-output', lambda: donor_paid_prefix.consume(config, rows, changed, proofs),
            'PAID_PREFIX_NATIVE_PRODUCER')
    changed = deepcopy(evidence); changed['native']['objects'][next(iter(changed['native']['objects']))] = '0'*64
    refusal('changed-compiled-object', lambda: donor_paid_prefix.consume(config, rows, changed, proofs),
            'PAID_PREFIX_NATIVE_PRODUCER')
    changed = deepcopy(evidence); changed['rows'][-1].pop()
    refusal('deleted-original-custody-receipt', lambda: donor_paid_prefix.consume(config, rows, changed, proofs),
            'PAID_PREFIX_ORIGINAL_ROWS')
    refusal('other-producer-identity', lambda: donor_paid_prefix.consume(config, rows,
        load(paid/'evidence-b.json'), proofs), 'PAID_PREFIX_ORIGINAL_PRODUCER')
    refusal('incomplete-word-is-not-complete-prefix', lambda: donor_paid_prefix.consume(config, rows[:89], evidence, proofs),
            'PAID_PREFIX_INCOMPLETE_WORD')
    changed_proofs = deepcopy(proofs); changed_proofs['82'] = {k: v for k, v in list(proofs['82'].items())[:2]}
    refusal('missing-committed-quorum', lambda: donor_paid_prefix.consume(config, rows, evidence, changed_proofs),
            'PAID_PREFIX_COMMIT_QUORUM')
    changed_rows = deepcopy(rows); changed = json.loads(changed_rows[81][3])['body']
    changed['native']['next']['clock'] = '999999'
    changed_rows[81][3] = canonical(sign(app_private(box/'service-pki/server'), 'ledger', changed)).decode()
    for index in range(81, len(changed_rows)):
        changed_rows[index][1] = changed_rows[index-1][2]
        changed_rows[index][2] = anchor.ledger_hash(changed_rows[index][1], json.loads(changed_rows[index][3]))
    refusal('signed-writer-cannot-substitute-another-native-history',
        lambda: donor_paid_prefix.consume(config, changed_rows, evidence, proofs), 'PAID_PREFIX_ACTUAL_NATIVE_OUTPUT')
    future = donor_paid_prefix.consume(config, rows + [[91, prefix['head'], 'unexamined', '{}']], evidence, proofs)
    if future['prefix'] != prefix or future['new_commands_consumed'] != 0:
        raise ValueError('SUPPLY_PAID_HISTORY_FUTURE_PROMOTED')
    controls.append('future-command-is-not-in-the-paid-tape')
    result = dict(schema='actual90-paid-native-prefix-independent/v1', verdict='accepted', prefix=prefix,
        native_producers=list(reports), old_outputs=reports['a']['old_outputs'], donor_outputs=reports['a']['donor_outputs'],
        fenced_rows=len(reports['a']['fenced_commits']), negative_controls=controls,
        boundary=reports['a'], native_preparations=0, native_computations=0, rpc=0,
        economic_requests=0, source_view='post-donor historical consumer')
    once(work/'paid-prefix-independent.json', result)
    print(json.dumps(dict(exit=0, original_native_producers=list(reports), old_outputs=result['old_outputs'],
        donor_outputs=result['donor_outputs'], fenced_rows=result['fenced_rows'], controls=len(controls),
        native_preparations=0, native_computations=0, economic_requests=0,
        receipt=str(work/'paid-prefix-independent.json'))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=('owner', 'stage', 'check-prepared', 'check-paid-prefix'))
    parser.add_argument('--box', type=Path, default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    {'owner': owner, 'stage': stage, 'check-prepared': check_prepared,
     'check-paid-prefix': check_paid_prefix}[args.operation](args.box.resolve(), args.work.resolve())


if __name__ == '__main__':
    main()

"""Independent, read-only audit of the paid physical coordinator failover."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import ledger_hash, public_key
from crypto import APP_KEY, digest, verify
from cryptography import x509
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from exercise import replay
from ha_anchor import verify_quorum
from ha_client import exchange
from ha_quorum import Quorum
from recovery_loop import birth, boot_identity, save
from service import Store


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    result = importlib.util.module_from_spec(spec); spec.loader.exec_module(result)
    return result


transport = module('ha_transport', 'public-ha-deploy.py')
original_check = module('original_recovery_consumer', 'public-recovery-check.py')


def require(value, message):
    if not value:
        raise RuntimeError(message)


def load(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rpc_key(config, member):
    certificate = x509.load_pem_x509_certificate((Path(config['anchors']['endpoints'][member]['pki'])/'server/cert.pem').read_bytes())
    return Ed25519PublicKey.from_public_bytes(certificate.extensions.get_extension_for_oid(APP_KEY).value.value)


QUERIES = {
    'rows': 'SELECT id,previous,hash,message FROM events ORDER BY id',
    'keys': 'SELECT actor,fingerprint,public FROM keys ORDER BY actor',
    'used': 'SELECT nonce,request_id,actor,seq FROM used ORDER BY actor,seq',
    'sequences': 'SELECT actor,seq FROM sequences ORDER BY actor',
    'receipts': 'SELECT seq,receipt FROM anchor_receipts ORDER BY seq',
}


def database(path):
    db = sqlite3.connect(path.resolve().as_uri()+'?mode=ro', uri=True)
    try:
        return {name: db.execute(query).fetchall() for name, query in QUERIES.items()}
    finally:
        db.close()


def collect(box, manifest):
    result = {}
    retired = {}
    scenario = box/'ha/alternating-01'
    if (scenario/'spark-execution-killed.json').exists():
        killed = load(scenario/'spark-execution-killed.json')
        retired = {'backend':killed['backend'],'anchor':killed['anchor'],
                   'service':load(scenario/'spark-executor-before.json')['coordinator']['body']['service']}
    for member in 'bcd':
        item = manifest['nodes'][member]
        # Charge the added immutable library view and its four launcher paths.
        timing_entries = (sum(1 for _ in (box.parent/'privacy/network-accepted-03/lib').rglob('*'))+4
                          if manifest.get('public_timing') and member == 'c' else 0)
        code = f'''import hashlib,json,sqlite3,sys,os,stat,time,subprocess
from pathlib import Path
p=Path({item['home']!r});c=Path({item['code']!r});sys.path.insert(0,str(c))
from recovery_loop import boot_identity,birth
d=sqlite3.connect((p/'journal.sqlite').as_uri()+'?mode=ro',uri=True)
v={{'rows':d.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall(),
 'binding':d.execute('SELECT value FROM binding').fetchall(),
 'ha_binding':d.execute('SELECT value FROM ha_binding').fetchall(),
 'terms':d.execute('SELECT stream,epoch,owner,lease_id,boot,deadline FROM ha_terms').fetchall(),
 'proofs':d.execute('SELECT seq,payload FROM ha_proofs JOIN ha_events ON ha_proofs.event=ha_events.id ORDER BY seq').fetchall(),
 'status':json.loads((p/'status.json').read_text()),'boot':boot_identity(),
 'protocol':{{n:hashlib.sha256((c/n).read_bytes()).hexdigest() for n in {list(item['protocol'])!r}}},
 'config':json.loads((p/'config.json').read_text()),'private_anchor_on_node':(p/'pki/anchor/app.key').is_file()}};d.close()
if {bool(manifest.get('semantic'))!r}:
 d=sqlite3.connect((p/'journal.sqlite').as_uri()+'?mode=ro',uri=True)
 v['intents']=d.execute('SELECT seq,previous,hash,message FROM ha_intents ORDER BY seq').fetchall()
 v['rejected']=d.execute('SELECT seq,hash,message,proof FROM ha_rejected_intents ORDER BY seq,hash').fetchall()
 v['superseded']=d.execute('SELECT seq,hash,message,proof FROM ha_superseded_intents ORDER BY seq,hash').fetchall();d.close()
size=0;apparent=0;inodes=set();count=0;start=time.monotonic()
for directory,dirs,files in os.walk(p,followlinks=False):
 for name in dirs+files:
  f=Path(directory)/name;s=f.lstat();count+=1
  assert count<{15000+(5210 if manifest.get('governance') and member in 'bc' else 0)+(5212 if manifest.get('energy') and member in 'bc' else 0)+(5214 if manifest.get('continuation') and member in 'bc' else 0)+(5216 if manifest.get('handoff') and member in 'bc' else 0)+timing_entries} and time.monotonic()-start<10,'owned inventory budget exceeded'
  assert not stat.S_ISLNK(s.st_mode),'unexpected link in owned runtime'
  if stat.S_ISREG(s.st_mode):
   apparent+=s.st_size
   # The native readers share immutable artifacts through verified hard links.
   identity=(s.st_dev,s.st_ino)
   if identity not in inodes:size+=s.st_size;inodes.add(identity)
v['inventory']={{'complete':True,'entries':count,'bytes':size,'apparent_bytes':apparent,'regular_inodes':len(inodes)}}
if {member!r}=='c':
 h=p/'ha';r=h/'runtime';v['coordinator']=json.loads((r/'ha-status.json').read_text())
 v['controller_config']=json.loads((h/'controller.json').read_text());v['service_config']=json.loads((h/'service.json').read_text())
 v['ready']=json.loads((h/'standby/ha-service-ready.json').read_text())
 db=sqlite3.connect((h/'standby/service.sqlite').as_uri()+'?mode=ro',uri=True)
 v['service_database']={{n:db.execute(q).fetchall() for n,q in {QUERIES!r}.items()}};db.close()
 closure=json.loads((h/'lean/closure.json').read_text())
 v['source_sha256']=hashlib.sha256((h/'lean/public-scoped-audit-source.lean').read_bytes()).hexdigest()
 v['runtime_sha256']=hashlib.sha256((h/'lean/lib/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/Runtime.olean').read_bytes()).hexdigest()
 v['closure_count']=len(closure);v['closure_verified']=all(hashlib.sha256((h/'lean/lib'/n).read_bytes()).hexdigest()==w for n,w in closure.items())
 state=v['coordinator']['body'];v['coordinator_alive']=birth(state['pid'])==state['birth']
 v['service_alive']=birth(v['ready']['body']['pid'])==v['ready']['body']['birth']
 backend=v['ready']['body'].get('backend');v['backend_alive']=bool(backend and birth(backend['pid'])==backend['birth'])
 v['backend_pgid']=os.getpgid(backend['pid']) if v['backend_alive'] else None
 v['retired_alive']={{n:birth(r['pid'])==r['birth'] for n,r in {retired!r}.items()}}
 v['source_unit']=subprocess.check_output(['systemctl','is-active','homework-public-source-ha.service'],text=True).strip()
 v['source_unit_command']=subprocess.check_output(['systemctl','show','homework-public-source-ha.service','-p','ExecStart','--value'],text=True).strip()
 v['auditor_private_keys_present']=any((h/'service-pki'/n/'app.key').exists() for n in ('auditor1','auditor2','rotated2'))
print(json.dumps(v))
'''
        result[member] = json.loads(transport.remote(member, code, timeout=60, python=item['python']))
    db = sqlite3.connect((box/'local-anchor/journal.sqlite').as_uri()+'?mode=ro', uri=True)
    try:
        result['a'] = {'rows': db.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall(),
                       'proofs': db.execute('SELECT seq,payload FROM ha_proofs JOIN ha_events ON ha_proofs.event=ha_events.id ORDER BY seq').fetchall()}
        if manifest.get('semantic'):
            result['a'].update(intents=db.execute('SELECT seq,previous,hash,message FROM ha_intents ORDER BY seq').fetchall(),
                rejected=db.execute('SELECT seq,hash,message,proof FROM ha_rejected_intents ORDER BY seq,hash').fetchall(),
                superseded=db.execute('SELECT seq,hash,message,proof FROM ha_superseded_intents ORDER BY seq,hash').fetchall())
    finally:
        db.close()
    save(box/'ha/current-independent.json', result)
    return result


def status(manifest, owner, signed):
    body = verify(public_key(manifest['owners'][owner]), 'ha-coordinator', signed)
    require(body['owner'] == owner and body['source'] == manifest['source'] and body['stream'] == 'recovery',
            'coordinator signed scope differs')
    return body


def check_fault(box, manifest, config, literal):
    witness = box/'ha/actual-01'; before = load(witness/'before.json')
    old = status(manifest, 'mac', before['mac']); standby = status(manifest, 'spark', before['spark'])
    takeover = status(manifest, 'spark', load(witness/'takeover.json'))
    returned = status(manifest, 'mac', load(witness/'returned.json'))
    require(old['phase'] == 'leader' and old['head']['seq'] == 7 and
            standby['phase'] == 'standby' and standby['service'] is None, 'preexisting primary/standby differs')
    require(all(standby[k] == takeover[k] for k in ('pid','birth','boot')) and
            takeover['phase'] == 'leader' and takeover['head']['seq'] == 8 and not takeover['members'],
            'takeover used a newly launched or Mac-dependent coordinator')
    require([vote['member'] for vote in takeover['grant']['votes']] == list('bcd') and
            takeover['grant']['point']['epoch'] > old['grant']['point']['epoch'], 'takeover not granted by surviving machines')
    ha_config = {'ha': {'trust': manifest['trust']}}
    for grant in (old['grant'], takeover['grant']):
        verify_quorum(ha_config, grant, 'ha-grant', grant['point'])
    boundary = verify(public_key(config['registry']['server']), 'ha-fault-boundary', load(witness/'boundary.json'))
    require(boundary['phase'] == 'after-source' and boundary['seq'] == 8 and
            boundary['grant']['point'] == old['grant']['point'] and boundary['owner'] == 'mac' and
            boundary['message'] == json.loads(literal[7][3]) and boundary['previous'] == literal[7][1],
            'source-advanced/pre-commit boundary differs from original eighth event')
    intent_point = dict(token=old['grant']['point'], seq=8, previous=literal[7][1], head=literal[7][2],
                        message=digest(boundary['message']), operation_id=boundary['message']['body']['request']['body']['request_id'])
    verify_quorum(ha_config, boundary['intent'], 'ha-intent', intent_point)
    verify_quorum(ha_config, boundary['grant'], 'ha-grant', old['grant']['point'])
    require(load(witness/'pending.json') == {k: boundary[k] for k in ('seq','previous','message')} and
            load(witness/'unknown.json') == {'error': 'OUTCOME_UNKNOWN', 'request': boundary['message']['body']['request']},
            'uncertain result replaced or lost the original request')
    isolated = load(witness/'isolated.json')
    require(isolated['coordinator'] == old and set(isolated['groups']) == {'a','b','c','d','service'},
            'injected domain omitted a coordinator dependency')
    for entry in isolated['groups'].values():
        require(entry['pid'] == entry['pgid'] and entry['boot'] == before['boot'], 'fault targeted an unowned process domain')
    require(boundary['at'] >= old['at'] and boundary['birth'] and boundary['pid'] > 0,
            'source fault did not follow the original leader')
    for name, row in [('recovered', literal[7]), ('next', literal[8])]:
        received = load(witness/(name+'.json')); response = received['response']
        require(received['tls'] == 'TLSv1.3' and response['ledger'] == json.loads(row[3]) and
                response['event'] == response['ledger']['body'], 'original TLS/source result differs')
        request = response['ledger']['body']['request']
        require(response['request'] == digest(request) and response['request_id'] == request['body']['request_id'],
                'lookup changed original request identity')
        original_check.certificate(config, response['anchor'], original_check.point(config, row))
    require(json.loads(literal[7][3])['body']['record']['labor'] == '2' and
            json.loads(literal[8][3])['body']['record']['access'] == 'unfunded' and
            json.loads(literal[8][3])['body']['record']['labor'] == '0', 'actual original payment/typed next differs')
    refusals = load(witness/'stale-writer-refusals.json')
    require(set(refusals) == set('abcd'), 'missing stale-writer rejection')
    for member, exchange_record in refusals.items():
        request = exchange_record['request']; body = verify(rpc_key(config, member), 'anchor-request', request)
        owner_body = {key: value for key,value in body.items() if key != 'owner_proof'}
        require(verify(public_key(manifest['owners']['mac']), 'ha-owner-request', body['owner_proof']) == {'request': digest(owner_body)},
                'stale writer was not the authenticated original owner')
        response = verify(public_key(manifest['trust']['members'][member]), 'anchor-response', exchange_record['response'])
        require(body['op'] == 'append' and body['grant'] == old['grant'] and body['seq'] == 8 and
                body['message'] == boundary['message'] and response['request'] == digest(request) and
                response['nonce'] == body['nonce'] and response['error'] == 'HA_FENCED',
                'old writer failed for a reason other than durable fencing')
    require(returned['phase'] == 'standby' and returned['service'] is None and returned['head']['seq'] == 9 and
            returned['boot'] == before['boot'] == boot_identity() and not Path(config['database']+'.pending.json').exists(),
            'returning Mac did not catch up as a nonwriter')
    print('ACTUAL FAILOVER PASS: preexisting Spark; b/c/d takeover; exact uncertain event8; all 4 old-writer fences; Mac follower9', flush=True)


def check_overlap(box, manifest):
    path = box/'ha/overlap-01'; before = load(path/'before.json')
    old = status(manifest, 'spark', before['spark']); prior_mac = status(manifest, 'mac', before['mac'])
    new = status(manifest, 'mac', load(path/'takeover.json'))
    returned = status(manifest, 'spark', load(path/'returned.json'))
    evidence = load(path/'minority-renewals.json'); grant = evidence['grant']
    verify_quorum({'ha': {'trust': manifest['trust']}}, grant, 'ha-grant', old['grant']['point'])
    require(evidence['members'] == list('cd') and len(evidence['rounds']) >= 25 and
            all(new[k] == prior_mac[k] for k in ('pid','birth','boot')) and new['phase'] == 'leader' and
            new['grant']['point']['epoch'] > grant['point']['epoch'] and new['head'] == old['head'] and
            returned['phase'] == 'standby' and returned['service'] is None and returned['head'] == old['head'] and
            returned['boot'] == old['boot'], 'overlap partition did not autonomously hand over unchanged history')
    verify_quorum({'ha': {'trust': manifest['trust']}}, new['grant'], 'ha-grant', new['grant']['point'])
    for member in 'cd':
        deadlines = set(); refused = False; nonces = set()
        for row in evidence['rounds']:
            exchange_record = row['exchanges'][member]
            body = verify(rpc_key(manifest['mac']['service'], member), 'anchor-request', exchange_record['request'])
            stripped = {k:v for k,v in body.items() if k != 'owner_proof'}
            require(verify(public_key(manifest['owners']['spark']), 'ha-owner-request', body['owner_proof']) == {'request': digest(stripped)} and
                    body['op'] == 'ha-grant' and body['renewal'] == grant and body['owner'] == 'spark', 'minority renewal request differs')
            require(body['nonce'] not in nonces, 'a cached exchange was reused as a new physical renewal')
            nonces.add(body['nonce'])
            response = verify(public_key(manifest['trust']['members'][member]), 'anchor-response', exchange_record['response'])
            require(response['nonce'] == body['nonce'] and response['request'] == digest(exchange_record['request']), 'renewal freshness differs')
            if 'error' in response:
                require(response['error'] in {'HA_FENCED','HA_LEASE_BUSY'}, 'unexpected minority refusal')
                refused = True
            else:
                vote = verify(public_key(manifest['trust']['members'][member]), 'ha-grant', response['result'])
                require(vote['point'] == grant['point'], 'renewal changed original token')
                deadlines.add(vote['deadline_ns'])
        require(len(deadlines) == 1 and refused, 'a minority repeatedly extended its lease or escaped fencing')
    print('PHYSICAL OVERLAP PASS: repeated authenticated c/d minority renewals stop extending; preexisting Mac takes over9; Spark returns nonwriter', flush=True)


def check_current(box, manifest, config, local, remote):
    literal = local['rows']; trust = manifest['trust']; old = load(box/'physical-independent.json')
    for member, snapshot in remote.items():
        require([tuple(row[:4]) for row in snapshot['rows']] == literal, 'physical full journal differs: '+member)
        key = public_key(trust['members'][member])
        for row in snapshot['rows']:
            require(verify(key, 'anchor-commit', json.loads(row[4])) == original_check.point(config, row[:4]),
                    'physical original signature differs: '+member)
        proofs = dict(snapshot['proofs'])
        require(set(proofs) == set(range(8,len(literal)+1)), 'new HA proof inventory differs: '+member)
        for seq, text in proofs.items():
            proof = verify(key, 'ha-event', json.loads(text)); row = literal[seq-1]
            require(proof['operation'] == 'append' and proof['source'] == config['source'] and
                    proof['point']['seq'] == seq and proof['point']['head'] == row[2] and
                    proof['point']['message'] == digest(json.loads(row[3])) and
                    proof['point']['operation_id'] == json.loads(row[3])['body']['request']['body']['request_id'],
                    'HA proof is not the committed original event')
            verify_quorum({'ha': {'trust': trust}}, proof['grant'], 'ha-grant', proof['point']['token'])
            verify_quorum({'ha': {'trust': trust}}, proof['intent'], 'ha-intent', proof['point'])
            require(verify(key, 'anchor-commit', proof['receipt']) == original_check.point(config, row), 'HA proof commit differs')
        if member == 'a':
            continue
        item = manifest['nodes'][member]
        now = verify(key, 'recovery-host-status', snapshot['status'])
        prior = verify(key, 'recovery-host-status', old[member]['status'])
        same_boot=now['boot']==prior['boot']==snapshot['boot']
        if member=='b' and manifest.get('governance') and not same_boot:
            same_boot=(now['boot']==snapshot['boot'] and
                       snapshot['windows_boot_unix']<prior['at'])
        expected_mode = ('ha_public_timing_native_spare_v1' if manifest.get('public_timing') else
                         'ha_fenced_native_spare_v1' if manifest.get('native_admission') else 'ha_fenced_v1')
        require(same_boot and now['source'] == config['source'] and
                now['mode'] == expected_mode and -2 < time.time()-now['at'] < 90, 'remote physical boot/service differs')
        require(snapshot['protocol'] == item['protocol'] == {n: sha(NETWORK/n) for n in item['protocol']}, 'installed bytes differ: '+member)
        expected = {'ha': snapshot['config']['ha'], 'cluster': digest(trust), 'streams': snapshot['config']['streams']}
        require(snapshot['ha_binding'] == [[json.dumps(expected,sort_keys=True,separators=(',',':'))]], 'HA identity/membership binding differs')
        require(snapshot['config']['ha']['owners'] == manifest['owners'] and snapshot['config']['ha']['trust'] == trust and
                snapshot['private_anchor_on_node'] and not (Path(config['anchors']['endpoints'][member]['pki'])/'anchor/app.key').exists(),
                'remote signing key ownership differs')
        budget=(4 if member=='c' and manifest.get('governance') else
                3 if member=='c' or member in manifest.get('semantic',{}).get('native_members','') else 1)
        require(snapshot['inventory']['complete'] and snapshot['inventory']['bytes'] < budget*(1<<30),
                'owned active runtime inventory incomplete or over budget')
    spark = remote['c']; spark_state = status(manifest, 'spark', spark['coordinator'])
    mac = status(manifest, 'mac', load(box/'runtime/ha-status.json'))
    states = {'mac': mac, 'spark': spark_state}
    leaders = [value for value in states.values() if value['phase'] == 'leader']
    require(len(leaders) == 1, 'multiple or missing current leaders')
    leader = leaders[0]; follower = states['spark' if leader['owner'] == 'mac' else 'mac']
    require(spark['coordinator_alive'] and leader['head']['seq'] == len(literal) and follower['phase'] == 'standby' and
            follower['service'] is None and follower['head']['seq'] == len(literal) and
            birth(mac['pid']) == mac['birth'] and -2 < time.time()-mac['at'] < 30, 'current live leader/follower differs')
    ready = verify(public_key(config['registry']['server']), 'ha-service-ready', spark['ready'])
    require(ready['boot'] == spark_state['boot'] and
            spark['controller_config'] == manifest['spark']['controller'] and not spark['controller_config'].get('members') and
            spark['source_unit'] == 'active' and manifest['nodes']['c']['code']+('/live_timing.py' if manifest.get('public_timing') else '/ha_coordinator.py') in spark['source_unit_command'],
            'Spark source does not have independent native ownership')
    if leader['owner'] == 'spark':
        require(spark['service_alive'] and spark['backend_alive'] and spark['backend_pgid']==leader['service']['pgid'] and
                ready['grant']['point'] == leader['grant']['point'], 'Spark source not alive under current grant')
    else:
        current_ready = verify(public_key(config['registry']['server']), 'ha-service-ready', load(box/'ha-service-ready.json'))
        require(current_ready['grant']['point'] == leader['grant']['point'] and
                birth(current_ready['pid']) == current_ready['birth'] and
                birth(current_ready['backend']['pid']) == current_ready['backend']['birth'] and
                os.getpgid(current_ready['backend']['pid']) == leader['service']['pgid'], 'Mac source not alive under current grant')
    require(spark['source_sha256'] == sha(ROOT/'Lean/scripts/verification/public-scoped-audit-source.lean') and
            spark['runtime_sha256'] == '88fa0dee28d5b1444d0833e95ff99977bf7ea2690f20f556bdb25ad7afb712fc' and
            spark['closure_count'] == 5205 and spark['closure_verified'] and not spark['auditor_private_keys_present'],
            'same native source closure or restricted credentials differs')
    if (box/'ha/alternating-01').exists():
        retired_mac=load(box/'ha/alternating-01/mac-executor-before.json')['body']
        require(not spark['retired_alive'].get('backend',True) and not spark['retired_alive'].get('service',True) and
                not spark['retired_alive'].get('anchor',True) and
                birth(retired_mac['pid'])!=retired_mac['birth'] and
                birth(retired_mac['backend']['pid'])!=retired_mac['backend']['birth'], 'a crashed executor survived as a duplicate')
    source = spark['service_database']
    for name in ('rows','keys','used','sequences'):
        require([tuple(row) for row in source[name]] == local[name], 'Spark original state table differs: '+name)
    for seq, text in source['receipts']:
        original_check.certificate(config, json.loads(text), original_check.point(config, literal[seq-1]))
    q = Quorum(manifest['mac']['service']); states = q.collect('status')
    require(set(states) == set('abcd') and all(s['head'] == leader['head'] and
            all(s[k] == leader['grant']['point'][k] for k in ('epoch','owner','lease_id')) and
            s['remaining_ns'] > 0 for s in states.values()), 'current four-anchor head/holder differs')
    # Lookup is authenticated against the live successor and cannot advance or pay.
    request = json.loads(literal[7][3])['body']['request']; addresses = load(box/'ha/addresses.json')
    lookup = exchange(Path(config['pki'])/'auditor2', config['source'], addresses['c' if leader['owner']=='spark' else 'a'], config['port'], {}, lookup=request)
    require(lookup['response']['ledger'] == json.loads(literal[7][3]) and database(Path(config['database'])) == local,
            'live recovery lookup changed ledger/payment state')
    save(box/'ha/current-lookup.json', lookup)
    print('LIVE FOUR-MACHINE PASS: '+str(4*len(literal))+' exact signed rows; HA grant/intent/commit proofs; '+leader['owner']+' leader; other candidate nonwriter; no reboot', flush=True)


def run(box, full, check_main):
    manifest = load(box/'ha/deployment.json'); config = load(box/'service.json')
    if manifest.get('donor'):
        work=Path(manifest['donor']['evidence'])
        paid=Path(load(work/'paid-work.json')['directory'])
        try:module('current_source_donor','public-donor-live-audit.py').final(box,work,paid,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('arrival'):
        try:module('current_source_arrival','public-arrival-live-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('productive'):
        try:module('current_productive_supply','public-productive-live-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('material'):
        try:module('current_material_supply','public-material-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('regeneration'):
        try:module('current_public_supply','public-supply-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('continuous_epochs'):
        try:module('current_public_continuation','public-continuous-check.py').audit(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('handoff'):
        try:module('current_distinct_handoff','public-handoff-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('continuation'):
        try:module('current_energy_continuation','public-continuation-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('energy'):
        try:module('current_energy_epoch','public-energy-check.py').run(box,full,check_main)
        finally:
            import governance,energy
            governance.close_readers();energy.close_readers()
        return
    if manifest.get('governance'):
        module('current_native_governance','public-governance-check.py').run(box,full,check_main)
        return
    baseline = load(box/'ha/baseline.json'); local = database(Path(config['database'])); literal = local['rows']
    require(len(literal) >= 9 and config == baseline['service'] and literal[:7] == [tuple(row) for row in baseline['rows']] and
            database(box/'ha/baseline-service.sqlite')['rows'] == literal[:7], 'original seven-event baseline changed')
    validator = object.__new__(Store); validator.config = config
    class PublicSigner:
        def public_key(self): return public_key(config['registry']['server'])
    validator.key = PublicSigner(); validator.database = sqlite3.connect(Path(config['database']).as_uri()+'?mode=ro', uri=True)
    validator.anchor = object()
    try:
        validator.validate_ledger(); validator.validate_anchor_receipts()
    finally:
        validator.database.close()
    observations, head = replay(config, config['registry'])
    require(len(observations) == len(literal) and sum(int(r['labor']) for r in observations) == 14 and head == literal[-1][2],
            'canonical original source/payment replay differs')
    print('ORIGINAL SOURCE/PAYMENT PASS: '+str(len(literal))+' events; total labor14; event8 paid once; next9 typed unfunded/labor0; every original QC verified', flush=True)
    check_fault(box, manifest, config, literal)
    check_overlap(box, manifest)
    if (box/'ha/alternating-01').exists():
        module('alternating_independent', 'public-ha-alternating-check.py').check(box,manifest,config,literal[:13])
    current = collect(box, manifest); check_current(box, manifest, config, local, current)
    semantic=None
    if manifest.get('semantic'):
        semantic=module('semantic_independent','public-semantic-check.py').check(box,manifest,config,literal,current)
    if full:
        result = subprocess.run([sys.executable, str(Path(__file__).with_name('public-distributed-audit.py')), '--verify-only', '--check-main'],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (box/'ha/original-full-audit.log').write_text(result.stdout)
        require(result.returncode == 0, 'original full audit failed: '+result.stdout[-2000:])
        print('ORIGINAL SIX/FULL COST PASS: seven literal routes; scoped evidence; quorum audit; prior four-machine end-to-end replay', flush=True)
    files = ['Verification/public-audit/network/'+name for name in
             ('ha_anchor.py','ha_quorum.py','ha_service.py','ha_host.py','ha_coordinator.py','ha_client.py')]
    files += ['Lean/scripts/verification/'+name for name in
              ('public-ha-local.py','public-ha-deploy.py','public-ha-actual.py','public-ha-overlap.py','public-ha-check.py',
               'public-ha-alternating.py','public-ha-alternating-check.py')]
    if semantic:
        files += ['Verification/public-audit/network/'+name for name in ('source_semantics.py','semantic_anchor.py')]
        files += ['Lean/scripts/verification/'+name for name in ('public-semantic-prepare.py','public-semantic-materialize.py',
                  'public-semantic-deploy.py','public-semantic-actual.py','public-semantic-local.py','public-semantic-check.py','public-semantic-orphan.py')]
    inputs = {name: sha(ROOT/name) for name in files}
    if check_main:
        for name, wanted in inputs.items():
            require(hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+name], cwd=ROOT)).hexdigest() == wanted,
                    'main differs: '+name)
        print('HA MAIN INTEGRATION PASS', flush=True)
    witnesses = {p.name: sha(p) for p in (box/'ha/actual-01').glob('*.json')}
    scenarios = {name:{p.name:sha(p) for p in (box/'ha'/name).glob('*.json')}
                 for name in ('actual-01','overlap-01','alternating-01') if (box/'ha'/name).exists()}
    save(box/'ha/final-check.json', {'exit': 0, 'inputs': inputs, 'witnesses': witnesses,
         'scenarios':scenarios,
         'semantic':semantic,
         'source_events': len(literal), 'labor': 14, 'replica_rows': {m: len(v['rows']) for m,v in current.items()},
         'head': head, 'physical_host_reboots': 0, 'main_verified': check_main,
         'original_full_audit': sha(box/'ha/original-full-audit.log') if full else None, 'at': time.time()})
    print('INDEPENDENT PHYSICAL COORDINATOR FAILOVER AUDIT ACCEPTED', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('box', type=Path)
    parser.add_argument('--full', action='store_true'); parser.add_argument('--check-main', action='store_true')
    args = parser.parse_args(); run(args.box.resolve(), args.full, args.check_main)

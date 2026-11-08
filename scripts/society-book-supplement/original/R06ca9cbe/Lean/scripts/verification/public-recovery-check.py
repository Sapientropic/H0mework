"""Independently replay paid recovery witnesses without new service actions."""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT / 'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import ledger_hash, public_key
from client import exchange
from crypto import digest, verify
from exercise import replay
from recovery_loop import Loop, birth, boot_identity, save


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def load(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path, table):
    database = sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)
    try:
        return database.execute(table).fetchall()
    finally:
        database.close()


def point(config, row):
    seq, previous, head, text = row
    return dict(source=config['source'], stream=config['stream'], seq=seq,
                previous=previous, head=head, message=digest(json.loads(text)),
                cluster=digest(config['anchors']['trust']))


def certificate(config, signed, expected):
    trust = config['anchors']['trust']
    require(set(signed) == {'kind', 'cluster', 'body', 'votes'} and
            signed['kind'] == 'anchor-quorum' and signed['cluster'] == digest(trust)
            and signed['body'] == expected, 'quorum scope or exact event differs')
    votes = signed['votes']; names = [vote['member'] for vote in votes]
    require(3 <= len(names) <= 4 and names == sorted(set(names)), 'missing or duplicate quorum vote')
    for vote in votes:
        require(verify(public_key(trust['members'][vote['member']]), 'anchor-commit', vote['receipt'])
                == expected, 'original quorum signature differs')


def check_isolation(box, config, literal):
    key = public_key(config['registry']['server'])
    baseline = load(box/'isolation-baseline.json')
    require([tuple(row) for row in baseline['rows']] == literal[:5], 'original five-event prefix changed')
    intent = load(box/'isolation-pending.json')
    boundary = verify(key, 'recovery-fault-boundary', load(box/'fault-boundary.json'))
    expected = point(config, literal[5])
    require(intent == {name: boundary[name] for name in ('seq', 'previous', 'message')} and
            intent == {'seq': 6, 'previous': literal[5][1], 'message': json.loads(literal[5][3])},
            'pending identity is not original committed event six')
    certificate(config, boundary['receipt'], expected)
    request = intent['message']['body']['request']
    unknown = load(box/'isolation-unknown.json')
    require(unknown == {'error': 'OUTCOME_UNKNOWN', 'request': request}, 'uncertain outcome lost exact request')
    restored = load(box/'isolation-recovered.json')['response']
    require(restored['ledger'] == intent['message'] and restored['event'] == intent['message']['body']
            and restored['request'] == digest(request) and restored['request_id'] == request['body']['request_id'],
            'recovery generated a replacement request')
    certificate(config, restored['anchor'], expected)
    following = load(box/'isolation-next.json')['response']
    require(following['ledger'] == json.loads(literal[6][3]) and literal[6][1] == literal[5][2],
            'own next is not the original successor')
    certificate(config, following['anchor'], point(config, literal[6]))
    blocked = verify(key, 'recovery-status', load(box/'cold-isolated-status.json'))
    killed = load(box/'cold-start-groups.json')
    require(blocked['phase'] == 'blocked' and blocked['unavailable'] == list('bcd') and
            blocked['members']['a'] == {name: expected[name] for name in ('source', 'stream', 'seq', 'head')}
            and all('error' in blocked['members'][name] for name in 'bcd') and
            blocked['processes']['service'] is None and 'QUORUM_UNAVAILABLE' in blocked['error'],
            'cold isolation blocked for a different reason or exposed a service')
    require(blocked['owner'] != killed['owner'] and
            set(killed['groups']) == {'service', 'member-a', 'member-b', 'member-c', 'member-d'},
            'owned application domain was not cold-started')
    for name, record in killed['groups'].items():
        require(record['boot'] == baseline['boot'] and record['pid'] == record['pgid'], 'cold-start group owner differs')
        require(not (birth(record['pid']) == record['birth']), 'old application group remains alive')
        replacement = blocked['processes']['a' if name == 'member-a' else name.removeprefix('member-')]
        if replacement:
            require(replacement['pid'] != record['pid'], 'cold start adopted a killed process')
    cuts = load(box/'isolated-links.json'); gates = load(box/'isolation-gates.json')
    require(set(gates) == set('bcd') and cuts['a']['seq'] == 6 and
            all('error' in cuts[name] and gates[name]['refused'] > 0 for name in 'bcd'), 'remote links were not cut')
    require(boot_identity() == baseline['boot'], 'coordinator physical boot changed')
    policy = load(box/'reboot-policy.json')
    require(policy['physical_host_reboot_allowed'] is False and policy['executed'] is False,
            'host reboot policy changed')


def check_process_recovery(box, config, literal):
    key = public_key(config['registry']['server'])
    transitions = []
    for line in (box/'runtime/events.jsonl').read_text().splitlines():
        body = verify(key, 'recovery-event', json.loads(line))
        require(body['source'] == config['source'] and body['stream'] == config['stream'],
                'recovery lifecycle event changed original scope')
        transitions.append(body)
    require(any(row['kind'] == 'state-changed' and row['phase'] == 'blocked' for row in transitions) and
            any(row['kind'] == 'state-changed' and row['phase'] == 'ready' for row in transitions) and
            any(row['kind'] == 'process-rebuilt' and row['member'] == 'c' for row in transitions) and
            any(row['kind'] == 'service-rebuilt' for row in transitions), 'missing signed recovery transitions')
    spark = load(box/'spark-process-recovery.json')
    identity = public_key(config['anchors']['trust']['members']['c'])
    before = verify(identity, 'recovery-host-status', spark['before'])
    after = verify(identity, 'recovery-host-status', spark['after'])
    require(before['boot'] == after['boot'] and before['process']['pid'] != after['process']['pid'] and
            before['source'] == after['source'] == config['source'], 'remote owned anchor was not rebuilt')
    manager = load(box/'systemd-recovery.json')
    require(manager['before_pid'] and manager['after_pid'] and manager['before_pid'] != manager['after_pid'],
            'native service manager did not replace the node supervisor')
    responses = load(box/'physical-responses.json')
    require(len(responses) == 5 and all(value['response']['ledger'] == json.loads(row[3])
            for value, row in zip(responses, literal[:5])), 'physical recovery changed the original first five events')


def collect(box, config):
    spec = importlib.util.spec_from_file_location('paid_physical_recovery', Path(__file__).with_name('public-recovery-physical.py'))
    physical = importlib.util.module_from_spec(spec); spec.loader.exec_module(physical)
    deployed = load(box/'deployment.json'); result = {}
    for member in 'bcd':
        item = deployed['nodes'][member]
        code = f"""import hashlib,json,sqlite3,subprocess,os,stat,time
from pathlib import Path
p=Path({item['home']!r});c=Path({item['code']!r})
d=sqlite3.connect('file:'+str(p/'journal.sqlite')+'?mode=ro',uri=True)
v={{'rows':d.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall(),
    'binding':d.execute('SELECT value FROM binding').fetchall(),
    'status':json.loads((p/'status.json').read_text()),
    'protocol':{{n:hashlib.sha256((c/n).read_bytes()).hexdigest() for n in {list(item['protocol'])!r}}}}};d.close()
v['registry']=json.loads((p/'config.json').read_text())['registry']
v['private_anchor_on_node']=(p/'pki/anchor/app.key').is_file()
if {member!r}=='b':v['wsl_address']=json.loads(subprocess.check_output(['ip','-json','route','get','1.1.1.1']))[0]['prefsrc']
total=0;entries=0;start=time.monotonic()
for directory,dirs,files in os.walk(p,followlinks=False):
 for name in dirs+files:
  info=(Path(directory)/name).lstat();entries+=1
  assert entries<10000 and time.monotonic()-start<5,'owned inventory budget exceeded'
  assert not stat.S_ISLNK(info.st_mode) and (stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode)),'uninspected owned file'
  if stat.S_ISREG(info.st_mode):total+=info.st_size
v['owned_inventory']={{'complete':True,'entries':entries,'apparent_bytes':total}}
compatibility={item.get('compatibility_home')!r}
if compatibility:
 q=Path(compatibility);v['compatibility_link']={{'is_symlink':q.is_symlink(),'exact_target':q.resolve()==p.resolve()}}
print(json.dumps(v))
"""
        result[member] = json.loads(physical.python(physical.remote(member), code))
    save(box/'current-independent.json', result)
    return result


def check_replicas(box, config, literal, current):
    trust = config['anchors']['trust']; cluster = digest(trust)
    old = load(box/'physical-independent.json'); isolated = load(box/'isolation-independent.json')
    deployment = load(box/'deployment.json')
    require(trust['threshold'] == 3 and trust['version'] == 1 and set(trust['members']) == set('abcd'),
            'original fixed membership changed')
    require(len({entry['app'] for entry in trust['members'].values()}) == 4, 'anchor keys are shared')
    require(len({sha(Path(endpoint['pki'])/'ca.pem') for endpoint in config['anchors']['endpoints'].values()}) == 4,
            'physical anchors share a TLS issuer')
    local = rows(box/'local-anchor/journal.sqlite', 'SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq')
    replicas = {'a': {'rows': local}, **current}
    for member, value in replicas.items():
        require([tuple(row[:4]) for row in value['rows']] == literal, 'full physical journal differs: ' + member)
        identity = public_key(trust['members'][member])
        for row in value['rows']:
            require(verify(identity, 'anchor-commit', json.loads(row[4])) == point(config, row[:4]),
                    'stored original replica signature differs: ' + member)
        if member == 'a':
            continue
        before = verify(identity, 'recovery-host-status', old[member]['status'])
        during = verify(identity, 'recovery-host-status', isolated[member]['status'])
        now = verify(identity, 'recovery-host-status', value['status'])
        require(before['boot'] == during['boot'] == now['boot'] and now['source'] == config['source']
                and now['cluster'] == cluster and -2 < time.time() - now['at'] < 30,
                'physical node boot, scope or freshness differs: ' + member)
        require([tuple(row[:4]) for row in old[member]['rows']] == literal[:5] and
                [tuple(row[:4]) for row in isolated[member]['rows']] == literal, 'paid snapshots differ')
        require(value['protocol'] == deployment['nodes'][member]['protocol'] ==
                {name: sha(NETWORK/name) for name in value['protocol']}, 'installed source differs: ' + member)
        binding = json.loads(value['binding'][0][0])
        require(len(value['binding']) == 1 and binding['cluster'] == cluster and
                binding['identity'] == trust['members'][member] and
                binding['streams'] == {'recovery': {'source': config['source'], 'writer': config['registry']['server']}},
                'node journal writer/source binding differs')
        require(all(value['registry'][name] == config['registry'][name] for name in config['registry']),
                'node lost original auditor identity')
        require(value['private_anchor_on_node'] and not
                (Path(config['anchors']['endpoints'][member]['pki'])/'anchor/app.key').exists(),
                'anchor signing key not retained on its own node')
        require(value['owned_inventory']['complete'] and value['owned_inventory']['apparent_bytes'] < 1 << 30,
                'owned continuous service inventory incomplete or over budget')
        if member == 'd':
            require(value['compatibility_link'] == {'is_symlink': True, 'exact_target': True},
                    'Studio compatibility link changed target')
    if (box/'dynamic-tunnel-recovery.json').exists():
        rebuilt = load(box/'dynamic-tunnel-recovery.json'); resolution = rebuilt['resolution']
        require(rebuilt['before']['pid'] != rebuilt['after']['pid'] and
                rebuilt['before']['boot'] == rebuilt['after']['boot'] == boot_identity() and
                resolution['owner_monitor'] == rebuilt['after']['pid'] and
                resolution['address'] == current['b']['wsl_address'] and
                any(str(NETWORK/'recovery_tunnel.py') == part for part in rebuilt['after']['argv']),
                'owned WSL tunnel was not rebuilt from current guarded address')
    return {member: len(value['rows']) for member, value in replicas.items()}


def configuration_controls(box, config, loop):
    # Construct only: no start(), source action, tunnel or remote mutation.
    with tempfile.TemporaryDirectory(dir=box.parent, prefix='configuration-') as temporary:
        root = Path(temporary); service = root/'service.json'; save(service, config)
        cfg = {**loop, 'state': str(root/'default'), 'service': str(service)}
        probe = Loop(cfg)
        require(Path(probe.service.argv[1]) == NETWORK/'recovery_service.py', 'default runner changed')
        probe.lock.close(); del probe
        save(service, {**config, 'port': config['port'] + 1})
        try:
            Loop(cfg)
        except ValueError as error:
            require(str(error) == 'RECOVERY_OWNER_CONFIGURATION_CHANGED', 'different configuration failure')
        else:
            raise RuntimeError('service content drift was silently admitted')
        save(service, config)
        for label, runner in [('explicit', NETWORK/'recovery_fault_service.py'), ('missing', root/'recovery_service.py')]:
            override = {**cfg, 'state': str(root/label), 'service_entrypoint': str(runner)}
            try:
                probe = Loop(override)
            except ValueError as error:
                require(label == 'missing' and str(error) == 'RECOVERY_SERVICE_RUNNER_MISSING', 'runner near-miss failure')
            else:
                require(label == 'explicit' and Path(probe.service.argv[1]) == runner, 'implicit fallback accepted missing runner')
                probe.lock.close(); del probe
    from recovery_tunnel import destination
    class Route:
        def __init__(self):
            self.values = iter(['192.0.2.10', '192.0.2.11'])
        def wsl(self, command, timeout, allow_probe):
            require(command == 'ip -json route get 1.1.1.1\n' and not allow_probe, 'address query bypasses transport guard')
            return json.dumps([{'prefsrc': next(self.values)}])
    route = Route()
    require(destination(route) == '192.0.2.10' and destination(route) == '192.0.2.11',
            'WSL address discovery reused a stale address')


def run(box, full, check_main):
    config = load(box/'service.json'); loop = load(box/'loop.json')
    literal = rows(Path(config['database']), 'SELECT id,previous,hash,message FROM events ORDER BY id')
    baseline = load(box/'isolation-baseline.json')
    original_loop = baseline['loop']
    if loop != original_loop:
        transition = verify(public_key(config['registry']['server']), 'recovery-configuration', load(box/'dynamic-tunnel-configuration.json'))
        require(transition['before'] == original_loop and transition['after'] == loop,
                'unrecorded operational configuration change')
        allowed = copy.deepcopy(loop)
        allowed['members']['b']['command'] = original_loop['members']['b']['command']
        require(allowed == original_loop, 'configuration transition changed more than the WSL tunnel launcher')
    require(len(literal) == 7 and config == baseline['service'] and 'service_entrypoint' not in loop,
            'normal production configuration or exact history changed')
    before = '0'*64
    key = public_key(config['registry']['server'])
    for row in literal:
        event = verify(key, 'ledger', json.loads(row[3]))
        require(row[0] == literal.index(row)+1 and row[1] == before and ledger_hash(before, json.loads(row[3])) == row[2]
                and event['source'] == config['source'] and event['stream'] == config['stream'], 'original source chain differs')
        before = row[2]
    certs = rows(Path(config['database']), 'SELECT seq,receipt FROM anchor_receipts ORDER BY seq')
    require(len(certs) == len(literal), 'missing original service commit receipt')
    for (seq, text), row in zip(certs, literal):
        require(seq == row[0], 'service certificate order differs'); certificate(config, json.loads(text), point(config, row))
    observations, head = replay(config, config['registry'])
    require(len(observations) == 7 and sum(int(record['labor']) for record in observations) == 12 and head == before,
            'independent canonical source replay or complete payment differs')
    print('RECOVERY SOURCE PASS: 7 genuine events; labor 12; canonical source and every original QC replayed', flush=True)
    check_isolation(box, config, literal)
    check_process_recovery(box, config, literal)
    print('UNCERTAIN COMMIT PASS: exact pending/QC6; all 3 links isolated; cold owner blocked; same request recovered; own next7', flush=True)
    replica_counts = check_replicas(box, config, literal, collect(box, config))
    print('PHYSICAL RECOVERY PASS: 4 original journals; 28 exact rows; deployed bytes match; 0 physical reboots', flush=True)
    configuration_controls(box, config, loop)
    state = verify(key, 'recovery-status', load(box/'runtime/status.json'))
    require(state['phase'] == 'ready' and not state['unavailable'] and state['head']['head'] == head and
            state['configuration'] == digest({'loop': loop, 'service': config}) and
            -2 < time.time()-state['at'] < 15 and birth(state['owner']['pid']) == state['owner']['birth'],
            'normal continuous production service is not ready')
    request = json.loads(literal[5][3])['body']['request']
    lookup = exchange(Path(config['pki'])/'auditor2', config['port'], config['source'], {},
                      lookup=request, expected_stream='recovery')
    require(lookup['response']['ledger'] == json.loads(literal[5][3]) and
            rows(Path(config['database']), 'SELECT id,previous,hash,message FROM events ORDER BY id') == literal,
            'normal runner lookup changed original source or charged again')
    print('CONTINUOUS SERVICE PASS: original normal runner ready on all 4 anchors; exact lookup; binding/default/override controls', flush=True)
    files = ['Verification/public-audit/network/'+name for name in
             ('recovery_loop.py', 'recovery_host.py', 'recovery_service.py', 'recovery_tunnel.py', 'recovery_fault_service.py')]
    files += ['Lean/scripts/verification/'+name for name in
              ('public-recovery-audit.py', 'public-recovery-deploy.py', 'public-recovery-physical.py',
               'public-recovery-isolation.py', 'public-recovery-check.py')]
    inputs = {name: sha(ROOT/name) for name in files}
    if full:
        result = subprocess.run([sys.executable, str(Path(__file__).with_name('public-distributed-audit.py')),
                                 '--verify-only', '--check-main'], cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        (box/'original-full-audit.log').write_text(result.stdout)
        require(result.returncode == 0, 'original full-chain audit failed: ' + result.stdout[-2000:])
        print('ORIGINAL FULL CHAIN PASS: seven literal routes, complete rent/cost bound, scoped audit and physical anchor audit', flush=True)
    if check_main:
        for name, wanted in inputs.items():
            require(hashlib.sha256(subprocess.check_output(['git', 'show', 'refs/heads/main:'+name], cwd=ROOT)).hexdigest()
                    == wanted, 'main differs: '+name)
        print('RECOVERY MAIN INTEGRATION PASS', flush=True)
    save(box/'final-check.json', {'exit': 0, 'inputs': inputs, 'source_events': 7, 'labor': 12,
          'replica_rows': replica_counts, 'head': head, 'physical_host_reboots': 0,
          'original_full_audit': sha(box/'original-full-audit.log') if full else None,
          'main_verified': check_main, 'at': time.time(),
          'scope': 'fixed physical hosts and membership; task-owned cold start, isolated data links, exact-event reconciliation'})
    print('INDEPENDENT CONTINUOUS RECOVERY AUDIT ACCEPTED', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--check-main', action='store_true')
    args = parser.parse_args(); run(args.box.resolve(), args.full, args.check_main)

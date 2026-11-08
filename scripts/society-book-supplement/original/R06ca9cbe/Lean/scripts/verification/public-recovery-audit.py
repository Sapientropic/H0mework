"""Actual original-service recovery, supervised children and exact paid replay."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import socket
import sqlite3
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT / 'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import Journal, ledger_hash, public_key
from client import exchange
from crypto import create_pki, digest, verify
from exercise import replay
from quorum import membership
from recovery_loop import OwnedProcess, birth, save


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def port():
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        return sock.getsockname()[1]


def wait(box, predicate, seconds=90):
    cfg = json.loads((box / 'service.json').read_text())
    loop = json.loads((box / 'loop.json').read_text())
    identity = digest({'loop': loop, 'service': cfg})
    key = public_key(cfg['registry']['server'])
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        try:
            status = verify(key, 'recovery-status', json.loads((box / 'runtime/status.json').read_text()))
            if (time.time() - status['at'] < 8 and status['configuration'] == identity
                    and birth(status['owner']['pid']) == status['owner']['birth'] and predicate(status)):
                return status
        except (FileNotFoundError, json.JSONDecodeError):
            pass
        time.sleep(.2)
    raise TimeoutError('recovery did not reach the required signed state; inspect retained runtime logs')


def setup(box):
    box.mkdir(parents=True)
    pki = box / 'service-pki'
    registry = create_pki(pki)
    source = json.loads((ROOT / '.agents/tmp/public-quorum-audit-20261102/actual-04/receipt.json').read_text())['source']
    trust = {'version': 1, 'threshold': 3, 'members': {}}
    members, endpoints, configs = {}, {}, {}
    for name in 'abcd':
        keys = box / ('anchor-' + name + '-pki')
        reg = create_pki(keys, anchor=True)
        trust['members'][name] = reg['anchor']
        configs[name] = {'pki': str(keys), 'registry': {**registry, 'anchor': reg['anchor']},
                         'transport_writer': reg['server'], 'database': str(box / (name + '.sqlite')),
                         'port': port(), 'streams': {'recovery': {'source': source, 'writer': registry['server']}}}
        endpoints[name] = {'host': '127.0.0.1', 'hostname': 'anchor.local', 'port': configs[name]['port'], 'pki': str(keys)}
    for name, config in configs.items():
        config['cluster'] = membership(trust)
        save(box / (name + '-config.json'), config)
        journal = Journal(config, True)
        journal.db.close()
        members[name] = {'command': [sys.executable, str(NETWORK / 'challenge_anchor.py'), str(box / (name + '-config.json'))]}
    for label in ['auditor1', 'auditor2']:
        save(pki / label / 'anchors.json', trust)
        save(pki / label / 'stream.json', 'recovery')
    config = {'pki': str(pki), 'source': source, 'stream': 'recovery', 'registry': registry,
              'anchors': {'trust': trust, 'endpoints': endpoints}, 'port': port(),
              'database': str(box / 'service.sqlite'), 'lean': str(ROOT / 'Lean'),
              'backend_error': str(box / 'source.log'),
              'backend': ['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', '-DElab.async=false', '-j1',
                          '--run', 'scripts/verification/public-scoped-audit-source.lean', 'private-one']}
    save(box / 'service.json', config)
    save(box / 'loop.json', {'state': str(box / 'runtime'), 'service': str(box / 'service.json'), 'members': members, 'interval': 1})
    return config


def run(box):
    config = setup(box)
    runtime = box / 'runtime'
    command = [sys.executable, '-u', str(NETWORK / 'recovery_loop.py'), str(box / 'loop.json')]
    log = (box / 'loop.log').open('a')
    loop = subprocess.Popen(command, stdout=log, stderr=log, start_new_session=True)
    tests, results = [], []
    def passed(name):
        tests.append(name)
        save(box / 'tests.json', tests)
        print('PASS ' + name, flush=True)
    def request():
        actor = 1 if len(results) < 2 else 2
        result = exchange(Path(config['pki']) / ('auditor' + str(actor)), config['port'], config['source'],
                          {'slots': 63, 'fields': 3}, expected_stream='recovery')
        require('response' in result, 'original service did not return: ' + str(result.get('error')))
        results.append(result)
        save(box / 'responses.json', results)
        return result
    def kill(name):
        record = json.loads((runtime / (name + '-process.json')).read_text())
        os.killpg(record['pid'], signal.SIGKILL)
        return record['pid']
    try:
        wait(box, lambda x: x['phase'] == 'ready')
        first = request()
        passed('original_Lean_service_generated_and_three_anchor_committed')
        former = kill('member-c')
        wait(box, lambda x: x['phase'] == 'ready' and not x['unavailable'] and
             x['processes']['c']['pid'] != former)
        request()
        passed('anchor_process_detected_rebuilt_and_exactly_reconciled')
        former = kill('service')
        wait(box, lambda x: x['phase'] == 'ready' and
             x['processes']['service']['pid'] != former)
        recovered = exchange(Path(config['pki']) / 'auditor1', config['port'], config['source'], {},
                             lookup=first['request'], expected_stream='recovery')
        require(recovered['response']['ledger'] == first['response']['ledger'], 'recovery changed original committed event')
        request()
        passed('service_and_Lean_backend_rebuilt_original_lookup_without_repayment')
        duplicate = subprocess.run(command, capture_output=True, text=True, timeout=10)
        require(duplicate.returncode != 0 and 'RECOVERY_OWNER_ALREADY_ACTIVE' in duplicate.stderr, 'second recovery owner acquired the writer')
        passed('duplicate_supervisor_refused')
        children = {name: json.loads((runtime / (name + '-process.json')).read_text())['pid']
                    for name in ['service', 'member-a', 'member-b', 'member-c', 'member-d']}
        os.kill(loop.pid, signal.SIGKILL)
        loop.wait(timeout=10)
        request()  # No supervisor is available to perform this source action.
        passed('management_coordinator_process_absent_original_service_continues')
        loop = subprocess.Popen(command, stdout=log, stderr=log, start_new_session=True)
        wait(box, lambda x: x['phase'] == 'ready' and x['owner']['pid'] == loop.pid)
        require(all(json.loads((runtime / (name + '-process.json')).read_text())['pid'] == pid for name, pid in children.items()),
                'coordinator recovery duplicated or replaced a healthy owner process')
        request()
        passed('restarted_coordinator_adopts_exact_process_births_without_duplicate_writer')
    finally:
        runtime.mkdir(exist_ok=True)
        (runtime / 'STOP').touch()
        if loop.poll() is None:
            loop.wait(timeout=60)
        log.close()
    observed, head = replay(config, config['registry'])
    require(len(observed) == len(results) == 5, 'new source event count differs')
    previous = '0' * 64
    database = sqlite3.connect(config['database'])
    literal = database.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
    database.close()
    for index, before, hashed, text in literal:
        event = json.loads(text)
        verify(public_key(config['registry']['server']), 'ledger', event)
        require(before == previous and ledger_hash(before, event) == hashed, 'source chain changed')
        previous = hashed
    for name in 'abcd':
        database = sqlite3.connect(box / (name + '.sqlite'))
        external = database.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall()
        database.close()
        require([row[:4] for row in external] == literal, 'recovery lost an exact original source event')
        for index, before, hashed, text, receipt in external:
            point = verify(public_key(config['anchors']['trust']['members'][name]), 'anchor-commit', json.loads(receipt))
            require(point['seq'] == index and point['head'] == hashed and point['message'] == digest(json.loads(text)), 'node receipt mismatch')
    for line in (runtime / 'events.jsonl').read_text().splitlines():
        verify(public_key(config['registry']['server']), 'recovery-event', json.loads(line))
    passed('independent_original_source_replay_four_full_journals_and_signed_recovery_events')
    save(box / 'acceptance.json', {'tests': tests, 'new_source_events': len(results), 'head': head,
                                 'labor': sum(int(x['labor']) for x in observed),
                                 'scope': 'local-process actual; no physical-host reboot or host failover claimed'})
    print('ORIGINAL SERVICE RECOVERY ACTUAL PASS: 7/7; 5 new original source events; no duplicate payment', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    args = parser.parse_args()
    run(args.box.resolve())

"""Task-isolated physical Journal calls, authenticated by SSH and original owner proofs.

This control transport is separate from the unchanged production mTLS service.
Every vote and commit still comes from the original Journal implementation.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import sys
import time


def main(code, original_home, case, operation, value, member):
    sys.path.insert(0, str(code))
    import anchor
    from crypto import app_private, canonical, create_pki, digest, sign
    from native_spare import Journal
    from quorum import membership
    from recovery_loop import birth, boot_identity, save
    import energy
    import governance
    import semantic_anchor
    from source_semantics import Engine
    case.mkdir(parents=True, exist_ok=True)
    original = json.loads((original_home/'config.json').read_text())
    if operation == 'identity':
        path = case/'identity.json'
        if not path.exists():
            save(path, create_pki(case/'pki', anchor=True))
        return json.loads(path.read_text())['anchor']
    if operation == 'seed':
        identity = json.loads((case/'identity.json').read_text())
        cfg = copy.deepcopy(original)
        cfg.update(pki=str(case/'pki'), database=str(case/'journal.sqlite'),
                   cluster=membership(value['trust']), transport_writer=identity['server'],
                   governance_members=list('abc'))
        cfg['registry']['anchor'] = identity['anchor']
        cfg['ha'] = {**original['ha'], 'trust': value['trust'], 'lease_seconds': 60}
        cfg.pop('native_admission', None)
        cfg['semantic'].update(background_warmup=False, warm_on_start=False, error_log=str(case/'source.log'), replay_seconds=180)
        with sqlite3.connect(Path(original['database']).as_uri()+'?mode=ro', uri=True) as db:
            prefix = db.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? AND seq<=24 ORDER BY seq', ('recovery',)).fetchall()
        assert len(prefix) == 24 and prefix[-1][2] == value['point']['prefix']['head']
        path = Path(cfg['database'])
        # Historical source comparisons retain their original signing domain;
        # the fresh replication cluster governs only the new test journals.
        seed_config = copy.deepcopy(cfg)
        seed_config['ha']['trust'] = original['ha']['trust']
        seeded = anchor.Journal(seed_config, not path.exists())
        try:
            present = seeded.head('recovery')['seq']
            for seq, previous, head, text in prefix[present:]:
                seeded.execute(dict(op='append', source=cfg['streams']['recovery']['source'], stream='recovery',
                                    seq=seq, previous=previous, head=head, message=json.loads(text)))
            seed = seeded.db.execute('SELECT seq,previous,hash,message,receipt FROM entries ORDER BY seq').fetchall()
        finally:
            seeded.db.close()
        save(case/'config.json', cfg)
        journal = semantic_anchor.Journal(cfg)
        try:
            journal.engine.sync(prefix, deadline=time.monotonic()+180)
            status = journal.engine.status()
            ready = sign(journal.key, 'native-source-ready', {
                'point': value['point'], 'member': member, 'compiler': cfg['semantic']['descriptor']['compiler'],
                'backend': status['backend'], 'at': time.time()})
        finally:
            journal.engine.close()
            governance.close_readers()
            energy.close_readers()
            journal.db.close()
        return {'ready': ready, 'entries': seed}
    cfg = json.loads((case/'config.json').read_text())
    if operation == 'admit':
        cfg.update(governance_members=list('abcd'), native_admission=value)
        save(case/'config.json', cfg)
    if operation == 'isolate':
        save(case/'isolated.json', {'isolated': value})
    key = app_private(case/'pki/anchor')
    started = time.monotonic_ns()
    journal = None
    try:
        isolated = (case/'isolated.json').exists() and json.loads((case/'isolated.json').read_text())['isolated']
        if operation == 'call' and isolated:
            raise ValueError('TASK_NODE_ISOLATED')
        journal = Journal(cfg)
        if operation == 'call':
            result = journal.execute_request(value)
        elif operation in {'admit', 'isolate', 'snapshot'}:
            result = {'head': journal.head('recovery')}
        else:
            raise ValueError('TASK_OPERATION')
        answer = {'result': result}
    except Exception as problem:
        answer = {'error': str(problem), 'error_type': type(problem).__name__}
    finally:
        database = sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro', uri=True)
        tables = {name: database.execute('SELECT * FROM '+name+' ORDER BY rowid').fetchall()
                  for name in ('entries', 'ha_intents', 'ha_proofs', 'ha_governance_policy', 'ha_energy_policy',
                               'ha_continuation_policy', 'ha_handoff_policy', 'native_admission')
                  if database.execute('SELECT name FROM sqlite_master WHERE type="table" AND name=?', (name,)).fetchone()}
        database.close()
        backend = journal.engine.status() if journal else None
        if journal:
            journal.stop_warming.set()
            journal.engine.close()
            governance.close_readers()
            energy.close_readers()
            journal.db.close()
    return sign(key, 'native-spare-rpc', {
        'operation': operation, 'input': value, 'member': member, 'answer': answer, 'tables': tables,
        'source': cfg['semantic']['descriptor'], 'source_status': backend,
        'configuration': digest(cfg), 'started_ns': started, 'finished_ns': time.monotonic_ns(),
        'process': {'pid': os.getpid(), 'birth': birth(os.getpid()), 'boot': boot_identity()},
        'helper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'journal_sha256': hashlib.sha256((code/'native_spare.py').read_bytes()).hexdigest()})

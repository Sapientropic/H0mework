"""Restore the current donor writer from its original paid source history."""
import json
import os
from pathlib import Path

from crypto import canonical, digest, sign
import donor_arrival_live as donor
from donor_source_view import Engine
import governance
import ha_timing
import service
from productive_owner_request import history
from recovery_loop import birth, boot_identity, save
from verify import verify_disclosure


def validate_tables(config, database, engine):
    rows = governance.rows_of(database)
    engine.sync(rows)
    keys, sequences, _ = history(config, rows)
    prior_keys = {config['registry'][name]['actor']: config['registry'][name] for name in ('auditor1', 'auditor2')}
    used = set()
    import arrival_extension, arrival_regeneration, continuation, energy, handoff
    import material_extension, material_regeneration, productive_extension, productive_regeneration
    import regeneration, source_extension
    commands = {
        'native-response': governance, 'energy-renewal': energy, 'energy-audit': energy,
        'energy-continuation': continuation, 'energy-handoff': handoff,
        'energy-regeneration': regeneration, 'energy-material': material_regeneration,
        'energy-productive': productive_regeneration, 'energy-arrival': arrival_regeneration,
        donor.ACTION: donor}
    controls = {'source-extension': source_extension, 'material-extension': material_extension,
                'productive-extension': productive_extension, 'arrival-extension': arrival_extension}
    for index, row in enumerate(rows):
        event = json.loads(row[3])['body']; request = event['request']; body = request['body']
        governance.registration_bound(event)
        actor = body['actor']; kind = event['type']; prefix = rows[:index]
        if body.get('stream') != config['stream']:
            raise ValueError('RESTORE_STREAM')
        used.add((body['nonce'], body['request_id'], actor, body['seq']))
        if kind == 'rotation':
            prior_keys[actor] = event['new']
            continue
        if event['peer'] != prior_keys[actor]['fingerprint']:
            raise ValueError('RESTORE_MEMBER_CERTIFICATE')
        if kind == 'disclosure' and request['kind'] == 'audit':
            record = event['record']
            if (record['actor'] != int(actor) or record['version'] != body['epoch'] or
                    record['cut'] != body['cut'] or record['query'] != body['query']):
                raise ValueError('RESTORE_SCOPE')
            verify_disclosure(record)
            if 'registration' in event:
                governance.expected(config, prefix, event, native=False)
        elif request['kind'] != kind:
            raise ValueError('RESTORE_EVENT_KIND')
        elif kind in commands:
            commands[kind].expected(config, prefix, event, native=False)
        elif kind in controls:
            controls[kind].expected(config, prefix, event)
        elif kind == donor.CONTROL:
            donor.expected(config, prefix, event, native=False)
        else:
            raise ValueError('RESTORE_EVENT_KIND')
    expected_keys = {(actor, value['fingerprint'], value['app']) for actor, value in keys.items()}
    if (set(database.execute('SELECT actor,fingerprint,public FROM keys')) != expected_keys or
            dict(database.execute('SELECT actor,seq FROM sequences')) != sequences or
            set(database.execute('SELECT nonce,request_id,actor,seq FROM used')) != used):
        raise ValueError('RESTORE_STATE_TABLES')


class Store(ha_timing.Store):
    def validate_ledger(self):
        if not hasattr(self, 'donor_view'):
            self.donor_view = Engine(self.config)
        validate_tables(self.config, self.database, self.donor_view)

    def restore_source(self):
        # The old Backend is not a donor state carrier. The active donor state
        # is reconstructed by context from this validated, committed history.
        self.donor_view.sync(governance.rows_of(self.database))

    def check_event(self, rows, event, phase):
        boundary = self.config['donor_history']['prefix']
        if phase == 'restore' and len(rows) < boundary['seq']:
            actual = self.database.execute('SELECT message FROM events WHERE id=?', (len(rows)+1,)).fetchone()
            if actual is None or canonical(json.loads(actual[0])['body']) != canonical(event):
                raise ValueError('DONOR_RESTORE_EVENT_CHANGED')
            return self.donor_view.boundary
        return super().check_event(rows, event, phase)

    def __init__(self, config):
        try:
            super().__init__(config)
        except BaseException:
            if hasattr(self, 'donor_view'):
                self.donor_view.close()
            raise
        try:
            if self.public_worker.call({'mode': 'source-extension', 'native': {'warm': 'public'}}) != {'warm': 'public'}:
                raise ValueError('DONOR_PUBLIC_WORKER_WARMUP')
            value = canonical(config['donor_history']).decode()
            self.database.execute('CREATE TABLE IF NOT EXISTS donor_history_binding(value TEXT NOT NULL UNIQUE)')
            prior = self.database.execute('SELECT value FROM donor_history_binding').fetchall()
            if not prior:
                self.database.execute('INSERT INTO donor_history_binding VALUES(?)', (value,))
            elif prior != [(value,)]:
                raise ValueError('DONOR_HISTORY_BINDING_CHANGED')
            self.restoration = sign(self.key, 'paid-donor-public-restore', dict(
                source=config['source'], stream=config['stream'], prefix=config['donor_history']['prefix'],
                current=dict(seq=self.donor_view.count, head=self.donor_view.head),
                history=digest(governance.rows_of(self.database)), view=config['donor_history'],
                consumed=self.donor_view.boundary, boot=boot_identity(), pid=os.getpid(),
                birth=birth(os.getpid()), native_preparations=0, historical_native_replays=0,
                economic_requests=0))
            save(Path(config['database']+'.paid-history.json'), self.restoration)
        except BaseException:
            self.close()
            raise

    def close(self):
        try:
            super().close()
        finally:
            if hasattr(self, 'donor_view'):
                self.donor_view.close()


class FollowStore(service.Store):
    """The original follower uses the same historical consumer, without IPC."""
    validate_ledger = Store.validate_ledger
    restore_source = Store.restore_source

"""Explicit HA journal: durable fencing and intent precede the original CAS."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import signal
import time

import anchor
from challenge_anchor import Handler
from crypto import canonical, digest, sign, tls_context, verify
from recovery_loop import boot_identity


def token(config, body):
    return {name: body[name] for name in ('epoch', 'owner', 'lease_id')} | {
        'source': body['source'], 'stream': body['stream'], 'cluster': config['cluster']}


def verify_quorum(config, certificate, kind, expected):
    trust = config['ha']['trust']
    if certificate['kind'] != kind+'-quorum' or certificate['point'] != expected:
        raise ValueError('HA_CERTIFICATE_BINDING')
    names = [vote['member'] for vote in certificate['votes']]
    if not 3 <= len(names) <= 4 or names != sorted(set(names)):
        raise ValueError('HA_CERTIFICATE_QUORUM')
    for vote in certificate['votes']:
        body = verify(anchor.public_key(trust['members'][vote['member']]), kind, vote['receipt'])
        if body['point'] != expected:
            raise ValueError('HA_CERTIFICATE_VOTE')


class Journal(anchor.Journal):
    def __init__(self, config):
        super().__init__(config)
        if digest(config['ha']['trust']) != config['cluster'] or set(config['ha']['owners']) != {'mac', 'spark'}:
            raise ValueError('HA_FIXED_MEMBERSHIP')
        if not 1 <= config['ha']['lease_seconds'] <= 60:
            raise ValueError('HA_LEASE_DURATION')
        self.db.executescript('''
          CREATE TABLE IF NOT EXISTS ha_binding(value TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS ha_terms(stream TEXT PRIMARY KEY,epoch INTEGER,owner TEXT,lease_id TEXT,boot TEXT,deadline INTEGER);
          CREATE TABLE IF NOT EXISTS ha_intents(stream TEXT,seq INTEGER,previous TEXT,hash TEXT,message TEXT,
            PRIMARY KEY(stream,seq));
          CREATE TABLE IF NOT EXISTS ha_events(id INTEGER PRIMARY KEY,payload TEXT);
          CREATE TABLE IF NOT EXISTS ha_proofs(stream TEXT,seq INTEGER,event INTEGER,PRIMARY KEY(stream,seq));
          CREATE TABLE IF NOT EXISTS ha_semantic_policy(value TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS ha_rejected_intents(stream TEXT,seq INTEGER,hash TEXT,message TEXT,proof TEXT,
            PRIMARY KEY(stream,seq,hash));
          CREATE TABLE IF NOT EXISTS ha_superseded_intents(stream TEXT,seq INTEGER,hash TEXT,message TEXT,proof TEXT,
            PRIMARY KEY(stream,seq,hash));
        ''')
        policy=config.get('semantic_policy')
        if policy:
            if (policy['source']!=next(iter(config['streams'].values()))['source'] or
                    set(config['streams'])!={policy['stream']}):raise ValueError('HA_SEMANTIC_POLICY_SOURCE')
            prior=self.db.execute('SELECT value FROM ha_semantic_policy').fetchall();value=canonical(policy).decode()
            if not prior:self.db.execute('INSERT INTO ha_semantic_policy VALUES(?)',(value,))
            elif prior!=[(value,)]:raise ValueError('HA_SEMANTIC_POLICY_CHANGED')
        value = canonical({'ha': config['ha'], 'cluster': config['cluster'], 'streams': config['streams']}).decode()
        prior = self.db.execute('SELECT value FROM ha_binding').fetchall()
        if not prior:
            self.db.execute('INSERT INTO ha_binding VALUES(?)', (value,))
            for stream in config['streams']:
                self.db.execute('INSERT INTO ha_terms VALUES(?,0,?,?,?,0)', (stream, '', '', ''))
        elif prior != [(value,)]:
            raise ValueError('HA_CONFIGURATION_CHANGED')
        if config.get('governance'):
            self.db.execute('CREATE TABLE IF NOT EXISTS ha_governance_policy(value TEXT NOT NULL)')
            value=canonical({'descriptor':config['governance']['descriptor'],
                             'members':config['governance_members']}).decode()
            prior=self.db.execute('SELECT value FROM ha_governance_policy').fetchall()
            if not prior:self.db.execute('INSERT INTO ha_governance_policy VALUES(?)',(value,))
            elif prior!=[(value,)]:raise ValueError('NATIVE_GOVERNANCE_POLICY_CHANGED')
        if config.get('energy'):
            self.db.execute('CREATE TABLE IF NOT EXISTS ha_energy_policy(value TEXT NOT NULL)')
            value=canonical({'descriptor':config['energy']['descriptor'],
                             'members':config['governance_members']}).decode()
            prior=self.db.execute('SELECT value FROM ha_energy_policy').fetchall()
            if not prior:self.db.execute('INSERT INTO ha_energy_policy VALUES(?)',(value,))
            elif prior!=[(value,)]:raise ValueError('ENERGY_POLICY_CHANGED')

        if config.get('continuation'):
            self.db.execute('CREATE TABLE IF NOT EXISTS ha_continuation_policy(value TEXT NOT NULL)')
            value=canonical({'descriptor':config['continuation']['descriptor'],
                             'members':config['governance_members']}).decode()
            prior=self.db.execute('SELECT value FROM ha_continuation_policy').fetchall()
            if not prior:self.db.execute('INSERT INTO ha_continuation_policy VALUES(?)',(value,))
            elif prior!=[(value,)]:raise ValueError('CONTINUATION_POLICY_CHANGED')
        if config.get('handoff'):
            self.db.execute('CREATE TABLE IF NOT EXISTS ha_handoff_policy(value TEXT NOT NULL)')
            value=canonical({'descriptor':config['handoff']['descriptor'],
                             'members':config['governance_members']}).decode()
            prior=self.db.execute('SELECT value FROM ha_handoff_policy').fetchall()
            if not prior:self.db.execute('INSERT INTO ha_handoff_policy VALUES(?)',(value,))
            elif prior!=[(value,)]:raise ValueError('HANDOFF_POLICY_CHANGED')

    def state(self, stream):
        epoch, owner, lease, boot, deadline = self.db.execute(
            'SELECT epoch,owner,lease_id,boot,deadline FROM ha_terms WHERE stream=?', (stream,)).fetchone()
        remaining = max(0, deadline-time.monotonic_ns()) if boot == boot_identity() else 0
        return dict(epoch=epoch, owner=owner, lease_id=lease, boot=boot, remaining_ns=remaining,
                    head=self.head(stream))

    def owner(self, body):
        point = {key: value for key, value in body.items() if key != 'owner_proof'}
        identity = self.config['ha']['owners'].get(body.get('owner'))
        if identity is None or verify(anchor.public_key(identity), 'ha-owner-request', body['owner_proof']) != {'request': digest(point)}:
            raise ValueError('HA_OWNER_PROOF')

    def event(self, operation, **values):
        seq = self.db.execute('SELECT count(*) FROM ha_events').fetchone()[0]+1
        point = dict(index=seq, operation=operation, source=values.pop('source'),
                     cluster=self.config['cluster'], boot=boot_identity(), **values)
        self.db.execute('INSERT INTO ha_events VALUES(?,?)',
                        (seq, canonical(sign(self.key, 'ha-event', point)).decode()))
        return seq

    def check_fence(self, body):
        state = self.state(body['stream']); expected = token(self.config, body)
        if any(state[name] != expected[name] for name in ('epoch', 'owner', 'lease_id')) or not state['remaining_ns']:
            raise ValueError('HA_FENCED')
        verify_quorum(self.config, body['grant'], 'ha-grant', expected)
        return expected

    def intent_point(self, body, current):
        return dict(token=current, seq=body['seq'], previous=body['previous'], head=body['head'],
                    message=digest(body['message']), operation_id=body['message']['body']['request']['body']['request_id'])

    def reject_intent(self, body):
        policy=self.config.get('semantic_policy')
        if not policy:raise ValueError('HA_SEMANTIC_POLICY_REQUIRED')
        stream=body['stream'];message=body['message'];self.validate_message(stream,message)
        hashed=anchor.ledger_hash(body['previous'],message)
        saved=self.db.execute('SELECT message,proof FROM ha_rejected_intents WHERE stream=? AND seq=? AND hash=?',
                              (stream,body['seq'],hashed)).fetchone()
        if saved:
            if saved[0]!=canonical(message).decode():raise ValueError('HA_REJECTION_FORK')
            return json.loads(saved[1])
        head=self.head(stream)
        if (body['seq'],body['previous'])!=(head['seq']+1,head['head']):raise ValueError('HA_REJECTION_PREFIX')
        from supply_disposition import FEATURES, consume
        if message['body']['type'] in FEATURES:
            rows=self.db.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? ORDER BY seq',(stream,)).fetchall()
            consume(self.config, rows, message, body['comparison'])
            return self.retain_source_rejection(body, hashed)
        votes=body['comparison']['votes'];members=[v['member'] for v in votes]
        if members!=sorted(set(members)) or not 3<=len(members)<=4:raise ValueError('HA_REJECTION_QUORUM')
        expected=None
        for vote in votes:
            decision=verify(anchor.public_key(self.config['ha']['trust']['members'][vote['member']]),'source-semantic-decision',vote['receipt'])
            if (decision['classification']!='invalid' or decision['source']!=body['source'] or
                    decision['stream']!=stream or decision['descriptor']!=policy or
                    decision['prefix']!={'seq':head['seq'],'head':head['head']} or
                    decision['event']!=digest(message) or decision['actual']!=message['body']['record'] or
                    decision['expected']==decision['actual']):raise ValueError('HA_REJECTION_COMPARISON')
            if expected is None:expected=decision['expected']
            elif expected!=decision['expected']:raise ValueError('HA_REJECTION_EXPECTED')
        return self.retain_source_rejection(body, hashed)

    def retain_source_rejection(self, body, hashed):
        stream=body['stream'];message=body['message']
        old=self.db.execute('SELECT previous,hash,message FROM ha_intents WHERE stream=? AND seq=?',(stream,body['seq'])).fetchone()
        if old and old!=(body['previous'],hashed,canonical(message).decode()):raise ValueError('HA_REJECTION_DIFFERENT_INTENT')
        point=dict(source=body['source'],stream=stream,seq=body['seq'],previous=body['previous'],head=hashed,
                   message=digest(message),comparison=body['comparison'],disposition='source-invalid')
        result=sign(self.key,'ha-intent-rejection',point)
        self.db.execute('INSERT OR IGNORE INTO ha_rejected_intents VALUES(?,?,?,?,?)',
                        (stream,body['seq'],hashed,canonical(message).decode(),canonical(result).decode()))
        self.db.execute('DELETE FROM ha_intents WHERE stream=? AND seq=?',(stream,body['seq']))
        return result

    def execute(self, body):
        stream = body['stream']
        if body['source'] != self.config['streams'][stream]['source']:
            raise ValueError('ANCHOR_SOURCE')
        operation = body['op']
        if operation == 'ha-proof':
            row = self.db.execute('SELECT payload FROM ha_events JOIN ha_proofs ON ha_events.id=ha_proofs.event '
                                  'WHERE ha_proofs.stream=? AND ha_proofs.seq=?', (stream, body['seq'])).fetchone()
            if not row:
                raise ValueError('HA_PROOF_NOT_FOUND')
            return {'proof': json.loads(row[0])}
        if operation == 'ha-status':
            state = self.state(stream)
            state['intents'] = [dict(seq=seq, previous=previous, message=json.loads(text))
                for seq, previous, text in self.db.execute(
                    'SELECT seq,previous,message FROM ha_intents WHERE stream=? AND seq>? ORDER BY seq',
                    (stream, state['head']['seq']))]
            return state
        if operation in {'head', 'get'}:
            return super().execute(body)
        if operation not in {'ha-grant', 'ha-stage', 'append','ha-reject-intent'}:
            raise ValueError('HA_OPERATION')
        if 'owner_proof' not in body:
            raise ValueError('HA_FENCE_REQUIRED')
        self.owner(body)
        # Grant, fence check and CAS share the same persistent transaction.
        # A second process opening this SQLite file cannot slip a term change
        # between validation and append.
        self.db.execute('BEGIN IMMEDIATE')
        try:
            if operation == 'ha-grant':
                state = self.state(stream); current = token(self.config, body)
                if type(body['epoch']) is not int or body['epoch'] < 1:
                    raise ValueError('HA_EPOCH')
                same = all(state[name] == body[name] for name in ('epoch', 'owner', 'lease_id'))
                if same and not state['remaining_ns']:
                    raise ValueError('HA_FENCED')
                if not same and (body['epoch'] <= state['epoch'] or state['remaining_ns']):
                    raise ValueError('HA_LEASE_BUSY')
                extend = not same
                if same and body.get('renewal'):
                    verify_quorum(self.config, body['renewal'], 'ha-grant', current)
                    # A partial renewal may extend each member only once. A
                    # second extension requires a new quorum containing that
                    # member's exact last deadline; two isolated votes cannot
                    # renew themselves indefinitely using an old certificate.
                    own = [vote['receipt']['body'] for vote in body['renewal']['votes']
                           if self.config['ha']['trust']['members'][vote['member']] == self.config['registry']['anchor']]
                    extend = bool(own and own[0]['boot'] == state['boot'] and
                                  own[0]['deadline_ns'] == self.db.execute(
                                      'SELECT deadline FROM ha_terms WHERE stream=?', (stream,)).fetchone()[0])
                    if extend and not state['remaining_ns']:
                        raise ValueError('HA_FENCED')
                deadline = (time.monotonic_ns()+int(self.config['ha']['lease_seconds']*10**9) if extend else
                            self.db.execute('SELECT deadline FROM ha_terms WHERE stream=?', (stream,)).fetchone()[0])
                self.db.execute('UPDATE ha_terms SET epoch=?,owner=?,lease_id=?,boot=?,deadline=? WHERE stream=?',
                    (body['epoch'], body['owner'], body['lease_id'], boot_identity(), deadline, stream))
                if not same:
                    self.event('grant', source=body['source'], stream=stream, point=current,
                               previous_epoch=state['epoch'], head=self.head(stream))
                result = sign(self.key, 'ha-grant', dict(point=current, boot=boot_identity(),
                    deadline_ns=deadline, head=self.head(stream)))
            else:
                current = self.check_fence(body)
                if operation=='ha-reject-intent':
                    result=self.reject_intent(body);self.db.execute('COMMIT');return result
                if type(body['seq']) is not int or body['seq'] < 1:
                    raise ValueError('ANCHOR_SEQUENCE')
                self.validate_message(stream, body['message'])
                if self.db.execute('SELECT 1 FROM ha_rejected_intents WHERE stream=? AND seq=? AND hash=?',
                                   (stream,body['seq'],body['head'])).fetchone():raise ValueError('HA_INTENT_SOURCE_REJECTED')
                if anchor.ledger_hash(body['previous'], body['message']) != body['head']:
                    raise ValueError('ANCHOR_HASH')
                old = self.db.execute('SELECT previous,hash,message,receipt FROM entries WHERE stream=? AND seq=?',
                                      (stream, body['seq'])).fetchone()
                exact = (body['previous'], body['head'], canonical(body['message']).decode())
                if old:
                    if old[:3] != exact:
                        raise ValueError('ANCHOR_FORK')
                else:
                    head = self.head(stream)
                    if (head['seq']+1, head['head']) != (body['seq'], body['previous']):
                        raise ValueError('ANCHOR_CAS')
                    self.validate_extension(stream, body['message'])
                expected = self.intent_point(body, current)
                native=(body['message']['body']['type'] in {'native-response','energy-renewal','energy-audit','energy-continuation','energy-handoff','donor-extension','energy-donor'} or
                        'registration' in body['message']['body'])
                if operation == 'ha-stage':
                    if native and not hasattr(self,'engine'):
                        raise ValueError('NATIVE_SOURCE_NOT_INSTALLED')
                    prior = self.db.execute('SELECT previous,hash,message FROM ha_intents WHERE stream=? AND seq=?',
                                            (stream, body['seq'])).fetchone()
                    if prior and prior != exact:
                        raise ValueError('HA_INTENT_FORK')
                    if not prior and not old:
                        self.db.execute('INSERT INTO ha_intents VALUES(?,?,?,?,?)', (stream, body['seq'], *exact))
                    result = sign(self.key, 'ha-intent', {'point': expected})
                    self.event('stage', source=body['source'], stream=stream, point=expected,
                               receipt=result)
                else:
                    verify_quorum(self.config, body['intent'], 'ha-intent', expected)
                    if native and len({vote['member'] for vote in body['intent']['votes']} &
                                      set(self.config['governance_members']))<3:
                        raise ValueError('NATIVE_SOURCE_QUORUM_REQUIRED')
                    point = dict(source=body['source'], stream=stream, seq=body['seq'],
                                 previous=body['previous'], head=body['head'], message=digest(body['message']),
                                 cluster=self.config['cluster'])
                    receipt = json.loads(old[3]) if old else sign(self.key, 'anchor-commit', point)
                    if not old:
                        self.db.execute('INSERT INTO entries VALUES(?,?,?,?,?,?)',
                            (stream, body['seq'], *exact, canonical(receipt).decode()))
                        proof = self.event('append', source=body['source'], stream=stream, point=expected,
                                           grant=body['grant'], intent=body['intent'], receipt=receipt)
                        self.db.execute('INSERT INTO ha_proofs VALUES(?,?,?)', (stream, body['seq'], proof))
                    prior=self.db.execute('SELECT previous,hash,message FROM ha_intents WHERE stream=? AND seq=?',
                                          (stream,body['seq'])).fetchone()
                    if prior and prior!=exact:
                        # A committed quorum can supersede a minority proposal.
                        # Preserve the signed disposition; this neither fulfills
                        # its user's request nor labels that proposal misconduct.
                        disposition=sign(self.key,'ha-intent-supersession',dict(source=body['source'],stream=stream,
                            seq=body['seq'],previous=prior[0],head=prior[1],message=json.loads(prior[2]),
                            committed=body['message'],grant=body['grant'],intent=body['intent'],receipt=receipt))
                        self.db.execute('INSERT OR IGNORE INTO ha_superseded_intents VALUES(?,?,?,?,?)',
                            (stream,body['seq'],prior[1],prior[2],canonical(disposition).decode()))
                        self.db.execute('DELETE FROM ha_intents WHERE stream=? AND seq=?',(stream,body['seq']))
                    result = {'receipt': receipt}
            self.db.execute('COMMIT')
            return result
        except BaseException:
            if self.db.in_transaction:
                self.db.execute('ROLLBACK')
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('config', type=Path)
    args = parser.parse_args(); config = json.loads(args.config.read_text())
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    journal = Journal(config)
    try:
        with anchor.Server((config.get('bind', '127.0.0.1'), config['port']), Handler) as server:
            server.journal = journal; server.context = tls_context(Path(config['pki'])/'anchor', server=True)
            print(json.dumps({'port': config['port'], 'mode': 'ha_fenced_v1'}), flush=True)
            server.serve_forever(poll_interval=.1)
    finally:
        journal.db.close()


if __name__ == '__main__':
    main()

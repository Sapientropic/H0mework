"""One source-bound implementation deviation at the writer's proposal interface.

The original native result is retained. Only a copy of its outgoing proposal is
changed; all source voters keep their ordinary verification and fencing paths.
"""
from copy import deepcopy
from fractions import Fraction
import json
import os
from pathlib import Path

import anchor
from crypto import app_private, canonical, digest, sign, verify
from ha_quorum import Quorum as OriginalQuorum
from recovery_loop import birth, boot_identity
import supply_disposition

SCHEMA = 'source-bound-interface-episode/v1'
KIND = 'native-next-stock-offset-by-requested-quantity'
DOMAIN = 'source-interface-episode'


def once(path, value):
    raw = canonical(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open('xb') as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno())
    except FileExistsError:
        if path.read_bytes() != raw:
            raise ValueError('SOURCE_INTERFACE_OCCURRENCE_CHANGED')


def altered(config, message):
    policy = config['source_interface_fault']; event = message['body']; body = event['request']['body']
    if (set(policy) != {'schema', 'kind', 'request_id', 'prefix', 'owner_permission', 'source_intent', 'journal'} or
            policy['schema'] != SCHEMA or policy['kind'] != KIND):
        raise ValueError('SOURCE_INTERFACE_POLICY')
    if (event['type'] != 'energy-donor' or body['request_id'] != policy['request_id'] or
            body['parent'] != policy['prefix'] or digest(body['continuation']) != policy['owner_permission'] or
            digest(body['transport_intent']) != policy['source_intent'] or body['command']['kind'] != 'donate' or
            type(body['command']['quantity']) is not int or body['command']['quantity'] <= 0):
        raise ValueError('SOURCE_INTERFACE_SOURCE_SCOPE')
    verify(anchor.public_key(config['registry']['server']), 'ledger', message)
    certificate = config['donor_admission']['point']
    selected = [index for index, row in enumerate(event['native']['next']['stock'])
                if row[:2] == [certificate['recipient'], certificate['unit']]]
    if len(selected) != 1:
        raise ValueError('SOURCE_INTERFACE_ACTUAL_STOCK_REQUIRED')
    index = selected[0]; changed = deepcopy(event)
    prior = changed['native']['next']['stock'][index][2]
    changed['native']['next']['stock'][index][2] = str(Fraction(prior) + body['command']['quantity'])
    key = app_private(Path(config['pki'])/'server')
    bad = sign(key, 'ledger', changed)
    point = dict(schema=SCHEMA, kind=KIND, source=event['source'], stream=event['stream'],
                 prefix=policy['prefix'], request_id=body['request_id'], source_intent=policy['source_intent'],
                 owner_permission=policy['owner_permission'], original=digest(message), deviating=digest(bad),
                 capability=dict(signer=config['registry']['server']['app'], distinct_proposals=1,
                                 field=['native', 'next', 'stock', index, 2]),
                 original_value=prior, altered_value=changed['native']['next']['stock'][index][2])
    return point, bad


class Quorum(OriginalQuorum):
    def history_at(self, seq, head):
        current = self.readonly_head()
        if current['seq'] < seq:
            raise ValueError('SOURCE_INTERFACE_CURRENT_PREFIX')
        rows = []; before = anchor.ZERO
        for index, entry in enumerate(self.entries[:seq], 1):
            hashed = entry['receipt']['body']['head']
            rows.append((index, before, hashed, canonical(entry['message']).decode())); before = hashed
        if len(rows) != seq or before != head:
            raise ValueError('SOURCE_INTERFACE_COMMITTED_HISTORY')
        return rows

    def recover(self):
        self.recovering_episode = True
        self.allowed_recovery_message = None
        try:
            return self.recover_episode()
        finally:
            self.recovering_episode = False
            self.allowed_recovery_message = None

    def recover_episode(self):
        # The coordinator must not let the ordinary recovery loop commit an
        # accepted deviating proposal, even when three voters accepted it.
        policy = self.config['source_interface_fault']
        states = self.collect('status')
        if len(states) < 3:
            raise ValueError('SOURCE_INTERFACE_RECOVERY_UNAVAILABLE')
        pending = {digest(intent['message']): intent for state in states.values() for intent in state['intents']
                   if intent['message']['body']['request']['body']['request_id'] == policy['request_id']}
        if len(pending) > 1:
            raise ValueError('SOURCE_INTERFACE_RECOVERY_FORK')
        if pending:
            intent = next(iter(pending.values())); candidate = intent['message']
            episode = Path(policy['journal'])/'episode.json'
            if episode.exists():
                saved = verify(anchor.public_key(self.config['registry']['server']), DOMAIN, json.loads(episode.read_text()))
                original = saved['original']
                if candidate not in (saved['original'], saved['deviating']):
                    raise ValueError('SOURCE_INTERFACE_RECOVERY_UNEXPLAINED')
            else:
                # Another admitted owner can recover the actual source result;
                # the pending proposal never supplies its own expected output.
                rows = self.history_at(intent['seq']-1, intent['previous'])
                context = supply_disposition.context_at(self.config)
                module, argument, _ = supply_disposition.source_at(context, rows, candidate)
                native = module.native_call(context, argument)
                event = deepcopy(candidate['body']); event['native'] = native
                event['nextScope'] = (module.scope_id(context, event['request']['body']['parent'], native['nextScope'])
                                      if native.get('opening') else None)
                module.expected(context, rows, event, native=False)
                original = sign(app_private(Path(self.config['pki'])/'server'), 'ledger', event)
                _, bad = altered(self.config, original)
                if candidate not in (original, bad):
                    raise ValueError('SOURCE_INTERFACE_RECOVERY_UNEXPLAINED')
                if candidate == original:
                    self.allowed_recovery_message = digest(original)
                    self.recovered_native_message = digest(original)
                    try:
                        return super().recover()
                    finally:
                        self.recovered_native_message = None
            # This retries only the same deviating packet. It either obtains
            # three actual comparisons and all dispositions, or stays blocked.
            self.allowed_recovery_message = digest(original)
            self.stage(intent['seq'], intent['previous'], original)
        return super().recover()

    def stage(self, seq, previous, message):
        policy = self.config['source_interface_fault']
        if message['body']['request']['body']['request_id'] != policy['request_id']:
            return super().stage(seq, previous, message)
        if getattr(self, 'recovering_episode', False) and getattr(self, 'allowed_recovery_message', None) != digest(message):
            raise ValueError('SOURCE_INTERFACE_RECOVERY_UNEXAMINED')
        if getattr(self, 'recovered_native_message', None) == digest(message):
            return super().stage(seq, previous, message)
        point, bad = altered(self.config, message)
        if (seq, previous) != (policy['prefix']['seq']+1, policy['prefix']['head']):
            raise ValueError('SOURCE_INTERFACE_PREFIX')
        directory = Path(policy['journal']); key = app_private(Path(self.config['pki'])/'server')
        signer = anchor.public_key(self.config['registry']['server'])
        episode = directory/'episode.json'
        if episode.exists():
            saved = verify(signer, DOMAIN, json.loads(episode.read_text()))
            if saved['point'] != point or saved['original'] != message or saved['deviating'] != bad:
                raise ValueError('SOURCE_INTERFACE_BUDGET_SPENT')
        else:
            once(episode, sign(key, DOMAIN, dict(point=point, original=message, deviating=bad,
                occurrence=dict(owner=self.config['ha']['owner'], boot=boot_identity(), pid=os.getpid(), birth=birth(os.getpid())))))
        done = directory/'disposition.json'
        if done.exists():
            value = verify(signer, 'source-interface-disposition', json.loads(done.read_text()))
            if value['episode'] != digest(point) or value['successful_request_retained'] != message['body']['request']:
                raise ValueError('SOURCE_INTERFACE_DISPOSITION_CHANGED')
            if getattr(self, 'validated_episode', None) != digest(point):
                rows = self.history_at(seq-1, previous)
                supply_disposition.consume(self.config, rows, bad, value['comparison'])
                wanted = dict(source=self.config['source'], stream=self.config['stream'], seq=seq, previous=previous,
                              head=anchor.ledger_hash(previous, bad), message=digest(bad), comparison=value['comparison'], disposition='source-invalid')
                if set(value['rejections']) != set(self.config['governance_members']):
                    raise ValueError('SOURCE_INTERFACE_DISPOSITION_INCOMPLETE')
                for member, receipt in value['rejections'].items():
                    if verify(anchor.public_key(self.trust['members'][member]), 'ha-intent-rejection', receipt) != wanted:
                        raise ValueError('SOURCE_INTERFACE_REJECTION_CHANGED')
                self.validated_episode = digest(point)
            return super().stage(seq, previous, message)
        head = self.readonly_head()
        if (head['seq'], head['head']) != (seq-1, previous):
            raise ValueError('SOURCE_INTERFACE_CURRENT_PREFIX')
        rows = []; before = anchor.ZERO
        for index, entry in enumerate(self.entries, 1):
            hashed = entry['receipt']['body']['head']
            rows.append((index, before, hashed, canonical(entry['message']).decode())); before = hashed
        if len(rows) != seq-1 or before != previous:
            raise ValueError('SOURCE_INTERFACE_COMMITTED_HISTORY')
        # A timeout or missing vote is not evidence. Only actual source decisions
        # below can authorize the original rejection transaction.
        accepted = self.collect('stage', seq=seq, previous=previous, message=bad)
        if len(accepted) >= 3:
            raise ValueError('SOURCE_INTERFACE_UNEXPECTED_ACCEPTANCE')
        comparison_path = directory/'comparison.json'
        if comparison_path.exists():
            comparison = json.loads(comparison_path.read_text())
        else:
            votes = []
            for member, client in self.nodes.items():
                try:
                    status = client.call('semantic-status')
                    for ident, in status['decisions']:
                        receipt = client.call('semantic-decision', id=ident)
                        value = verify(anchor.public_key(self.trust['members'][member]), 'source-semantic-decision', receipt)
                        if value.get('event') == digest(bad) and value.get('classification') == 'invalid':
                            votes.append(dict(member=member, receipt=receipt)); break
                except (ValueError, OSError, EOFError):
                    continue
            if len(votes) < 3:
                raise ValueError('SOURCE_INTERFACE_COMPARISON_UNAVAILABLE')
            comparison = dict(votes=sorted(votes, key=lambda vote: vote['member'])[:3])
            supply_disposition.consume(self.config, rows, bad, comparison)
            once(comparison_path, comparison)
        supply_disposition.consume(self.config, rows, bad, comparison)
        rejected = self.collect('reject', seq=seq, previous=previous, message=bad, comparison=comparison)
        wanted = dict(source=self.config['source'], stream=self.config['stream'], seq=seq, previous=previous,
                      head=anchor.ledger_hash(previous, bad), message=digest(bad), comparison=comparison, disposition='source-invalid')
        valid = {}
        for member, receipt in rejected.items():
            value = verify(anchor.public_key(self.trust['members'][member]), 'ha-intent-rejection', receipt)
            if value != wanted:
                raise ValueError('SOURCE_INTERFACE_REJECTION_CHANGED')
            valid[member] = receipt
        if set(valid) != set(self.config['governance_members']):
            raise ValueError('SOURCE_INTERFACE_DISPOSITION_INCOMPLETE')
        once(done, sign(key, 'source-interface-disposition', dict(episode=digest(point), comparison=comparison,
             rejections=valid, successful_request_retained=message['body']['request'])))
        self.validated_episode = digest(point)
        return super().stage(seq, previous, message)

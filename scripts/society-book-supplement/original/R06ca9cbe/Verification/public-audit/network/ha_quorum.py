"""Authenticated candidate ownership on the original four CAS journals."""
from __future__ import annotations

import json
from pathlib import Path
import secrets
import socket

import anchor
from challenge_anchor import Client as ChallengeClient
from crypto import app_private, digest, peer, receive, send, sign, tls_context, verify
from ha_anchor import token, verify_quorum
from quorum import Client as OriginalQuorum


def vote_timeout(config, operation):
    if operation not in {'ha-stage', 'append'}:
        return 3
    seconds = config.get('semantic_vote_timeout', 3)
    if type(seconds) not in (int, float) or not 3 <= seconds <= 25:
        raise ValueError('HA_VOTE_TIMEOUT')
    if 'productive' in config:
        # Only the admitted source's compute budget changes the RPC wait.
        # Challenge freshness, renewals and the final atomic fence stay intact.
        step = config['productive'].get('native_call_seconds', 30)
        replay = config.get('semantic', {}).get('replay_seconds', step)
        if any(type(v) not in (int, float) or not 0 < v <= 300 for v in (step, replay)):
            raise ValueError('HA_SOURCE_TIMEOUT')
        seconds = max(seconds, replay + step + 3)
    return seconds


class Client(ChallengeClient):
    def call(self, operation, **values):
        endpoint = self.endpoint; ha = self.config['ha']
        raw = socket.create_connection((endpoint['host'], endpoint['port']), timeout=3)
        try:
            connection = tls_context(self.profile, server=False).wrap_socket(raw, server_hostname=endpoint['hostname'])
        except BaseException:
            raw.close(); raise
        with connection:
            connection.settimeout(vote_timeout(self.config, operation))
            uri, fingerprint, key = peer(connection)
            if uri != 'urn:public-audit:anchor' or fingerprint != endpoint['identity']['fingerprint'] or key.public_bytes_raw().hex() != endpoint['identity']['app']:
                raise ValueError('ANCHOR_IDENTITY')
            challenge = receive(connection); body = verify(key, 'anchor-challenge', challenge)
            if body['cluster'] != endpoint['cluster'] or body['valid_for'] != 30:
                raise ValueError('ANCHOR_CHALLENGE_SCOPE')
            request = dict(op=operation, source=self.config['source'], stream=self.config['stream'],
                           nonce=secrets.token_hex(32), challenge=digest(challenge), **values)
            if operation in {'ha-grant', 'ha-stage', 'append','ha-reject-intent'}:
                request['owner'] = ha['owner']
                request['owner_proof'] = sign(app_private(Path(ha['owner_profile'])),
                                              'ha-owner-request', {'request': digest(request)})
            signed = sign(self.key, 'anchor-request', request); send(connection, signed)
            response = receive(connection)
            self.last_exchange = {'request': signed, 'response': response}
            result = verify(key, 'anchor-response', response)
            if result['request'] != digest(signed) or result['nonce'] != request['nonce']:
                raise ValueError('ANCHOR_FRESHNESS')
            if 'error' in result:
                raise ValueError(result['error'])
            return result['result']

    def status(self):
        return self.call('ha-status')

    def proof(self, seq):
        return self.call('ha-proof', seq=seq)

    def grant(self, epoch, lease_id, renewal=None):
        return self.call('ha-grant', epoch=epoch, lease_id=lease_id, renewal=renewal)

    def stage(self, seq, previous, message):
        cfg = self.config['ha']; current = cfg['grant']['point']
        return self.call('ha-stage', seq=seq, previous=previous, head=anchor.ledger_hash(previous, message),
                         message=message, **{k: current[k] for k in ('epoch', 'lease_id')}, grant=cfg['grant'])

    def append(self, seq, previous, message):
        cfg = self.config['ha']; current = cfg['grant']['point']
        intent = self.quorum.stage(seq, previous, message)
        result = self.call('append', seq=seq, previous=previous, head=anchor.ledger_hash(previous, message),
                           message=message, **{k: current[k] for k in ('epoch', 'lease_id')},
                           grant=cfg['grant'], intent=intent)
        anchor.verify_commit(self.endpoint['identity'], result['receipt'], source=self.config['source'],
            stream=self.config['stream'], seq=seq, head=anchor.ledger_hash(previous, message),
            previous=previous, message=message, cluster=self.endpoint['cluster'])
        return result['receipt']

    def reject(self, seq, previous, message, comparison):
        cfg=self.config['ha'];current=cfg['grant']['point']
        return self.call('ha-reject-intent',seq=seq,previous=previous,message=message,comparison=comparison,
                         **{k:current[k] for k in ('epoch','lease_id')},grant=cfg['grant'])


class Quorum(OriginalQuorum):
    def __init__(self, config):
        super().__init__(config)
        self.nodes = {name: Client({**config, 'anchor': {**entry, 'identity': self.trust['members'][name],
                            'cluster': self.cluster}}) for name, entry in config['anchors']['endpoints'].items()}
        for client in self.nodes.values():
            client.quorum = self
        self.intents = {}

    def certificate_at(self, receipts, kind, point):
        if len(receipts) < 3:
            raise ValueError('HA_QUORUM_UNAVAILABLE')
        result = {'kind': kind+'-quorum', 'point': point,
                  'votes': [{'member': name, 'receipt': value} for name, value in sorted(receipts.items())]}
        verify_quorum({'ha': {'trust': self.trust}}, result, kind, point)
        return result

    def grant(self, previous=None):
        if previous:
            point = previous['point']; epoch = point['epoch']; lease = point['lease_id']
        else:
            states = self.collect('status')
            if len(states) < 3:
                raise ValueError('HA_QUORUM_UNAVAILABLE')
            if any(state['owner'] not in ('', self.config['ha']['owner']) and state['remaining_ns'] > 0
                   for state in states.values()):
                raise ValueError('HA_LEASE_BUSY')
            epoch = max(state['epoch'] for state in states.values())+1; lease = secrets.token_hex(32)
            proposal_path = getattr(self, 'proposal_path', None)
            if proposal_path and proposal_path.exists():
                proposed = json.loads(proposal_path.read_text())
                if proposed['epoch'] >= epoch or any(state['epoch'] == proposed['epoch'] and
                        state['lease_id'] == proposed['lease_id'] and state['remaining_ns'] > 0 for state in states.values()):
                    epoch, lease = proposed['epoch'], proposed['lease_id']
            for state in states.values():
                same = [row for row in states.values() if all(row[k] == state[k] for k in ('epoch', 'owner', 'lease_id'))]
                if state['owner'] == self.config['ha']['owner'] and len([r for r in same if r['remaining_ns'] > 0]) >= 3:
                    epoch, lease = state['epoch'], state['lease_id']; break
            if proposal_path:
                from recovery_loop import save
                save(proposal_path, {'epoch': epoch, 'lease_id': lease})
        point = dict(epoch=epoch, owner=self.config['ha']['owner'], lease_id=lease,
                     source=self.config['source'], stream=self.config['stream'], cluster=self.cluster)
        votes = self.collect('grant', epoch=epoch, lease_id=lease, renewal=previous)
        result = self.certificate_at(votes, 'ha-grant', point)
        self.config['ha']['grant'] = result
        return result

    def stage(self, seq, previous, message):
        current = self.config['ha']['grant']['point']; key = digest([current, seq, previous, message])
        if key not in self.intents:
            point = dict(token=current, seq=seq, previous=previous, head=anchor.ledger_hash(previous, message),
                         message=digest(message), operation_id=message['body']['request']['body']['request_id'])
            self.intents[key] = self.certificate_at(self.collect('stage', seq=seq, previous=previous, message=message),
                                                   'ha-intent', point)
        return self.intents[key]

    def recover(self):
        head = self.head()
        states = self.collect('status')
        if len(states) < 3:
            raise ValueError('HA_QUORUM_UNAVAILABLE')
        candidates = {}
        for state in states.values():
            for intent in state['intents']:
                if intent['seq'] == head['seq']+1 and intent['previous'] == head['head']:
                    candidates[digest(intent)] = intent
        if len(candidates) > 1:
            raise ValueError('HA_UNRESOLVED_INTENT_FORK')
        if candidates:
            intent = next(iter(candidates.values()))
            try:self.stage(intent['seq'], intent['previous'], intent['message'])
            except ValueError:
                policy=self.config.get('semantic_policy')
                if not policy:raise
                votes=[]
                for member,client in self.nodes.items():
                    try:
                        state=client.call('semantic-status')
                        for ident, in state['decisions']:
                            decision=client.call('semantic-decision',id=ident)
                            value=verify(anchor.public_key(self.trust['members'][member]),'source-semantic-decision',decision)
                            if (value['event']==digest(intent['message']) and value['classification']=='invalid' and
                                    value['prefix']=={'seq':head['seq'],'head':head['head']} and value['descriptor']==policy):
                                votes.append({'member':member,'receipt':decision});break
                    except (ValueError,OSError,EOFError):continue
                if len(votes)<3:raise ValueError('HA_INTENT_COMPARISON_INCOMPLETE')
                comparison={'votes':sorted(votes,key=lambda v:v['member'])}
                rejected=self.collect('reject',seq=intent['seq'],previous=intent['previous'],message=intent['message'],comparison=comparison)
                point=dict(source=self.config['source'],stream=self.config['stream'],seq=intent['seq'],previous=intent['previous'],
                           head=anchor.ledger_hash(intent['previous'],intent['message']),message=digest(intent['message']),disposition='source-invalid')
                valid=set()
                for member,receipt in rejected.items():
                    try:
                        value=verify(anchor.public_key(self.trust['members'][member]),'ha-intent-rejection',receipt)
                        if all(value.get(k)==v for k,v in point.items()):valid.add(member)
                    except ValueError:continue
                affected={member for member,state in states.items() if intent in state['intents']}
                if len(valid)<3 or not affected<=valid:raise ValueError('HA_INTENT_REJECTION_INCOMPLETE')
                return head
            self.append(intent['seq'], intent['previous'], intent['message'])
            head = self.head()
        return head

    def readonly_head(self):
        states = self.collect('status')
        if len(states) < 3:
            raise ValueError('HA_QUORUM_UNAVAILABLE')
        highest = max((state['head'] for state in states.values()), key=lambda point: point['seq'])
        if sum(state['head'] == highest for state in states.values()) < 3:
            raise ValueError('HA_READ_QUORUM_NOT_CAUGHT_UP')
        if len(self.entries) > highest['seq']:
            raise ValueError('HA_READ_ROLLBACK')
        entries = list(self.entries)
        previous = entries[-1]['receipt']['body']['head'] if entries else '0'*64
        for seq in range(len(entries)+1, highest['seq']+1):
            fetched = self.collect('get', seq=seq)
            groups = {}
            for name, value in fetched.items():
                groups.setdefault(digest(value['message']), {})[name] = value
            accepted = [group for group in groups.values() if len(group) >= 3]
            if len(accepted) != 1:
                raise ValueError('HA_READ_EVENT_QUORUM')
            group = accepted[0]; message = next(iter(group.values()))['message']
            receipt = self.certificate({name: value['receipt'] for name,value in group.items()},
                                       seq=seq, previous=previous, message=message)
            entries.append({'message': message, 'receipt': receipt}); previous = receipt['body']['head']
        if previous != highest['head']:
            raise ValueError('HA_READ_CHAIN')
        self.entries = entries
        return highest


class Reader(Quorum):
    def head(self):
        return self.readonly_head()

    def append(self, *args, **kwargs):
        raise ValueError('HA_FOLLOWER_READ_ONLY')

    def stage(self, *args, **kwargs):
        raise ValueError('HA_FOLLOWER_READ_ONLY')

    def grant(self, *args, **kwargs):
        raise ValueError('HA_FOLLOWER_READ_ONLY')

    def recover(self):
        return self.readonly_head()

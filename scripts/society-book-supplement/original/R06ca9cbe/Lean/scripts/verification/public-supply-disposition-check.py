"""Check the live source-comparison/recovery seam without RPC or economic writes.

The small source fixture executes the original signed HA/SQLite recovery loop.
An optional original journal check consumes a retained native result and performs
its real source argument/authentication checks; it does not rerun that program.
"""
import argparse
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'Verification/public-audit/network'))
import anchor
from crypto import app_private, canonical, create_pki, digest, sign, verify
import donor_arrival_live as donor
import donor_owner_continuation as owner_continuation
from ha_anchor import Journal as HAJournal
from ha_quorum import Client, Quorum
import semantic_anchor
from source_semantics import Engine, Incomplete, Mismatch
import supply_disposition as supply
import supply_interface_fault as interface


def identity(key):
    app = key.public_key().public_bytes_raw().hex()
    return dict(app=app, fingerprint=digest(dict(fixture=app)))


def rejected(action, error=None):
    try:
        action()
    except (ValueError, InvalidSignature, KeyError) as problem:
        if error is not None:
            assert str(problem) == error, (str(problem), error)
        return
    raise AssertionError('negative control accepted')


class LocalClient(Client):
    def __init__(self, journal, config, owner):
        self.journal, self.config, self.owner_key = journal, config, owner
        self.endpoint = dict(identity=journal.config['registry']['anchor'], cluster=config['cluster'])
        self.hidden = False

    def call(self, operation, **values):
        if self.hidden and operation in {'semantic-status', 'semantic-decision'}:
            raise OSError('COMPARISON_DELIVERY_WITHHELD')
        body = dict(op=operation, source=self.config['source'], stream='recovery', **values)
        if operation in {'ha-grant', 'ha-stage', 'append', 'ha-reject-intent'}:
            body['owner'] = 'mac'
            body['owner_proof'] = sign(self.owner_key, 'ha-owner-request', dict(request=digest(body)))
        return self.journal.execute(body)


class LocalQuorum(Quorum):
    def __init__(self, config, nodes, owner):
        self.config, self.trust, self.cluster = config, config['ha']['trust'], config['cluster']
        self.nodes = {name: LocalClient(node, config, owner) for name, node in nodes.items()}
        self.intents, self.entries = {}, []
        for client in self.nodes.values(): client.quorum = self


def fixture():
    checks = []
    with tempfile.TemporaryDirectory(prefix='supply-disposition-') as directory, ExitStack() as stack:
        home = Path(directory); registry = create_pki(home/'pki', anchor=True)
        keys = {name: Ed25519PrivateKey.generate() for name in 'abcd'}
        owner = Ed25519PrivateKey.generate()
        trust = dict(version=1, threshold=3, members={name: identity(key) for name, key in keys.items()})
        descriptor = dict(source='supply-fixture', stream='recovery', compiler='fixture')
        settings = dict(descriptor=descriptor, backend=['fixture', '--run', 'fixture.lean'], exporter='fixture.lean')
        owners = {name: identity(owner) for name in ('mac', 'spark')}
        context = dict(source=descriptor['source'], stream='recovery', registry=registry,
                       semantic=dict(descriptor=descriptor), ha=dict(trust=trust, owners=owners), donor=settings)
        config = dict(source=context['source'], stream='recovery', registry=registry,
                      streams=dict(recovery=dict(source=context['source'], writer=registry['server'])),
                      semantic=dict(descriptor=descriptor, governance_context=context, warm_on_start=False),
                      semantic_policy=descriptor, cluster=digest(trust), donor=settings, governance_members=list('abcd'),
                      ha=dict(trust=trust, owners=owners, owner='mac', lease_seconds=60))
        calls = []

        def argument(ctx, rows, event):
            body = event['request']['body']
            operation = body.get('fixture_operation', body['command'])
            assert ctx['source'] == context['source']
            if (body['parent'] != dict(seq=len(rows), head=rows[-1][2] if rows else anchor.ZERO) or
                    body['permission'] != 'fixture-source-one-use' or operation not in {'supply', 'withhold'}):
                raise ValueError('FIXTURE_SOURCE_AUTHORIZATION')
            return dict(command=operation, inventory=6, old_debt=2, request=body['request_id'])

        def native(ctx, value):
            calls.append(deepcopy(value))
            return dict(status='BLOCKED' if value['command'] == 'withhold' else 'SUPPLIED',
                        next=dict(inventory=0 if value['command'] == 'supply' else value['inventory'],
                                  old_debt=value['old_debt'], delivered=0, clock='1',
                                  stock=[['audit:0', 'feed', '6']],
                                  technology=dict(audit=dict(version=1, holder=2, offered=None))),
                        metadata=value['command'], opening=None, nextScope=None)

        def expected(ctx, rows, event, *, native=True):
            argument(ctx, rows, event)
            if event['nextScope'] is not None:
                raise ValueError('FIXTURE_NEXT')

        def sync(self, rows, **kwargs):
            self.count, self.head = len(rows), rows[-1][2] if rows else anchor.ZERO

        stack.enter_context(patch.object(Engine, 'validate', lambda self: None))
        stack.enter_context(patch.object(Engine, 'sync', sync))
        stack.enter_context(patch('source_extension.guard', lambda *args: None))
        stack.enter_context(patch.object(donor, 'argument', argument))
        stack.enter_context(patch.object(donor, 'native_call', native))
        stack.enter_context(patch.object(donor, 'expected', expected))
        nodes = {}
        try:
            for name, key in keys.items():
                nodehome = home/name; nodehome.mkdir()
                (nodehome/'anchor').mkdir()
                from cryptography.hazmat.primitives import serialization
                (nodehome/'anchor/app.key').write_bytes(key.private_bytes(
                    serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()))
                cfg = deepcopy(config); cfg['database'] = str(nodehome/'journal.sqlite'); cfg['pki'] = str(nodehome)
                cfg['registry']['anchor'] = identity(key)
                initial = anchor.Journal(cfg, initialize=True)
                initial.db.close()
                nodes[name] = semantic_anchor.Journal(cfg)
            quorum = LocalQuorum(config, nodes, owner)
            grant = quorum.grant()
            writer = app_private(home/'pki/server'); actor = app_private(home/'pki/auditor1')
            request = dict(source=config['source'], stream='recovery', actor='1', seq=1,
                           nonce='fixture-nonce', request_id='original-request', parent=dict(seq=0, head=anchor.ZERO),
                           permission='fixture-source-one-use', command='supply')
            event = dict(type='energy-donor', source=config['source'], stream='recovery',
                         request=sign(actor, 'energy-donor', request), peer=registry['auditor1']['fingerprint'],
                         scope='fixture-scope', native=None, nextScope=None)
            event['native'] = native(context, argument(context, [], event))
            good = sign(writer, 'ledger', event)
            bad_event = deepcopy(event); bad_event['native']['next']['old_debt'] = 0
            bad_event['native']['next']['inventory'] = 999
            bad = sign(writer, 'ledger', bad_event)
            # One explicit implementation-fault occurrence, restored immediately.
            point = grant['point']
            body = dict(op='ha-stage', source=config['source'], stream='recovery', seq=1, previous=anchor.ZERO,
                        head=anchor.ledger_hash(anchor.ZERO, bad), message=bad, owner='mac',
                        epoch=point['epoch'], lease_id=point['lease_id'], grant=grant)
            body['owner_proof'] = sign(owner, 'ha-owner-request', dict(request=digest(body)))
            with patch.object(nodes['a'], 'validate_extension', lambda *args: None):
                HAJournal.execute(nodes['a'], body)
            assert nodes['a'].db.execute('SELECT count(*) FROM ha_intents').fetchone() == (1,)
            for client in quorum.nodes.values(): client.hidden = True
            rejected(quorum.recover, 'HA_INTENT_COMPARISON_INCOMPLETE')
            assert nodes['a'].db.execute('SELECT count(*) FROM ha_intents').fetchone() == (1,)
            assert all(node.head('recovery')['seq'] == 0 for node in nodes.values())
            checks.append('missing-comparison-delivery-retains-original-intent')
            for client in quorum.nodes.values(): client.hidden = False
            quorum.recover()
            assert all(node.db.execute('SELECT count(*) FROM ha_intents').fetchone() == (0,) for node in nodes.values())
            proofs = {}
            for name, node in nodes.items():
                raw, signed = node.db.execute('SELECT message,proof FROM ha_rejected_intents').fetchone()
                assert raw == canonical(bad).decode()
                proof = json.loads(signed)
                value = verify(anchor.public_key(trust['members'][name]), 'ha-intent-rejection', proof)
                assert value['disposition'] == 'source-invalid' and value['message'] == digest(bad)
                supply.consume(config, [], bad, value['comparison'])
                proofs[name] = proof
                assert node.head('recovery')['seq'] == 0
            checks.append('three-real-signatures-reject-and-retain-complete-responsibility')
            comparison = proofs['a']['body']['comparison']
            assert len(comparison['votes']) >= 3
            rejection = dict(body, op='ha-reject-intent', comparison=comparison)
            rejection['owner_proof'] = sign(owner, 'ha-owner-request', dict(request=digest(
                {key: value for key, value in rejection.items() if key != 'owner_proof'})))
            assert nodes['a'].execute(rejection) == proofs['a']
            checks.append('duplicate-disposition-is-idempotent')
            bad_controls = {}
            for name, mutate in {
                'missing-quorum': lambda c: c['votes'].pop(),
                'duplicate-receipt': lambda c: c['votes'].__setitem__(1, c['votes'][0]),
                'wrong-signer': lambda c: c['votes'][0].__setitem__('receipt', c['votes'][1]['receipt']),
                'forged-comparison': lambda c: c['votes'][0]['receipt']['body'].__setitem__('expected', '0'*64),
            }.items():
                changed = deepcopy(comparison)
                if name == 'missing-quorum': changed['votes'] = changed['votes'][:3]
                mutate(changed)
                rejected(lambda: supply.consume(config, [], bad, changed))
                bad_controls[name] = True
            forked = deepcopy(comparison)
            first = forked['votes'][0]; value = deepcopy(first['receipt']['body']); value['expected'] = '0'*64
            first['receipt'] = sign(keys[first['member']], 'source-semantic-decision', value)
            rejected(lambda: supply.consume(config, [], bad, forked), 'SUPPLY_COMPARISON_EXPECTED_FORK')
            checks.extend(bad_controls); checks.append('one-valid-signer-cannot-fork-expected-output')
            changed = deepcopy(bad['body']); changed['request']['body']['seq'] = 2
            rejected(lambda: nodes['b'].engine.check([], sign(writer, 'ledger', changed)), 'SUPPLY_COMPARISON_SIGNATURE')
            checks.append('forged-actor-input-produces-no-comparison')
            missing = deepcopy(event); del missing['nextScope']
            rejected(lambda: nodes['b'].engine.check([], sign(writer, 'ledger', missing)), 'SUPPLY_COMPARISON_EVENT')
            checks.append('deleted-generated-next-cannot-be-consumed')
            revoked = deepcopy(event); revoked_request = deepcopy(request); del revoked_request['permission']
            revoked['request'] = sign(actor, 'energy-donor', revoked_request)
            rejected(lambda: nodes['b'].engine.check([], sign(writer, 'ledger', revoked)))
            checks.append('deleted-source-permission-cannot-be-consumed')
            moved = deepcopy(config); moved['semantic']['governance_context']['donor']['backend'][-1] = 'other.lean'
            rejected(lambda: supply.consume(moved, [], bad, comparison), 'SUPPLY_COMPARISON_BINDING')
            moved['donor'] = deepcopy(config['donor'])
            rejected(lambda: supply.consume(moved, [], bad, comparison), 'SUPPLY_COMPARISON_SOURCE_POLICY')
            checks.append('changed-program-does-not-inherit-old-comparisons')
            prior = nodes['b'].db.execute('SELECT count(*) FROM semantic_decisions').fetchone()
            with patch.object(donor, 'native_call', side_effect=Incomplete('SOURCE_TIMEOUT')):
                rejected(lambda: nodes['b'].execute({**body, 'owner_proof': body['owner_proof']}), 'SEMANTIC_INCOMPLETE')
            assert nodes['b'].db.execute('SELECT count(*) FROM semantic_decisions').fetchone() == prior
            checks.append('source-timeout-is-not-deviation-or-decision')
            blocked = deepcopy(event); blocked_request = {**request, 'command': 'withhold'}
            blocked['request'] = sign(actor, 'energy-donor', blocked_request)
            blocked['native'] = native(context, argument(context, [], blocked))
            witness = nodes['b'].engine.check([], sign(writer, 'ledger', blocked))
            assert witness['classification'] == 'verified' and blocked['native']['status'] == 'BLOCKED'
            assert all(node.head('recovery')['seq'] == 0 for node in nodes.values())
            checks.append('source-valid-blocked-is-not-a-ledger-decision')
            quorum.stage(1, anchor.ZERO, good); quorum.append(1, anchor.ZERO, good)
            quorum.append(1, anchor.ZERO, good)
            assert good['body']['request'] == bad['body']['request']
            for node in nodes.values():
                assert node.head('recovery')['seq'] == 1
                rows = node.rows('recovery')
                assert json.loads(rows[0][3]) == good
                assert node.db.execute('SELECT count(*) FROM ha_rejected_intents').fetchone() == (1,)
            checks.append('original-request-continues-once-with-old-debt-and-own-next')
            rejected(lambda: supply.consume(config, nodes['a'].rows('recovery'), bad, comparison))
            checks.append('old-prefix-comparison-cannot-reject-the-next-round')
            # Authorization unit over this fixture's actual committed poststate.
            continuation_context = deepcopy(context)
            continuation_context['donor_admission'] = dict(point=dict(source=config['source'], stream='recovery',
                owner='spark', executor=identity(owner)['app'], source_root=donor.admission.ORIGIN, donor='audit:3', quantity=6))
            actual_rows = nodes['a'].rows('recovery')
            def poststate(ctx, rows):
                assert rows == actual_rows
                paid = json.loads(rows[-1][3])['body']
                after = paid['native']['next']; technology = after['technology']['audit']
                return (dict(mode='donor', base=dict(origin='fixture-source'), commands=[paid['request']['body']['command']]),
                        paid['scope'], dict(clock=after['clock'], cut=int(after['clock']), **technology),
                        dict(commands=[paid['request']['body']['command']]))
            member = dict(seq=1, head=actual_rows[0][2], party=1)
            with patch.object(donor, 'context', poststate), patch('governance.member', return_value=member):
                next_body = owner_continuation.draft(continuation_context, actual_rows, '1')
                intent = sign(actor, donor.ACTION, next_body)
                permit = owner_continuation.approve(continuation_context, actual_rows, intent, owner)
                continued = sign(actor, donor.ACTION, {**next_body, 'continuation': permit})
                value, scope, current, plan = poststate(continuation_context, actual_rows)
                accepted = owner_continuation._consume_at(continuation_context, actual_rows, continued,
                                                          value, scope, current, plan)
                assert accepted == permit['body'] and next_body['command']['round'] == 1
                assert next_body['index'] == 1 and next_body['request_id'] != request['request_id']
                changed = deepcopy(continued['body']); changed['request_id'] = 'another-request'
                rejected(lambda: owner_continuation._consume_at(continuation_context, actual_rows,
                    sign(actor, donor.ACTION, changed), value, scope, current, plan), 'DONOR_CONTINUATION_BINDING')
                rejected(lambda: owner_continuation.approve(continuation_context, actual_rows,
                    intent, Ed25519PrivateKey.generate()), 'DONOR_CONTINUATION_OWNER')
            checks.append('fresh-owner-permission-binds-one-generated-poststate-request')
            episode_body = {**continued['body'], 'transport_intent': intent,
                            'permission': 'fixture-source-one-use', 'fixture_operation': 'supply'}
            episode_event = dict(type=donor.ACTION, source=config['source'], stream='recovery',
                request=sign(actor, donor.ACTION, episode_body), peer=registry['auditor1']['fingerprint'],
                scope='fixture-scope', native=None, nextScope=None)
            episode_event['native'] = native(context, argument(context, actual_rows, episode_event))
            episode_message = sign(writer, 'ledger', episode_event)
            config['pki'] = str(home/'pki')
            config['donor_admission'] = dict(point=dict(recipient='audit:0', unit='feed'))
            config['source_interface_fault'] = dict(schema=interface.SCHEMA, kind=interface.KIND,
                request_id=episode_body['request_id'], prefix=episode_body['parent'],
                owner_permission=digest(permit), source_intent=digest(intent), journal=str(home/'interface'))
            class EpisodeQuorum(interface.Quorum, LocalQuorum):
                __init__ = LocalQuorum.__init__
            active = EpisodeQuorum(config, nodes, owner)
            for client in active.nodes.values(): client.hidden = True
            rejected(lambda: active.stage(2, actual_rows[-1][2], episode_message), 'SOURCE_INTERFACE_COMPARISON_UNAVAILABLE')
            assert not (home/'interface/disposition.json').exists()
            assert all(node.head('recovery')['seq'] == 1 for node in nodes.values())
            checks.append('interface-missing-receipts-cannot-become-a-disposition-or-decision')
            for client in active.nodes.values(): client.hidden = False
            with ExitStack() as transient:
                for name in 'abc':
                    transient.enter_context(patch.object(nodes[name].engine, 'check', return_value=None))
                rejected(lambda: active.stage(2, actual_rows[-1][2], episode_message), 'SOURCE_INTERFACE_UNEXPECTED_ACCEPTANCE')
                rejected(active.recover, 'SOURCE_INTERFACE_UNEXPECTED_ACCEPTANCE')
                assert all(node.head('recovery')['seq'] == 1 for node in nodes.values())
                checks.append('three-acceptances-cannot-send-the-bad-proposal-through-coordinator-recovery')
                with patch.object(donor, 'native_call', side_effect=Incomplete('SOURCE_TIMEOUT')):
                    rejected(active.recover, 'SOURCE_INTERFACE_UNEXPECTED_ACCEPTANCE')
                assert all(node.head('recovery')['seq'] == 1 for node in nodes.values())
                checks.append('three-acceptances-and-one-timeout-remain-uncommitted')
                racing_config = deepcopy(config)
                racing_path = home/'racing-recovery'
                racing_config['source_interface_fault']['journal'] = str(racing_path)
                racing = EpisodeQuorum(racing_config, nodes, owner)
                collect = racing.collect; seen = []
                def racing_collect(operation, *names, **values):
                    result = collect(operation, *names, **values)
                    if operation == 'status':
                        seen.append(operation)
                        if len(seen) == 1:
                            result = {name: {**state, 'intents': []} for name, state in result.items()}
                    return result
                for name in 'abc': racing.nodes[name].hidden = True
                with patch.object(racing, 'collect', side_effect=racing_collect):
                    rejected(racing.recover, 'HA_INTENT_COMPARISON_INCOMPLETE')
                assert not (racing_path/'episode.json').exists()
                assert all(node.head('recovery')['seq'] == 1 for node in nodes.values())
                checks.append('a-pending-visibility-race-cannot-generate-or-commit-a-second-deviation')
            with ExitStack() as transient:
                for name in 'ab':
                    transient.enter_context(patch.object(nodes[name].engine, 'check', return_value=None))
                    active.nodes[name].hidden = True
                rejected(active.recover, 'SOURCE_INTERFACE_COMPARISON_UNAVAILABLE')
                assert all(node.head('recovery')['seq'] == 1 for node in nodes.values())
                checks.append('two-acceptances-and-only-two-delivered-comparisons-retain-the-source-duty')
            for client in active.nodes.values(): client.hidden = False
            # A cold admitted coordinator has the pending signed packet but no
            # local episode file. Its expected result must come from the source.
            recovered_config = deepcopy(config)
            episode_directory = home/'interface-recovery'
            recovered_config['source_interface_fault']['journal'] = str(episode_directory)
            active = EpisodeQuorum(recovered_config, nodes, owner)
            original_call = active.nodes['d'].call
            def withhold_last_commit(operation, **values):
                if operation == 'append' and values.get('seq') == 2: raise OSError('LAST_COMMIT_DELIVERY_WITHHELD')
                return original_call(operation, **values)
            with patch.object(active.nodes['d'], 'call', side_effect=withhold_last_commit):
                active.recover()
            assert sum(node.head('recovery')['seq'] == 2 for node in nodes.values()) == 3
            # A cold read of a paid disposition must not recursively repair its
            # own head while validating that disposition.
            active = EpisodeQuorum(recovered_config, nodes, owner)
            active.recover()
            assert all(node.head('recovery')['seq'] == 2 for node in nodes.values())
            checks.append('the-same-identities-resume-with-real-comparisons-after-the-transient-fault')
            checks.append('cold-recovery-regenerates-the-original-output-from-the-source')
            checks.append('cold-partial-commit-recovery-reads-disposition-history-without-recursive-append')
            calls_before = len(calls)
            active.stage(2, actual_rows[-1][2], episode_message)
            assert len(calls) == calls_before
            episode_receipt = verify(anchor.public_key(registry['server']), interface.DOMAIN, json.loads((episode_directory/'episode.json').read_text()))
            assert episode_receipt['original'] == episode_message
            assert episode_receipt['deviating']['body']['request'] == episode_message['body']['request']
            assert episode_receipt['point']['capability']['distinct_proposals'] == 1
            disposition = verify(anchor.public_key(registry['server']), 'source-interface-disposition', json.loads((episode_directory/'disposition.json').read_text()))
            assert len(disposition['comparison']['votes']) == 3 and set(disposition['rejections']) == set('abcd')
            for node in nodes.values():
                assert node.head('recovery')['seq'] == 2
                assert node.db.execute('SELECT count(*) FROM ha_rejected_intents').fetchone() == (2,)
                assert json.loads(node.rows('recovery')[-1][3]) == episode_message
            assert episode_message['body']['native']['next']['old_debt'] == 2
            changed = deepcopy(episode_message['body']); changed['request']['body']['request_id'] = 'other'
            rejected(lambda: interface.altered(config, sign(writer, 'ledger', changed)), 'SOURCE_INTERFACE_SOURCE_SCOPE')
            changed = deepcopy(episode_message['body']); changed['native']['next']['inventory'] = 10
            rejected(lambda: active.stage(2, actual_rows[-1][2], sign(writer, 'ledger', changed)), 'SOURCE_INTERFACE_BUDGET_SPENT')
            checks.extend(['one-native-output-generates-one-accountable-proposal-deviation',
                'three-comparisons-and-four-dispositions-precede-the-original-request-commit',
                'interface-replay-keeps-one-proposal-and-cannot-spend-the-budget-on-another-output'])
            return dict(checks=checks, native_fixture_calls=len(calls), fixture_events=2,
                        retained_invalid_intents=8, original_request_id=request['request_id'])
        finally:
            for node in nodes.values():
                node.stop_warming.set(); node.engine.close(); node.db.close()


def original_retained(box):
    config = json.loads((box/'local-anchor/config.json').read_text())
    with sqlite3.connect(Path(config['database']).resolve().as_uri()+'?mode=ro', uri=True) as database:
        rows = database.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? ORDER BY seq', ('recovery',)).fetchall()
    chosen = next(row for row in rows if row[0] == 82)
    good = json.loads(chosen[3]); prefix = rows[:81]
    assert good['body']['type'] == 'energy-donor' and good['body']['native']['status'] == 'SUPPLIED'
    context = supply.context_at(config)
    module, argument, _ = supply.source_at(context, prefix, good)
    engine = SimpleNamespace(config=config['semantic'], descriptor=config['semantic_policy'], count=81, head=prefix[-1][2])
    with patch.object(module, 'native_call', return_value=deepcopy(good['body']['native'])) as retained:
        witness = supply.compare(engine, prefix, good)
        assert witness['expected'] == witness['actual'] and retained.call_args.args == (context, argument)
        writer = app_private(box/'service-pki/server')
        changed = deepcopy(good['body']); changed['native']['status'] = 'PRODUCED'
        changed['native']['next']['clock'] = '999999'
        bad = sign(writer, 'ledger', changed)
        try: supply.compare(engine, prefix, bad)
        except Mismatch as problem:
            different = problem.witness
            assert different['expected'] != different['actual'] and different['source_input'] == witness['source_input']
        else: raise AssertionError('retained source difference lost')
    replay = deepcopy(good); replay['body']['request']['body']['nonce'] = 'forged'
    rejected(lambda: supply.source_at(context, prefix, replay), 'SUPPLY_COMPARISON_SIGNATURE')
    # The retained native output is consumed as evidence, never recomputed here.
    compact_size = len(canonical(dict(message=bad, comparison=dict(votes=[dict(member=name,
        receipt=sign(Ed25519PrivateKey.generate(), 'source-semantic-decision', different)) for name in 'abc']))))
    assert compact_size + 8192 <= 65532, compact_size
    proposed = owner_continuation.draft(context, rows, '1')
    actor = app_private(box/'service-pki/auditor1')
    intent = sign(actor, donor.ACTION, proposed)
    value, scope, current, plan = donor.context(context, rows)
    point = owner_continuation._point(context, rows, intent, value, scope, current, plan)
    assert proposed['index'] == 12 and proposed['command'] == dict(kind='donate', quantity=6, round=135, signer=3, enabled=True)
    event = dict(type=donor.ACTION, source=proposed['source'], stream=proposed['stream'],
                 request=intent, scope=scope)
    rejected(lambda: donor.argument(context, rows, event), 'DONOR_CONTINUATION_PERMISSION')
    rejected(lambda: owner_continuation.approve(context, rows, intent, actor), 'DONOR_CONTINUATION_OWNER')
    replay = deepcopy(proposed); replay['continuation'] = config['donor_admission']['permission']
    event['request'] = sign(actor, donor.ACTION, replay)
    rejected(lambda: donor.argument(context, rows, event), 'DONOR_CONTINUATION_PERMISSION')
    changed = deepcopy(proposed); changed['command']['quantity'] = 999
    rejected(lambda: owner_continuation.approve(context, rows, sign(actor, donor.ACTION, changed), actor),
             'DONOR_CONTINUATION_GENERATED_REQUEST')
    return dict(prefix=81, retained_event=82, head=rows[-1][2], events=len(rows),
                source_input=witness['source_input'], comparison_request_bytes=compact_size,
                remaining_frame_bytes=65532-compact_size, native_computations=0, journal_writes=0,
                fresh_owner_request=dict(prefix=point['prefix'], index=proposed['index'], command=proposed['command'],
                    current=point['current'], original_admission=point['original_admission'],
                    controls=['missing-new-permission', 'wrong-owner', 'old-permission-replay', 'caller-supplied-quantity']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--retained-live', type=Path)
    args = parser.parse_args()
    result = dict(schema='supply-disposition-seam-check/v1', fixture=fixture(),
                  rpc=0, economic_requests=0, live_deployment=False)
    if args.retained_live:
        result['original_retained'] = original_retained(args.retained_live.resolve())
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()

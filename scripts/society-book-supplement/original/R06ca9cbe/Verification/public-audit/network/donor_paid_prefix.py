"""Consume the original paid native tape against its committed donor history.

This is a historical consumer. It neither replays economic requests nor gives a
future command an expected reply. The next command still needs native execution.
"""
import json
from pathlib import Path

import anchor
from crypto import canonical, digest, verify
import donor_arrival_admission as admission
import donor_arrival_live as donor
from ha_anchor import verify_quorum
from productive_owner_request import history
import source_readiness
import supply_disposition


def fenced(config, row, facts):
    trust = config['ha']['trust']; source = config['streams']['recovery']['source']
    message = json.loads(row[3]); accepted = []
    for member, item in facts.items():
        if not item.get('proof'):
            continue
        value = verify(anchor.public_key(trust['members'][member]), 'ha-event', item['proof'])
        token = value['grant']['point']
        point = dict(token=token, seq=row[0], previous=row[1], head=row[2], message=digest(message),
                     operation_id=message['body']['request']['body']['request_id'])
        admission.require(value['operation'] == 'append' and value['point'] == point and
            value['source'] == token['source'] == source and value['stream'] == token['stream'] == 'recovery' and
            value['cluster'] == token['cluster'] == config['cluster'] and token['owner'] in config['ha']['owners'],
            'PAID_PREFIX_FENCED_SOURCE')
        verify_quorum(config, value['grant'], 'ha-grant', token)
        verify_quorum(config, value['intent'], 'ha-intent', point)
        admission.require(len({vote['member'] for vote in value['intent']['votes']} &
                              set(config['governance_members'])) >= 3, 'PAID_PREFIX_NATIVE_QUORUM')
        anchor.verify_commit(trust['members'][member], value['receipt'], source=source, stream='recovery',
            seq=row[0], previous=row[1], head=row[2], message=message, cluster=config['cluster'])
        accepted.append(member)
    admission.require(len(accepted) >= 3, 'PAID_PREFIX_COMMIT_QUORUM')
    return sorted(accepted)


def consume(config, rows, evidence, proofs):
    context = supply_disposition.context_at(config)
    certificate = config['donor_admission']; point = certificate['point']; first = point['prefix']['seq']
    admission.require(len(rows) >= first + 1, 'PAID_PREFIX_MISSING_CONTROL')
    if 'anchor' in config['registry']:
        own = [name for name, key in config['ha']['trust']['members'].items() if key == config['registry']['anchor']]
        selected = config.get('donor_history', {}).get('producer')
        admission.require(selected is None or own == [selected], 'PAID_PREFIX_LOCAL_PRODUCER')
    else:
        # A public writer consumes its explicitly selected original producer;
        # it is not itself an anchor signer or a fifth native producer.
        selected = config['donor_history']['producer']
        admission.require(selected in config['ha']['trust']['members'], 'PAID_PREFIX_ORIGINAL_PRODUCER')
        own = [selected]
    admission.require(len(own) == 1 and evidence['member'] == own[0], 'PAID_PREFIX_ORIGINAL_PRODUCER')
    member = own[0]
    original_point, request, old = admission.context(config, rows[:first], point['program'])
    admission.require(original_point == point and evidence['input'] == request and
        evidence['settings']['point'] == point and evidence['settings']['program'] == point['program'] and
        evidence['vote'] == certificate['votes'][member], 'PAID_PREFIX_SOURCE_INPUT')
    donor.certificate(context, rows[:first])
    ready = verify(anchor.public_key(config['ha']['trust']['members'][member]), admission.READY, evidence['vote'])
    output = evidence['output']; native = evidence['native']; objects = ready['objects']
    admission.require(native['exit'] == 0 and native['original_database_writes'] == 0 and
        native['compiler'] == point['program']['compiler'] and native['program'] == point['program'] and
        native['input'] == digest(request) == ready['input'] and native['output'] == digest(output) == ready['output'] and
        native['objects'] == evidence['objects'] == objects and
        native['strict'][1:] == ['--trust=0', '-j1', '-M8000', '-DElab.async=false', '-DwarningAsError=true'],
        'PAID_PREFIX_NATIVE_PRODUCER')
    admission.require({name: source_readiness.sha(Path(config['donor']['lean_path'])/name) for name in objects} == objects,
                      'PAID_PREFIX_INSTALLED_OBJECTS')
    settings = config['donor']
    admission.require(settings.get('private_variant', 'private-one') == 'private-one' and
        settings['backend'][-1] == 'private-one' and 'private_exporter' not in settings, 'PAID_PREFIX_CANONICAL_SOURCE')
    root = Path(settings['cwd']).parent
    admission.require(source_readiness.sha(root/'Lean'/admission.CHECKER) == point['program']['sources'][admission.CHECKER],
                      'PAID_PREFIX_ORIGINAL_CONSUMER')
    admission.require(source_readiness.sha(root/'Verification/public-audit/network/verify.py') == point['program']['consumer'],
                      'PAID_PREFIX_CONSUMER_DEPENDENCY')
    admission.inspect_trace(root, output, request, old)
    signed = evidence['rows']
    admission.require(len(signed) == first and all(len(row) == 5 for row in signed) and
        [list(row[:4]) for row in signed] == [list(row[:4]) for row in rows[:first]], 'PAID_PREFIX_ORIGINAL_ROWS')
    for seq, previous, head, raw, receipt in signed:
        anchor.verify_commit(config['ha']['trust']['members'][member], json.loads(receipt), source=point['source'],
            stream=point['stream'], seq=seq, previous=previous, head=head, message=json.loads(raw), cluster=point['cluster'])
    tape = output['left']
    admission.require(tape['schema'] == 'actual77-donor-continuation/v1' and tape['old'] == old and
        digest(tape['old']) == point['old_output'] and len(tape['output']) == len(request['commands']),
        'PAID_PREFIX_COMPLETE_NATIVE_TAPE')
    end = first + 1 + len(request['commands'])
    admission.require(len(rows) >= end, 'PAID_PREFIX_INCOMPLETE_WORD')
    prefix = rows[:end]
    history(config, prefix)
    expected = [certificate] + tape['output']; receipts = {}
    for index, row in enumerate(prefix[first:]):
        event = json.loads(row[3])['body']
        admission.require(event['type'] == (donor.CONTROL if index == 0 else donor.ACTION) and
            canonical(event['native']) == canonical(expected[index]), 'PAID_PREFIX_ACTUAL_NATIVE_OUTPUT')
        donor.expected(context, prefix[:first+index], event, native=False)
        receipts[str(row[0])] = fenced(config, row, proofs[str(row[0])])
    return dict(schema='paid-donor-history-consumer/v1', source=point['source'], stream=point['stream'],
        prefix=donor.prefix(prefix), original_prefix=point['prefix'], original_history=point['history'],
        owner_admission=digest(certificate), source_input=digest(request), producer_output=digest(output),
        compiler=point['program']['compiler'], native_objects=objects, old_outputs=len(old),
        donor_outputs=len(tape['output']), fenced_commits=receipts, new_commands_consumed=0,
        native_computations=0, economic_requests=0)

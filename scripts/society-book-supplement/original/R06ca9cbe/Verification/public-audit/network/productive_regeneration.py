"""Continue the original material endpoint through its journal-admitted producer."""
from fractions import Fraction
import json

from anchor import public_key
from crypto import canonical, digest, verify
import governance
import energy
import material_regeneration
import productive_extension
import source_extension

KIND = productive_extension.FEATURE


def context(config, rows):
    activated, certificate = productive_extension.require(config, rows)
    parent, scope, current = material_regeneration.context(config, rows[:certificate['point']['prefix']['seq']])
    value = dict(mode='productive', parent=parent, commands=[])
    clock, cut = Fraction(current['clock']), current['cut']
    for row in rows[activated:]:
        event = json.loads(row[3])['body']
        if event['type'] == 'rotation': continue
        if event['type'] != KIND: raise ValueError('PRODUCTIVE_PREFIX_KIND')
        value['commands'].append(event['request']['body']['command'])
        native = event['native']
        if native['status'] == 'ERROR': continue
        after = native['next']; technology = after['technology']['audit']
        delta = Fraction(after['clock']) - clock
        if delta.denominator != 1 or delta < 0: raise ValueError('PRODUCTIVE_CLOCK_UNIT')
        current = dict(clock=after['clock'], cut=cut+int(delta), version=technology['version'],
                       holder=technology['holder'], offered=technology['offered'])
        scope = event['nextScope'] or scope
    return value, scope, current


def authorization(config, body):
    return {k: body[k] for k in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                'cut', 'epoch', 'command', 'unit', 'scope')} | {
        'descriptor': digest(config['productive']['descriptor'])}


def argument(config, rows, event):
    body = event['request']['body']
    if (event['type'] != KIND or event['request']['kind'] != KIND
            or body['unit'] != 'energy' or body['actor'] not in ('1', '2')):
        raise ValueError('PRODUCTIVE_KIND_OR_UNIT')
    value, scope, current = context(config, rows)
    parent = dict(seq=len(rows), head=rows[-1][2])
    source = config.get('source') or config['streams'][event['stream']]['source']
    if (event['source'] != source or body['source'] != source or event['stream'] != 'recovery'
            or body['stream'] != 'recovery' or body['parent'] != parent
            or event['scope'] != scope or body['scope'] != scope):
        raise ValueError('PRODUCTIVE_PARENT_SCOPE')
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])
            or body['member'] != governance.member(config, rows, body['actor'])):
        raise ValueError('PRODUCTIVE_CURRENT_MEMBER')
    registration = next((e for e in governance.registered(rows) if e['result']['key'] == body['executor']), None)
    if registration is None: raise ValueError('PRODUCTIVE_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    granted = verify(public_key(config['ha']['owners'][owner]), 'native-productive-regeneration', body['execution'])
    if granted != authorization(config, body): raise ValueError('PRODUCTIVE_OWNER_AUTHORIZATION')
    value['commands'].append(body['command'])
    return value


def native_call(config, value):
    return energy.native_call({**config, 'energy': config['productive']}, value)


def scope_id(config, parent, scope):
    return digest(dict(descriptor=config['productive']['descriptor'], parent=parent, scope=scope))


def expected(config, rows, event, *, native=True):
    source_extension.guard(config, rows, event)
    if set(event) != {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}:
        raise ValueError('PRODUCTIVE_EVENT_FIELDS')
    value = argument(config, rows, event); result = event['native']
    if result['metadata'] != value['commands'][-1] or result['status'] not in {'PRODUCED', 'OPENED', 'DELIVERED', 'BLOCKED', 'CONTINUED', 'ERROR'}:
        raise ValueError('PRODUCTIVE_COMPLETE_REPLY')
    expected_scope = scope_id(config, event['request']['body']['parent'], result['nextScope']) if result.get('opening') else None
    if event['nextScope'] != expected_scope: raise ValueError('PRODUCTIVE_GENERATED_SCOPE')
    if native and canonical(native_call(config, value)) != canonical(result): raise ValueError('PRODUCTIVE_SOURCE_MISMATCH')
    return result


def produce(config, rows, event):
    event['native'] = native_call(config, argument(config, rows, event))
    event['nextScope'] = scope_id(config, event['request']['body']['parent'], event['native']['nextScope']) if event['native'].get('opening') else None
    expected(config, rows, event)
    return event

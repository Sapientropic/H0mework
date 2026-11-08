"""Continue the original supply history through its admitted material producer."""
from fractions import Fraction
import json

from anchor import public_key
from crypto import canonical, digest, verify
import energy
import governance
import material_extension
import regeneration
import source_extension

KIND = material_extension.FEATURE
MODES = regeneration.MODES | {'refeed', 'deny-recycling'}


def context(config, rows):
    activated, certificate = material_extension.committed(config, rows) or (None, None)
    if activated is None: raise ValueError('MATERIAL_NOT_COMMITTED')
    origin = certificate['point']['prefix']['seq']
    value, scope, current = regeneration.context(config, rows[:origin])
    initial_clock = Fraction(current['clock']); initial_cut = current['cut']
    for row in rows[activated:]:
        event = json.loads(row[3])['body']
        if event['type'] == 'rotation': continue
        if event['type'] != KIND: raise ValueError('MATERIAL_PREFIX_KIND')
        value['requests'].append(regeneration.command(event['request']['body']))
        native = event['native']
        if native['status'] == 'ERROR': continue
        after = native['next']; technology = after['technology']['audit']
        delta = Fraction(after['clock'])-initial_clock
        if delta.denominator != 1 or delta < 0: raise ValueError('MATERIAL_CLOCK_UNIT')
        current = dict(clock=after['clock'], cut=initial_cut+int(delta), version=technology['version'],
                       holder=technology['holder'], offered=technology['offered'])
        scope = event['nextScope'] or scope
    return value, scope, current


def authorization(config, body):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                      'cut', 'epoch', 'query', 'mode', 'unit', 'scope')} | {
        'descriptor': digest(config['refeed']['descriptor'])}


def argument(config, rows, event):
    body = event['request']['body']
    if (event['type'] != KIND or event['request']['kind'] != KIND or body['mode'] not in MODES
            or body['unit'] != 'energy' or body['actor'] not in ('1', '2')):
        raise ValueError('MATERIAL_KIND_OR_UNIT')
    value, scope, current = context(config, rows)
    parent = dict(seq=len(rows), head=rows[-1][2])
    source = config.get('source') or config['streams'][event['stream']]['source']
    if (event['source'] != source or body['source'] != source or event['stream'] != 'recovery'
            or body['stream'] != 'recovery' or body['parent'] != parent
            or event['scope'] != scope or body['scope'] != scope):
        raise ValueError('MATERIAL_PARENT_SCOPE')
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])):
        raise ValueError('MATERIAL_CURRENT')
    energy.query(body['query'])
    if body['member'] != governance.member(config, rows, body['actor']):
        raise ValueError('MATERIAL_MEMBER')
    registration = next((e for e in governance.registered(rows) if e['result']['key'] == body['executor']), None)
    if registration is None: raise ValueError('MATERIAL_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    granted = verify(public_key(config['ha']['owners'][owner]), 'native-material-regeneration', body['execution'])
    if granted != authorization(config, body): raise ValueError('MATERIAL_OWNER_AUTHORIZATION')
    value['requests'].append(regeneration.command(body))
    return value


def native_call(config, value):
    return energy.native_call({**config, 'energy': config['refeed']}, value)


def scope_id(config, parent, scope):
    return digest(dict(descriptor=config['refeed']['descriptor'], parent=parent, scope=scope))


def expected(config, rows, event, *, native=True):
    source_extension.guard(config, rows, event)
    if set(event) != {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}:
        raise ValueError('MATERIAL_EVENT_FIELDS')
    value = argument(config, rows, event); result = event['native']
    if result['metadata'] != value['requests'][-1] or result['status'] not in {'OPENED','DELIVERED','BLOCKED','CONTINUED','ERROR'}:
        raise ValueError('MATERIAL_COMPLETE_REPLY')
    expected_scope = scope_id(config, event['request']['body']['parent'], result['nextScope']) if result.get('opening') else None
    if event['nextScope'] != expected_scope: raise ValueError('MATERIAL_GENERATED_SCOPE')
    if native and canonical(native_call(config, value)) != canonical(result): raise ValueError('MATERIAL_SOURCE_MISMATCH')
    return result


def produce(config, rows, event):
    event['native'] = native_call(config, argument(config, rows, event))
    event['nextScope'] = scope_id(config, event['request']['body']['parent'], event['native']['nextScope']) if event['native'].get('opening') else None
    expected(config, rows, event)
    return event

"""Reconstruct the paid supply programme from its committed admission and requests."""
from fractions import Fraction
import json

from anchor import public_key
from crypto import canonical, digest, verify
import energy
import governance
import handoff
import source_extension

KIND = source_extension.FEATURE
MODES = {'normal', 'withhold-fuel', 'deny-production', 'wrong-supplier'}


def command(body):
    return dict(query=body['query'], mode=body['mode'], metadata=body)


def scope_id(config, parent, scope):
    return digest(dict(descriptor=config['regeneration']['descriptor'], parent=parent, scope=scope))


def context(config, rows):
    activated, certificate = source_extension.require(config, rows)
    origin = certificate['point']['prefix']['seq']
    legacy = [row for row in rows[:origin] if json.loads(row[3])['body']['type'] != 'rotation']
    base, scope, current = handoff.context(config, legacy)
    base = dict(mode='handoff', **base)
    requests = []; initial_clock = Fraction(current['clock']); initial_cut = current['cut']
    for row in rows[activated:]:
        event = json.loads(row[3])['body']
        if event['type'] == 'rotation':
            continue
        if event['type'] != KIND:
            raise ValueError('REGENERATION_PREFIX_KIND')
        requests.append(command(event['request']['body']))
        native = event['native']
        if native['status'] == 'ERROR':
            continue
        next_state = native['next']; technology = next_state['technology']['audit']
        delta = Fraction(next_state['clock'])-initial_clock
        if delta.denominator != 1 or delta < 0:
            raise ValueError('REGENERATION_CLOCK_UNIT')
        current = dict(clock=next_state['clock'], cut=initial_cut+int(delta),
                       version=technology['version'], holder=technology['holder'], offered=technology['offered'])
        scope = event['nextScope'] or scope
    return dict(mode='regeneration', base=base, requests=requests), scope, current


def authorization(config, body):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                      'cut', 'epoch', 'query', 'mode', 'unit', 'scope')} | {
        'descriptor': digest(config['regeneration']['descriptor'])}


def argument(config, rows, event):
    body = event['request']['body']
    if (event['type'] != KIND or event['request']['kind'] != KIND or body['mode'] not in MODES
            or body['unit'] != 'energy' or body['actor'] not in ('1', '2')):
        raise ValueError('REGENERATION_KIND_OR_UNIT')
    value, scope, current = context(config, rows)
    source = config.get('source') or config['streams'][event['stream']]['source']
    stream = config.get('stream') or source_extension.require(config, rows)[1]['point']['stream']
    prefix = dict(seq=len(rows), head=rows[-1][2])
    if (event['source'] != source or body['source'] != source
            or event['stream'] != stream or body['stream'] != stream or body['parent'] != prefix
            or event['scope'] != scope or body['scope'] != scope):
        raise ValueError('REGENERATION_PARENT_SCOPE')
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])):
        raise ValueError('REGENERATION_CURRENT')
    energy.query(body['query'])
    if canonical(body['member']) != canonical(governance.member(config, rows, body['actor'])):
        raise ValueError('REGENERATION_MEMBER_ORIGIN')
    registration = next((entry for entry in governance.registered(rows)
                         if entry['result']['key'] == body['executor']), None)
    if registration is None:
        raise ValueError('REGENERATION_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    granted = verify(public_key(config['ha']['owners'][owner]), 'native-energy-regeneration', body['execution'])
    if canonical(granted) != canonical(authorization(config, body)):
        raise ValueError('REGENERATION_OWNER_AUTHORIZATION')
    value['requests'].append(command(body))
    return value


def native_call(config, value):
    return energy.native_call({**config, 'energy': config['regeneration']}, value)


def expected(config, rows, event, *, native=True):
    source_extension.guard(config, rows, event)
    if set(event) != {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}:
        raise ValueError('REGENERATION_EVENT_FIELDS')
    value = argument(config, rows, event)
    result = event['native']
    if result['metadata'] != value['requests'][-1] or result['status'] not in {'OPENED', 'DELIVERED', 'BLOCKED', 'CONTINUED', 'ERROR'}:
        raise ValueError('REGENERATION_COMPLETE_REPLY')
    next_scope = scope_id(config, event['request']['body']['parent'], result['nextScope']) if result.get('opening') else None
    if event['nextScope'] != next_scope:
        raise ValueError('REGENERATION_GENERATED_SCOPE')
    if native and canonical(native_call(config, value)) != canonical(result):
        raise ValueError('REGENERATION_SOURCE_MISMATCH')
    return result


def produce(config, rows, event):
    event['native'] = native_call(config, argument(config, rows, event))
    event['nextScope'] = scope_id(config, event['request']['body']['parent'], event['native']['nextScope']) if event['native'].get('opening') else None
    expected(config, rows, event)
    return event

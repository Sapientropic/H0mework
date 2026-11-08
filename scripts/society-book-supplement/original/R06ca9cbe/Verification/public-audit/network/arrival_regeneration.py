"""Replay the original source and the full arrival/service word for each request."""
from fractions import Fraction
import json

from anchor import public_key
from crypto import canonical, digest, verify
import energy
import governance
import productive_regeneration
import arrival_extension

KIND = arrival_extension.FEATURE
ORIGIN = arrival_extension.ORIGIN
REPLY_FIELDS = {'source_root', 'metadata', 'status', 'next', 'nextScope', 'opening', 'scope',
                'before', 'service', 'source', 'sourceNext', 'sourceRows', 'debit', 'credit',
                'spent', 'account'}


def _source_root(config):
    descriptor = config['arrival']['descriptor']
    if descriptor.get('source_root') != ORIGIN:
        raise ValueError('ARRIVAL_SOURCE_ROOT_DESCRIPTOR')
    return ORIGIN


def context(config, rows):
    activated, certificate = arrival_extension.require(config, rows)
    origin = certificate['point']['prefix']['seq']
    base, scope, current = productive_regeneration.context(config, rows[:origin])
    _source_root(config)
    value = dict(mode='arrival', source=base, events=[])
    for row in rows[activated:]:
        event = json.loads(row[3])['body']
        if event['type'] == 'rotation':
            continue
        if event['type'] != KIND:
            raise ValueError('ARRIVAL_PREFIX_KIND')
        command = event['request']['body']['command']
        value['events'].append(command)
        native = event['native']
        if native['status'] == 'ERROR':
            continue
        after = native['next']; technology = after['technology']['audit']
        delta = Fraction(after['clock']) - Fraction(current['clock'])
        if delta.denominator != 1 or delta < 0:
            raise ValueError('ARRIVAL_CLOCK_UNIT')
        current = dict(clock=after['clock'], cut=current['cut'] + int(delta),
                       version=technology['version'], holder=technology['holder'],
                       offered=technology['offered'])
        scope = event['nextScope'] or scope
    return value, scope, current


def authorization(config, body):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                      'cut', 'epoch', 'command', 'unit', 'scope', 'source_root')} | {
        'descriptor': digest(config['arrival']['descriptor'])}


def argument(config, rows, event):
    body = event['request']['body']
    if (event['type'] != KIND or event['request']['kind'] != KIND
            or body['unit'] != 'energy' or body['actor'] not in ('1', '2')):
        raise ValueError('ARRIVAL_KIND_OR_UNIT')
    source_root = _source_root(config)
    if body['source_root'] != source_root:
        raise ValueError('ARRIVAL_SOURCE_ROOT')
    value, scope, current = context(config, rows)
    parent = dict(seq=len(rows), head=rows[-1][2])
    source = config.get('source') or config['streams'][event['stream']]['source']
    stream = config.get('stream') or arrival_extension.require(config, rows)[1]['point']['stream']
    if (event['source'] != source or body['source'] != source
            or event['stream'] != stream or body['stream'] != stream
            or body['parent'] != parent or event['scope'] != scope or body['scope'] != scope):
        raise ValueError('ARRIVAL_PARENT_SCOPE')
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])):
        raise ValueError('ARRIVAL_CURRENT')
    if body['member'] != governance.member(config, rows, body['actor']):
        raise ValueError('ARRIVAL_MEMBER')
    registration = next((entry for entry in governance.registered(rows)
                         if entry['result']['key'] == body['executor']), None)
    if registration is None:
        raise ValueError('ARRIVAL_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    granted = verify(public_key(config['ha']['owners'][owner]),
                     'native-arrival-regeneration', body['execution'])
    if canonical(granted) != canonical(authorization(config, body)):
        raise ValueError('ARRIVAL_OWNER_AUTHORIZATION')
    value['events'].append(body['command'])
    return value


def native_call(config, value):
    return energy.native_call({**config, 'energy': config['arrival']}, value)


def scope_id(config, parent, scope):
    return digest(dict(descriptor=config['arrival']['descriptor'], parent=parent, scope=scope))


def expected(config, rows, event, *, native=True):
    arrival_extension.guard(config, rows, event)
    if set(event) != {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}:
        raise ValueError('ARRIVAL_EVENT_FIELDS')
    value = argument(config, rows, event); result = event['native']
    statuses = {'ARRIVED', 'BLOCKED', 'ERROR', 'PRODUCED', 'OPENED', 'DELIVERED', 'CONTINUED'}
    if (set(result) != REPLY_FIELDS or result['source_root'] != _source_root(config)
            or canonical(result['metadata']) != canonical(value['events'][-1])
            or result['status'] not in statuses
            or not isinstance(result['scope'], dict) or result['scope'].get('unit') != 'energy'
            or not isinstance(result['nextScope'], dict) or result['nextScope'].get('unit') != 'energy'
            or not isinstance(result['before'], dict)
            or not isinstance(result['source'], dict) or not isinstance(result['sourceNext'], dict)
            or not isinstance(result['sourceRows'], list)
            or not isinstance(result['debit'], list) or not isinstance(result['credit'], list)
            or type(result['spent']) is not bool
            or not isinstance(result['account'], dict)
            or set(result['account']) != {'slots', 'outstanding'}
            or type(result['account']['slots']) is not int or result['account']['slots'] < 0
            or not isinstance(result['account']['outstanding'], str)):
        raise ValueError('ARRIVAL_COMPLETE_REPLY')
    try:
        outstanding = Fraction(result['account']['outstanding'])
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('ARRIVAL_ACCOUNT_OUTSTANDING') from error
    if outstanding < 0:
        raise ValueError('ARRIVAL_ACCOUNT_OUTSTANDING')
    if not isinstance(result['next'], dict) or type(result['opening']) is not bool:
        raise ValueError('ARRIVAL_NEXT_SCHEMA')
    command = value['events'][-1]
    is_arrival = isinstance(command, dict) and command.get('kind') == 'arrival'
    allowed_statuses = {'ARRIVED', 'BLOCKED', 'ERROR'} if is_arrival else {
        'PRODUCED', 'OPENED', 'DELIVERED', 'BLOCKED', 'CONTINUED', 'ERROR'}
    if result['status'] not in allowed_statuses:
        raise ValueError('ARRIVAL_COMMAND_STATUS')
    if is_arrival and result['status'] != 'ERROR':
        if result['service'] is not None:
            raise ValueError('ARRIVAL_SERVICE_REPLY')
    else:
        service = result['service']
        if (not isinstance(service, dict) or service.get('status') != result['status']
                or canonical(service.get('metadata')) != canonical(result['metadata'])):
            raise ValueError('ARRIVAL_SERVICE_REPLY')
    if (result['status'] == 'ARRIVED') != bool(result['sourceRows']) or \
            (result['status'] == 'ARRIVED') != bool(result['debit']) or \
            (result['status'] == 'ARRIVED') != bool(result['credit']):
        raise ValueError('ARRIVAL_RECEIPT_SCOPE')
    expected_scope = scope_id(config, event['request']['body']['parent'], result['nextScope']) if result['opening'] else None
    if event['nextScope'] != expected_scope:
        raise ValueError('ARRIVAL_GENERATED_SCOPE')
    if native and canonical(native_call(config, value)) != canonical(result):
        raise ValueError('ARRIVAL_SOURCE_MISMATCH')
    return result


def produce(config, rows, event):
    event['native'] = native_call(config, argument(config, rows, event))
    event['nextScope'] = (scope_id(config, event['request']['body']['parent'], event['native']['nextScope'])
                          if event['native'].get('opening') else None)
    expected(config, rows, event)
    return event

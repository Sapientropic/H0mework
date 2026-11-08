"""A separately priced epoch generated from the original journal's paid supply.

The original labor law, descriptor and disclosure consumer remain immutable.
This reader reconstructs the original prefix and every energy epoch visit.
"""
from __future__ import annotations

from fractions import Fraction
import copy
import time

from anchor import public_key
from crypto import canonical, digest, verify
import governance
from verify import payment_scan, lifecycle_replay

KINDS = {'energy-renewal', 'energy-audit'}
_readers = {}
_cache = {}


def close_readers():
    for engine in _readers.values():
        engine.close()
    _readers.clear()
    _cache.clear()


def native_call(config, argument):
    from source_semantics import Engine
    settings = config.get('energy')
    if not settings or 'backend' not in settings:
        raise ValueError('ENERGY_SOURCE_NOT_INSTALLED')
    name = digest(settings)
    if name not in _readers:
        _readers[name] = Engine(settings)
    engine = _readers[name]
    if engine.process is None or engine.process.poll() is not None:
        engine.start()
        _cache[name] = {}
    cache = _cache.setdefault(name,{})
    identity = digest(argument)
    # This exporter is a pure function of the full signed-prefix input. A new
    # worker recomputes it; stage, append and lookup share its exact paid work.
    if identity not in cache:
        seconds = settings.get('native_call_seconds', 30)
        if type(seconds) not in (int, float) or not 0 < seconds <= 300:
            raise ValueError('NATIVE_CALL_SECONDS')
        result = engine.call(argument, time.monotonic()+seconds)
        if len(cache)>=64:cache.pop(next(iter(cache)))
        cache[identity] = result
    return copy.deepcopy(cache[identity])


def events(rows):
    return governance.contents(rows)


def latest(rows):
    return next((event for event in reversed(events(rows)) if event['type'] in KINDS), None)


def scope_id(config, parent, candidate):
    return digest({'descriptor': config['energy']['descriptor'], 'parent': parent,
                   'candidate': candidate, 'unit': 'energy'})


def query(value):
    if (set(value) != {'slots', 'fields'} or
            any(type(value[k]) is not int for k in value) or
            not 0 <= value['slots'] < 64 or not 0 <= value['fields'] < 4):
        raise ValueError('QUERY_MASK')
    return value


def argument(config, rows, event):
    body = event['request']['body']
    if event['type'] not in KINDS or event['request']['kind'] != event['type']:
        raise ValueError('ENERGY_EVENT_KIND')
    source = config.get('source') or config['streams'][event['stream']]['source']
    if body['source'] != source or event['source'] != source or body['unit'] != 'energy':
        raise ValueError('ENERGY_NAMESPACE_OR_UNIT')
    parent = {'seq': len(rows), 'head': rows[-1][2] if rows else '0'*64}
    if body['parent'] != parent:
        raise ValueError('ENERGY_PARENT')
    past = events(rows)
    if any(e['type']=='energy-continuation' for e in past):
        raise ValueError('CONTINUATION_QUERY_REQUIRED')
    renewal = next((e for e in past if e['type'] == 'energy-renewal'), None)
    response = governance.response_at(rows)
    if response is None:
        raise ValueError('ENERGY_ORIGINAL_RESPONSE_REQUIRED')
    if event['type'] == 'energy-renewal':
        if renewal or past[-1] != response:
            raise ValueError('ENERGY_RENEWAL_ORDER')
        candidate = body['candidate']
        if type(candidate) is not int or candidate not in (1, 2):
            raise ValueError('ENERGY_CANDIDATE')
        origin = governance.member(config, rows, body['actor'])
        if body['member'] != origin:
            raise ValueError('ENERGY_MEMBER_ORIGIN')
        key = body['executor']
        registration = next((entry for entry in governance.registered(rows)
                             if entry['result']['key'] == key), None)
        if registration is None:
            raise ValueError('ENERGY_OWNER_NOT_REGISTERED')
        owner = registration['proof']['body']['owner']
        authorization = verify(public_key(config['ha']['owners'][owner]),
                               'native-energy-renewal', body['execution'])
        expected = dict(source=source, stream=event['stream'], parent=parent,
                        executor=key, member=origin, candidate=candidate, unit='energy',
                        cut=body['cut'], epoch=body['epoch'], query=query(body['query']),
                        scope=scope_id(config, parent, candidate))
        if authorization != expected or event['scope'] != expected['scope']:
            raise ValueError('ENERGY_OWNER_AUTHORIZATION')
        current = response['native']['next']
        ordinal = 1
        received = []
    else:
        if renewal is None:
            raise ValueError('ENERGY_SCOPE_REQUIRED')
        candidate = renewal['request']['body']['candidate']
        if body['scope'] != renewal['scope'] or event['scope'] != renewal['scope']:
            raise ValueError('ENERGY_SCOPE')
        current_event = latest(rows)
        current = {**current_event['native']['epoch']['next'],
                   'cut': current_event['native']['nextCut']}
        ordinal = current_event['native']['epoch']['ordinal']+1
        received = [{'ordinal': e['native']['epoch']['ordinal'],
                     'query': e['request']['body']['query']} for e in past if e['type'] in KINDS]
    if body['actor'] != str(candidate):
        raise ValueError('ENERGY_AUDITOR_IDENTITY')
    if (body['cut'], body['epoch']) != (current['cut'], current['version']):
        raise ValueError('ENERGY_SOURCE_CURRENT')
    received.append({'ordinal': ordinal, 'query': query(body['query'])})
    births = [{'cut': entry['result']['cut'], 'key': entry['result']['key']}
              for entry in governance.registered(rows)]
    births += [{'cut': response['request']['body']['cut'],
                'key': response['request']['body']['executor']}]
    reply = response['request']['body']
    return {'cut': response['native']['next']['cut'],
            'history': [{'cut': e['record']['cut'], 'query': e['record']['query']}
                        for e in past if e['type'] == 'disclosure'],
            'births': births, 'replies': [{'cut': reply['cut'], 'challenger': int(reply['actor']),
                'observedCut': reply['proposal']['body']['record']['cut'],
                'alleged': reply['proposal']['body']['record']}],
            'candidate': candidate, 'queries': received, 'ordinal': ordinal}


def check_packet(packet, scope):
    if set(packet) != {'index','actor','query','unit','accessEnergy','deliveryEnergy','clock','version','evidence'}:
        raise ValueError('ENERGY_PACKET_SCHEMA')
    if any(type(packet[key]) is not int or packet[key]<0 for key in ('index','actor','version')):
        raise ValueError('ENERGY_PACKET_TYPES')
    query(packet['query'])
    if (packet['unit'] != 'energy' or Fraction(packet['accessEnergy']) != 1 or
            Fraction(packet['deliveryEnergy']) != 1 or
            not Fraction(scope['earliest']) <= Fraction(packet['clock']) <= Fraction(scope['deadline'])):
        raise ValueError('ENERGY_PACKET_PAYMENT_OR_WINDOW')
    mask, fields = packet['query']['slots'], packet['query']['fields']
    if [row['slot'] for row in packet['evidence']] != [i for i in range(6) if mask & (1 << i)]:
        raise ValueError('ENERGY_PACKET_SCOPE')
    for row in packet['evidence']:
        if (set(row) != {'slot','admission','payment'} or
                (row['admission'] is not None) != bool(fields & 1) or
                (row['payment'] is not None) != bool(fields & 2)):
            raise ValueError('ENERGY_PACKET_FIELDS')
    return {'payment': [payment_scan(row['slot'], row) for row in packet['evidence']],
            'lifecycle': [lifecycle_replay(row['slot'], row) for row in packet['evidence']]}


def check_flows(native):
    if not native.get('ready') or native['scope']['unit'] != 'energy':
        raise ValueError('ENERGY_SUPPLY_NOT_READY')
    visits = [native['supply'], *native['stages']]
    for index, visit in enumerate(visits):
        before, after = visit['before'], visit['next']
        if before['labor'] != after['labor']:
            raise ValueError('ENERGY_LABOR_CONVERSION')
        if Fraction(after['clock']) != Fraction(before['clock'])+1 or after['round'] != before['round']+1:
            raise ValueError('ENERGY_SOURCE_TICK')
        if index and before != visits[index-1]['next']:
            raise ValueError('ENERGY_SOURCE_SPLICE')
        balance = list(map(Fraction, before['energy']))
        for number, row in enumerate(visit['rows']):
            if row['index'] != number:
                raise ValueError('ENERGY_ROW_ORDER')
            debits, credits = map(lambda values: list(map(Fraction, values)),
                                  (row['energyDebit'], row['energyCredit']))
            if len(debits) != 4 or len(credits) != 4 or min(debits+credits) < 0:
                raise ValueError('ENERGY_FLOW_DOMAIN')
            if not row['accepted'] and any(debits+credits):
                raise ValueError('ENERGY_REJECTED_CHARGE')
            if any(debit > available for debit, available in zip(debits, balance)):
                raise ValueError('ENERGY_UNFUNDED_DEBIT')
            balance = [amount-debit+credit for amount,debit,credit in zip(balance,debits,credits)]
        if balance != list(map(Fraction, after['energy'])):
            raise ValueError('ENERGY_MATERIAL_BALANCE')
    if (native['scope']['earliest'] != native['stages'][1]['before']['clock'] or
            Fraction(native['scope']['deadline']) != Fraction(native['scope']['earliest'])+native['scope']['slots'] or
            native['scope']['oldDeadline'] != '22'):
        raise ValueError('ENERGY_SCOPE_ORIGIN')
    if native['epoch'] != {**native['stages'][-1], 'ordinal': native['epoch']['ordinal'],
                          'packets': native['epoch']['packets']}:
        raise ValueError('ENERGY_CURRENT_VISIT')
    return [check_packet(packet, native['scope']) for packet in native['epoch']['packets']]


def expected(config, rows, event, *, native=True):
    argument_value = argument(config, rows, event)
    supplied = event['native']
    checked = check_flows(supplied)
    if supplied['epoch']['ordinal'] != argument_value['ordinal']:
        raise ValueError('ENERGY_ORDINAL')
    if native and canonical(native_call(config, argument_value)) != canonical(supplied):
        raise ValueError('ENERGY_SOURCE_MISMATCH')
    return checked


def produce(config, rows, event):
    event['native'] = native_call(config, argument(config, rows, event))
    expected(config, rows, event)
    return event

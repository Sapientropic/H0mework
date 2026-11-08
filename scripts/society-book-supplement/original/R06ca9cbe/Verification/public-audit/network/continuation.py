"""Recursive paid supply and windows, rebuilt from the original signed journal."""
from fractions import Fraction
from anchor import public_key
from crypto import canonical, digest, verify
import energy
import governance

KIND = 'energy-continuation'
OPS = {'read', 'repair', 'revoke', 'open', 'grant'}


def latest(rows):
    return next((event for event in reversed(energy.events(rows)) if event['type'] == KIND), None)


def successor_scope(config, parent, scope, candidate):
    return digest(dict(descriptor=config['continuation']['descriptor'], parent=parent,
                       previous=scope, candidate=candidate, unit='energy'))


def context(config, rows):
    past = energy.events(rows)
    originals = [event for event in past if event['type'] in energy.KINDS]
    if len(originals) != 2 or past[16:18] != originals:
        raise ValueError('CONTINUATION_ORIGINAL18_REQUIRED')
    old = originals[-1]
    native_argument = energy.argument(config, rows[:17], old)
    phases = [[]]
    scope = originals[0]['scope']
    current = {**old['native']['epoch']['next'], 'cut': old['native']['nextCut']}
    for event in past[18:]:
        if event['type'] != KIND:
            raise ValueError('CONTINUATION_PREFIX_KIND')
        body = event['request']['body']
        phases[-1].append(dict(op=body['op'], query=body['query']))
        current = {**event['native']['next'], 'cut': event['native']['nextCut']}
        if event['native']['nextScope'] is not None:
            phases.append([])
            scope = event['nextScope']
    return native_argument, phases, scope, current


def authorization(config, body, scope):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor',
                                     'cut', 'epoch', 'op', 'query', 'unit')} | {
        'scope': scope, 'descriptor': digest(config['continuation']['descriptor'])}


def argument(config, rows, event):
    body = event['request']['body']
    if event['type'] != KIND or event['request']['kind'] != KIND or body['op'] not in OPS:
        raise ValueError('CONTINUATION_KIND')
    source = config.get('source') or config['streams'][event['stream']]['source']
    parent = dict(seq=len(rows), head=rows[-1][2])
    if (event['source'] != source or body['source'] != source or body['unit'] != 'energy'
            or body['parent'] != parent):
        raise ValueError('CONTINUATION_PARENT_OR_UNIT')
    original, phases, scope, current = context(config, rows)
    if (body['actor'] != str(original['candidate']) or body['scope'] != scope or event['scope'] != scope
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])
            or any(type(body[k]) is not int for k in ('cut', 'epoch'))):
        raise ValueError('CONTINUATION_CURRENT_OR_SCOPE')
    energy.query(body['query'])
    origin = governance.member(config, rows, body['actor'])
    if body['member'] != origin:
        raise ValueError('CONTINUATION_MEMBER')
    registration = next((entry for entry in governance.registered(rows)
                         if entry['result']['key'] == body['executor']), None)
    if registration is None:
        raise ValueError('CONTINUATION_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    signed = verify(public_key(config['ha']['owners'][owner]), 'native-energy-continuation', body['execution'])
    if canonical(signed) != canonical(authorization(config, body, scope)):
        raise ValueError('CONTINUATION_OWNER_AUTHORIZATION')
    phases[-1].append(dict(op=body['op'], query=body['query']))
    return {**original, 'phases': phases}


def native_call(config, value):
    return energy.native_call({**config, 'energy': config['continuation']}, value)


def check_flows(native, current):
    stages = native['stages']
    if not stages or stages[0]['before'] != {k: v for k,v in current.items() if k != 'cut'}:
        raise ValueError('CONTINUATION_ACTUAL_PARENT')
    prior = stages[0]['before']
    for stage in stages:
        before, after = stage['before'], stage['next']
        if before != prior or before['labor'] != after['labor']:
            raise ValueError('CONTINUATION_SOURCE_SPLICE')
        if Fraction(after['clock']) != Fraction(before['clock'])+1 or after['round'] != before['round']+1:
            raise ValueError('CONTINUATION_TICK')
        balance = list(map(Fraction, before['energy']))
        for number, row in enumerate(stage['rows']):
            if type(row['accepted']) is not bool or row['index'] != number:
                raise ValueError('CONTINUATION_ROW')
            debit, credit = [list(map(Fraction, row[key])) for key in ('energyDebit','energyCredit')]
            if len(debit) != 4 or len(credit) != 4 or min(debit+credit) < 0:
                raise ValueError('CONTINUATION_UNIT')
            if not row['accepted'] and any(debit+credit):
                raise ValueError('CONTINUATION_REFUSAL_CHARGED')
            if any(d > b for d,b in zip(debit,balance)):
                raise ValueError('CONTINUATION_UNFUNDED')
            balance = [b-d+c for b,d,c in zip(balance,debit,credit)]
        if balance != list(map(Fraction, after['energy'])):
            raise ValueError('CONTINUATION_BALANCE')
        prior = after
    if (native['next'] != prior or native['before'] != stages[-1]['before']
            or native['rows'] != stages[-1]['rows'] or native['nextCut'] != current['cut']+len(stages)):
        raise ValueError('CONTINUATION_NEXT')
    if native['nextScope'] is not None:
        scope = native['nextScope']
        if (native['reason'] != 'OPENED' or native['next']['holder'] is not None
                or Fraction(scope['earliest']) != Fraction(native['next']['clock'])+1
                or Fraction(scope['deadline']) != Fraction(scope['earliest'])+6
                or Fraction(scope['earliest']) <= Fraction(native['scope']['deadline'])):
            raise ValueError('CONTINUATION_WINDOW_ORIGIN')
    return [energy.check_packet(packet, native['scope']) for packet in native['packets']]


def expected(config, rows, event, *, native=True):
    value = argument(config, rows, event)
    _, _, scope, current = context(config, rows)
    checked = check_flows(event['native'], current)
    expected_scope = (successor_scope(config,event['request']['body']['parent'],scope,value['candidate'])
                      if event['native']['nextScope'] is not None else None)
    if event['nextScope'] != expected_scope:
        raise ValueError('CONTINUATION_NEW_SCOPE_IDENTITY')
    if native and canonical(native_call(config, value)) != canonical(event['native']):
        raise ValueError('CONTINUATION_SOURCE_MISMATCH')
    return checked


def produce(config, rows, event):
    value = argument(config, rows, event)
    event['native'] = native_call(config, value)
    event['nextScope'] = (successor_scope(config,event['request']['body']['parent'],event['scope'],value['candidate'])
                          if event['native']['nextScope'] is not None else None)
    expected(config, rows, event)
    return event

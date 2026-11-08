"""Consume original77 donor production and permission in the original HA journal."""
from fractions import Fraction
import json
from pathlib import Path

from anchor import public_key
from crypto import canonical, digest
import donor_arrival_admission as admission
import energy
import governance

CONTROL = 'donor-extension'
ACTION = 'energy-donor'
KINDS = {CONTROL, ACTION}
_closures = {}


def prefix(rows):
    return dict(seq=len(rows), head=rows[-1][2] if rows else '0'*64)


def authority(config):
    if 'governance_context' in config['semantic']:
        return config
    # Semantic workers receive the existing restricted context of this same journal.
    return {**config, 'streams': {'recovery': {'source': config['source'], 'writer': config['registry']['server']}},
            'semantic': {**config['semantic'], 'governance_context': config}}


def certificate(config, rows, supplied=None):
    settings = config.get('donor')
    admission.require(settings is not None, 'DONOR_NOT_INSTALLED')
    value = config['donor_admission'] if supplied is None else supplied
    admission.require(set(value) == {'point', 'votes', 'permission'}, 'DONOR_CERTIFICATE_FIELDS')
    point = value['point']; cut = point['prefix']['seq']
    admission.require(len(rows) >= cut, 'DONOR_ORIGINAL_PREFIX_MISSING')
    actual = admission.permission(authority(config), rows[:cut], point['program'], value['votes'], value['permission'])
    admission.require(actual == point, 'DONOR_CERTIFICATE_SOURCE')
    descriptor = settings['descriptor']
    admission.require(descriptor['source'] == point['source'] and descriptor['stream'] == point['stream'] and
        descriptor['compiler'] == point['program']['compiler'] and descriptor['source_root'] == admission.ORIGIN and
        descriptor['exporter_sha256'] == point['program']['sources'][admission.EXPORTER], 'DONOR_RUNTIME_PROGRAM')
    identity = (descriptor['closure_sha256'], config['arrival']['descriptor']['closure_sha256'])
    if identity not in _closures:
        baseline_path = Path(config['arrival']['closure']); path = Path(settings['closure'])
        admission.require(admission.sha(baseline_path) == identity[1] and admission.sha(path) == identity[0],
                          'DONOR_RUNTIME_CLOSURE_BYTES')
        objects = value['votes']['a']['body']['objects']
        admission.require(all(v['body']['objects'] == objects for v in value['votes'].values()),
                          'DONOR_UNIFORM_COMPILED_PROFILE')
        inventory = json.loads(baseline_path.read_text()); inventory.update(objects)
        admission.require(json.loads(path.read_text()) == inventory, 'DONOR_COMPLETE_RUNTIME_CLOSURE')
        _closures[identity] = True
    return value


def committed(config, rows):
    found = [(i, json.loads(r[3])['body']) for i, r in enumerate(rows)
             if json.loads(r[3])['body']['type'] == CONTROL]
    admission.require(len(found) <= 1, 'DONOR_DUPLICATE_CONTROL')
    if not found:
        return None
    index, event = found[0]
    value = certificate(config, rows[:index], event['native'])
    admission.require(value == config['donor_admission'] and value['point']['prefix'] == prefix(rows[:index]),
                      'DONOR_COMMITTED_CONTROL_PARENT')
    admission.require(all(json.loads(r[3])['body']['type'] in {ACTION, 'rotation'} for r in rows[index+1:]),
                      'DONOR_PAST_KIND')
    return index, value


def guard(config, rows, event):
    kind = event['type']
    if kind in KINDS:
        admission.require(config.get('donor') is not None, 'DONOR_NOT_INSTALLED')
    active = committed(config, rows)
    if active is not None:
        admission.require(kind in {ACTION, 'rotation'}, 'DONOR_CURRENT_SOURCE_REQUIRED')
    elif kind == ACTION:
        raise ValueError('DONOR_CONTROL_NOT_COMMITTED')


def context(config, rows):
    active = committed(config, rows)
    admission.require(active is not None, 'DONOR_CONTROL_NOT_COMMITTED')
    index, value = active; point = value['point']
    _, request, _ = admission.context(authority(config), rows[:index], point['program'])
    current = dict(point['current']); scope = point['scope']; commands = []
    for offset, row in enumerate(rows[index+1:], index+1):
        event = json.loads(row[3])['body']
        if event['type'] == 'rotation':
            continue
        command = event['request']['body']['command']
        if len(commands) < len(request['commands']):
            admission.require(command == request['commands'][len(commands)] and
                              'continuation' not in event['request']['body'], 'DONOR_AUTHORIZED_WORD')
        else:
            from donor_owner_continuation import _consume_at
            _consume_at(config, rows[:offset], event['request'],
                        dict(mode='donor', base=request['base'], commands=commands), scope, current, request)
        commands.append(command)
        reply = event['native']
        if reply['status'] == 'ERROR':
            continue
        after = reply['next']; delta = Fraction(after['clock'])-Fraction(current['clock'])
        admission.require(delta >= 0 and delta.denominator == 1, 'DONOR_CLOCK_UNIT')
        technology = after['technology']['audit']
        current = dict(clock=after['clock'], cut=current['cut']+int(delta),
                       **{k: technology[k] for k in ('version', 'holder', 'offered')})
        scope = event['nextScope'] or scope
    return dict(mode='donor', base=request['base'], commands=commands), scope, current, request


def request_binding(config, rows, event, current, scope=None):
    body = event['request']['body']; point = config['donor_admission']['point']
    admission.require(event['request']['kind'] == event['type'] and
        event['source'] == body['source'] == point['source'] and
        event['stream'] == body['stream'] == point['stream'] and body['parent'] == prefix(rows) and
        body['executor'] == point['executor'] and body['member'] == governance.member(config, rows, body['actor']) and
        body['cut'] == current['cut'] and body['epoch'] == current['version'] and
        body['certificate'] == digest(config['donor_admission']), 'DONOR_CURRENT_AUTHORIZATION')
    if scope is not None:
        admission.require(event['scope'] == body['scope'] == scope and body['unit'] == 'energy' and
                          body['source_root'] == admission.ORIGIN, 'DONOR_CURRENT_SCOPE')


def argument(config, rows, event):
    value, scope, current, plan = context(config, rows)
    request_binding(config, rows, event, current, scope)
    body = event['request']['body']; index = len(value['commands'])
    admission.require(type(body['index']) is int and body['index'] == index, 'DONOR_AUTHORIZED_WORD')
    if index < len(plan['commands']):
        admission.require(body['command'] == plan['commands'][index] and 'continuation' not in body,
                          'DONOR_AUTHORIZED_WORD')
    else:
        from donor_owner_continuation import _consume_at
        _consume_at(config, rows, event['request'], value, scope, current, plan)
    value['commands'].append(body['command'])
    return value


def native_call(config, value):
    return energy.native_call({**config, 'energy': config['donor']}, value)


def scope_id(config, parent, scope):
    return digest(dict(descriptor=config['donor']['descriptor'], parent=parent, scope=scope))


def expected(config, rows, event, *, native=True):
    from source_extension import guard as original_guard
    original_guard(config, rows, event)
    if event['type'] == CONTROL:
        admission.require(set(event) == {'type', 'source', 'stream', 'request', 'peer', 'native'},
                          'DONOR_CONTROL_FIELDS')
        value = certificate(config, rows, event['native'])
        admission.require(value == config['donor_admission'] and value['point']['prefix'] == prefix(rows),
                          'DONOR_CONTROL_PARENT')
        request_binding(config, rows, event, value['point']['current'])
        return value
    admission.require(event['type'] == ACTION and set(event) ==
        {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}, 'DONOR_COMMAND_FIELDS')
    value = argument(config, rows, event); reply = event['native']; command = value['commands'][-1]
    admission.require(isinstance(reply, dict) and reply.get('metadata') == command and
                      reply.get('status') in {'SUPPLIED','STALE','WITHHELD','WRONG_SIGNER','MATERIAL','SOURCE_LAW',
                          'PRODUCED','OPENED','DELIVERED','CONTINUED','BLOCKED','ERROR'}, 'DONOR_REPLY')
    next_scope = scope_id(config, event['request']['body']['parent'], reply['nextScope']) if reply.get('opening') else None
    admission.require(event['nextScope'] == next_scope, 'DONOR_GENERATED_SCOPE')
    if native:
        admission.require(canonical(native_call(config, value)) == canonical(reply), 'DONOR_ACTUAL_SOURCE_MISMATCH')
    return reply


def produce(config, rows, event):
    if event['type'] == CONTROL:
        event['native'] = config['donor_admission']
    else:
        event['native'] = native_call(config, argument(config, rows, event))
        event['nextScope'] = (scope_id(config, event['request']['body']['parent'], event['native']['nextScope'])
                              if event['native'].get('opening') else None)
    expected(config, rows, event)
    return event

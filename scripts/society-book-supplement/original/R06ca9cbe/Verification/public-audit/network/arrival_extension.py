"""Admit the original provider-material arrival as a successor of production."""
import json
import re

from anchor import public_key
from crypto import canonical, digest, verify
import productive_extension

EVENT = 'arrival-extension'
FEATURE = 'energy-arrival'
READY = 'native-arrival-extension-ready'
ORIGIN = 'provider-material-3/native-export-6/v1'


def point(config, prefix):
    parent = productive_extension.admission(config)
    descriptor = config['arrival']['descriptor']
    if (descriptor['source'], descriptor['stream'], descriptor['compiler'], descriptor['source_root']) != (
            parent['source'], parent['stream'], parent['descriptor']['compiler'], ORIGIN):
        raise ValueError('ARRIVAL_DESCRIPTOR')
    if (set(prefix) != {'seq', 'head'} or type(prefix['seq']) is not int
            or prefix['seq'] <= 54 or prefix['seq'] <= parent['prefix']['seq']
            or type(prefix['head']) is not str or re.fullmatch('[0-9a-f]{64}', prefix['head']) is None):
        raise ValueError('ARRIVAL_PREFIX')
    return dict(version=1, feature=FEATURE, parent=digest(config['productive_extension']),
                source=parent['source'], stream=parent['stream'], cluster=parent['cluster'],
                prefix=prefix, descriptor=descriptor)


def admission(config, certificate=None):
    certificate = config['arrival_extension'] if certificate is None else certificate
    if set(certificate) != {'point', 'votes'}:
        raise ValueError('ARRIVAL_CERTIFICATE')
    value = certificate['point']
    if value != point(config, value['prefix']):
        raise ValueError('ARRIVAL_CERTIFICATE_BINDING')
    settings = config['arrival']; backend = settings['backend']
    if (len(backend) != 6 or backend[-1] != 'private-one'
            or settings.get('private_variant', 'private-one') != 'private-one'
            or 'private_exporter' in settings):
        raise ValueError('ARRIVAL_PUBLIC_SOURCE')
    members = []; probes = []
    for vote in certificate['votes']:
        if set(vote) != {'member', 'receipt'} or vote['member'] not in config['ha']['trust']['members']:
            raise ValueError('ARRIVAL_VOTE')
        member = vote['member']
        body = verify(public_key(config['ha']['trust']['members'][member]), READY, vote['receipt'])
        if (body['point'] != value or body['member'] != member or body['legacy_prefix'] != value['prefix']
                or body['compiler'] != value['descriptor']['compiler']
                or not body['legacy_backend'] or not body['source_backend']
                or set(body['probe']) != {'input', 'output'}
                or any(not isinstance(item, str) or re.fullmatch('[0-9a-f]{64}', item) is None
                       for item in body['probe'].values())):
            raise ValueError('ARRIVAL_READY')
        members.append(member); probes.append(body['probe'])
    if members != list('abcd') or any(probe != probes[0] for probe in probes[1:]):
        raise ValueError('ARRIVAL_LOCAL_KERNEL_COVERAGE')
    return value


def committed(config, rows):
    active = None
    for index, row in enumerate(rows):
        event = json.loads(row[3])['body']
        if event['type'] == EVENT:
            if active is not None:
                raise ValueError('ARRIVAL_DUPLICATE')
            certificate = event['native']; value = admission(config, certificate)
            prefix = dict(seq=index, head=rows[index-1][2] if index else '0'*64)
            if value['prefix'] != prefix or row[1] != prefix['head']:
                raise ValueError('ARRIVAL_COMMITTED_PARENT')
            if value['parent'] != digest(productive_extension.require(config, rows[:index])[1]):
                raise ValueError('ARRIVAL_ACTUAL_PARENT_CERTIFICATE')
            active = (row[0], certificate)
        elif active is not None and event['type'] not in {FEATURE, 'rotation', 'donor-extension', 'energy-donor'}:
            raise ValueError('ARRIVAL_PAST_KIND')
    return active


def require(config, rows):
    value = committed(config, rows)
    if value is None:
        raise ValueError('ARRIVAL_NOT_COMMITTED')
    return value


def guard(config, rows, event):
    from source_extension import guard as source_guard
    source_guard(config, rows, event)
    active = committed(config, rows)
    if event['type'] in {EVENT, FEATURE} and not config.get('arrival'):
        raise ValueError('ARRIVAL_NOT_INSTALLED')
    if event['type'] == EVENT and active is not None:
        raise ValueError('ARRIVAL_DUPLICATE')
    if event['type'] == FEATURE and active is None:
        raise ValueError('ARRIVAL_NOT_COMMITTED')
    if active is not None and event['type'] not in {FEATURE, 'rotation', 'donor-extension', 'energy-donor'}:
        raise ValueError('ARRIVAL_QUERY_REQUIRED')


def authorization(body):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                      'cut', 'epoch', 'feature', 'certificate')}


def expected(config, rows, event):
    import governance
    import productive_regeneration
    from source_extension import guard as source_guard
    source_guard(config, rows, event)
    body = event['request']['body']; value = admission(config, event['native'])
    prefix = dict(seq=len(rows), head=rows[-1][2] if rows else '0'*64)
    if value['parent'] != digest(productive_extension.require(config, rows)[1]):
        raise ValueError('ARRIVAL_ACTUAL_PARENT_CERTIFICATE')
    if (set(event) != {'type', 'source', 'stream', 'request', 'peer', 'native'}
            or event['type'] != EVENT or event['request']['kind'] != EVENT
            or value['prefix'] != prefix or body['parent'] != prefix
            or event['source'] != value['source'] or body['source'] != value['source']
            or event['stream'] != value['stream'] or body['stream'] != value['stream']
            or body['feature'] != FEATURE or body['certificate'] != digest(event['native'])):
        raise ValueError('ARRIVAL_ADMISSION_EVENT')
    _, _, current = productive_regeneration.context(config, rows)
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])
            or body['member'] != governance.member(config, rows, body['actor'])):
        raise ValueError('ARRIVAL_CURRENT_MEMBER')
    registration = next((entry for entry in governance.registered(rows)
                         if entry['result']['key'] == body['executor']), None)
    if registration is None:
        raise ValueError('ARRIVAL_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    actual = verify(public_key(config['ha']['owners'][owner]), 'native-arrival-extension', body['execution'])
    if actual != authorization(body):
        raise ValueError('ARRIVAL_OWNER_AUTHORIZATION')
    return value


def produce(config, rows, event):
    event['native'] = config['arrival_extension']
    expected(config, rows, event)
    return event

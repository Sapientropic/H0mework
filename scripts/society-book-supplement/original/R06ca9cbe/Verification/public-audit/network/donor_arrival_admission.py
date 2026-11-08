"""Original77 donor readiness and owner permission for a future HA control event."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path

import anchor
from crypto import canonical, digest, sign, verify
import arrival_extension
import arrival_regeneration
import productive_owner_request as owner
import source_readiness

READY = 'actual77-donor-native-ready'
PERMIT = 'actual77-donor-control-permit'
ORIGIN = 'original-target-donor/feed6/v1'
STEM = 'SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Regeneration/Supply/Material/Productive/'
MODULES = [STEM + 'DonorRelease.lean'] + [STEM + 'ExternalArrival/Donor/' + n + '.lean' for n in ('Source', 'Consumer', 'Wire')]
EXPORTER = 'scripts/verification/public-donor-arrival-source.lean'
CHECKER = 'scripts/verification/public-actual77-donor-check.py'


def require(value, reason):
    if not value:
        raise ValueError(reason)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def programs(root, config):
    root = Path(root)
    return dict(sources={p: sha(root / 'Lean' / p) for p in MODULES + [EXPORTER, CHECKER]},
                compiler=config['arrival']['descriptor']['compiler'],
                consumer=sha(root/'Verification/public-audit/network/verify.py'),
                readiness=sha(root/'Verification/public-audit/network/donor_arrival_admission.py'),
                worker=sha(root/'Lean/scripts/verification/public-donor-arrival-ready.py'))


def context(config, rows, program):
    actors, _, _ = owner.history(config, rows)
    registration = owner.registration(config, rows)
    activated, certificate = arrival_extension.require(config, rows)
    require(len(rows) == 77 and activated == 69, 'DONOR_ACTUAL77_PREFIX')
    require(set(program) == {'sources', 'compiler', 'consumer', 'readiness', 'worker'} and
            set(program['sources']) == set(MODULES + [EXPORTER, CHECKER]) and
            program['compiler'] == config['arrival']['descriptor']['compiler'], 'DONOR_PROGRAM')
    base, scope, current = arrival_regeneration.context(config, rows)
    base.pop('mode')
    old = [json.loads(row[3])['body']['native'] for row in rows[activated:]
           if json.loads(row[3])['body']['type'] == arrival_regeneration.KIND]
    require(len(old) == 8 and old[-1]['spent'] is True and
            old[-1]['sourceNext']['available'] == '0', 'DONOR_OLD_EXHAUSTED')
    round_ = old[-1]['next']['round']
    commands = [dict(kind='cycle', mode='normal'),
        dict(kind='donate', round=round_+2, signer=3, enabled=False, quantity=6),
        dict(kind='donate', round=round_+4, signer=0, enabled=True, quantity=6),
        dict(kind='donate', round=round_+6, signer=3, enabled=True, quantity=6),
        dict(kind='donate', round=round_+6, signer=3, enabled=True, quantity=6),
        *[dict(kind='cycle', mode='normal') for _ in range(3)],
        *[dict(kind='service', query=dict(slots=63, fields=3)) for _ in range(2)],
        dict(kind='arrival', quantity=3),
        dict(kind='donate', round=round_+20, signer=3, enabled=True, quantity=39)]
    request = dict(base=base, commands=commands)
    trust = config['ha']['trust']
    require(set(trust['members']) == set('abcd') and
            len({i['app'] for i in trust['members'].values()}) == 4, 'DONOR_FOUR_IDENTITIES')
    require(registration['result']['key'] == config['ha']['owners']['spark']['app'], 'DONOR_ORIGINAL_OWNER')
    point = dict(schema='actual77-donor-admission/v1', source_root=ORIGIN,
        source=config['streams']['recovery']['source'], stream='recovery',
        prefix=dict(seq=len(rows), head=rows[-1][2]), history=digest(rows),
        parent=digest(certificate), cluster=config['cluster'], members=deepcopy(trust),
        executor=registration['result']['key'], owner='spark', actors=actors,
        source_input=digest(request), old_output=digest(old), program=deepcopy(program),
        scope=scope, current=current, quantity=6, unit='feed', donor='audit:3', recipient='audit:0',
        requires=dict(readiness=list('abcd'), ha_intent_quorum=3, ha_commit_quorum=3, exact_parent=True))
    return point, request, old


def inspect_trace(root, output, request, old):
    path = Path(root) / 'Lean' / CHECKER
    spec = importlib.util.spec_from_file_location('actual77_donor_consumer', path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker.replay(output, request, old)


def ready(config, rows, program, member, output, objects, key):
    point, request, _ = context(config, rows, program)
    require(member in point['members']['members'] and
            key.public_key().public_bytes_raw().hex() == point['members']['members'][member]['app'], 'DONOR_READY_SIGNER')
    require(set(objects) == {str(Path(p).with_suffix('.olean')) for p in MODULES}, 'DONOR_LOCAL_OBJECTS')
    return sign(key, READY, dict(point=point, member=member, input=digest(request), output=digest(output),
        objects=objects, disposition='native-readiness-only', original_database_writes=0))


def consume(config, rows, program, votes):
    point, request, _ = context(config, rows, program)
    require(set(votes) == set('abcd'), 'DONOR_FOUR_NATIVE_REQUIRED')
    outputs = set()
    for member in 'abcd':
        fact = verify(anchor.public_key(point['members']['members'][member]), READY, votes[member])
        require(set(fact) == {'point', 'member', 'input', 'output', 'objects', 'disposition', 'original_database_writes'} and
                fact['point'] == point and fact['member'] == member and fact['input'] == digest(request) and
                fact['original_database_writes'] == 0 and fact['disposition'] == 'native-readiness-only' and
                set(fact['objects']) == {str(Path(p).with_suffix('.olean')) for p in MODULES} and
                all(isinstance(h, str) and len(h) == 64 and all(c in '0123456789abcdef' for c in h)
                    for h in [fact['output'], *fact['objects'].values()]), 'DONOR_READY_BINDING')
        outputs.add(fact['output'])
    require(len(outputs) == 1, 'DONOR_NATIVE_DISAGREEMENT')
    return point


def authorize(config, rows, program, votes, key):
    point = consume(config, rows, program, votes)
    require(key.public_key().public_bytes_raw().hex() == point['executor'], 'DONOR_OWNER_SIGNER')
    return sign(key, PERMIT, dict(point=point, readiness=digest(votes),
        disposition='prepared-for-original77-control-admission'))


def permission(config, rows, program, votes, permit):
    point = consume(config, rows, program, votes)
    body = verify(anchor.public_key(config['ha']['owners']['spark']), PERMIT, permit)
    require(body == dict(point=point, readiness=digest(votes),
        disposition='prepared-for-original77-control-admission'), 'DONOR_OWNER_PERMISSION')
    return point

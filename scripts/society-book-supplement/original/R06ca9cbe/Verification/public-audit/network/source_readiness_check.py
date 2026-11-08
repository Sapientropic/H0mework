"""Consume a local readiness vote by replaying its literal journal and probe."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import time

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

import anchor
from crypto import canonical, digest, sign, verify
from online_privacy import source_input
import source_readiness as producer


def consume(config, rows, prefix, vote, argument, result):
    member = vote['member']; identity = config['ha']['trust']['members'][member]
    if identity != config['registry']['anchor']:
        raise ValueError('READY_LOCAL_SIGNER')
    body = verify(anchor.public_key(identity), producer.KIND, vote['receipt'])
    if (body['member'] != member or body['point'] != producer.point(config, prefix)
            or body['compiler'] != body['point']['descriptor']['compiler']
            or body['legacy_prefix'] != prefix):
        raise ValueError('READY_SOURCE_BINDING')
    previous = '0' * 64
    for index, row in enumerate(rows, 1):
        seq, before, head, text, receipt = row
        message = json.loads(text)
        event = verify(anchor.public_key(config['streams'][body['point']['stream']]['writer']), 'ledger', message)
        if (event['source'], event['stream']) != (body['point']['source'], body['point']['stream']):
            raise ValueError('READY_LEDGER_NAMESPACE')
        if seq != index or before != previous or head != anchor.ledger_hash(before, message):
            raise ValueError('READY_CHAIN')
        anchor.verify_commit(identity, json.loads(receipt), source=event['source'], stream=event['stream'],
                            seq=seq, head=head, previous=before, message=message, cluster=config['cluster'])
        previous = head
    if prefix != dict(seq=len(rows), head=previous):
        raise ValueError('READY_PREFIX')
    if body['journal'] != digest(rows):
        raise ValueError('READY_JOURNAL_DIGEST')
    # The issuer uses handoff.context; the consumer reconstructs the last actual
    # event through the original online input decoder and its owner checks.
    event = json.loads(rows[-1][3])['body']
    expected = dict(mode='regeneration', base=source_input(config, [row[:4] for row in rows[:-1]], event),
                    requests=[dict(query={'slots': 63, 'fields': 3}, mode='normal')])
    if canonical(argument) != canonical(expected):
        raise ValueError('READY_INPUT_ORIGIN')
    if body['probe'] != dict(input=digest(argument), output=digest(result)):
        raise ValueError('READY_LITERAL_DIGEST')
    if result['status'] != 'OPENED' or result['opening'] is not True or result['metadata'] != argument['requests'][0]:
        raise ValueError('READY_OPENING')
    for field in ('legacy_backend', 'source_backend'):
        backend = body[field]
        if (set(backend) != {'pid', 'birth', 'pgid', 'boot'} or type(backend['pid']) is not int
                or backend['pid'] <= 0 or backend['pgid'] != backend['pid']
                or not backend['birth'] or not backend['boot']):
            raise ValueError('READY_WORKER_OCCURRENCE')
    return body


def controls(config, rows, prefix, vote, argument, result):
    accepted = []
    def reject(label, *, c=None, r=None, p=None, v=None, a=None, o=None, reason=None):
        try:
            consume(c if c is not None else config, r if r is not None else rows,
                    p if p is not None else prefix, v if v is not None else vote,
                    a if a is not None else argument, o if o is not None else result)
        except (ValueError, KeyError, TypeError, IndexError, InvalidSignature) as error:
            if reason is not None and str(error) != reason and type(error).__name__ != reason:
                raise AssertionError('WRONG_CONTROL_GATE:' + label) from error
            accepted.append(label)
        else:
            raise AssertionError('CONTROL_ACCEPTED:' + label)
    bad = copy.deepcopy(vote); bad['receipt']['signature'] = 'AA=='
    reject('forged-signature', v=bad)
    bad = copy.deepcopy(vote); bad['member'] = next(m for m in config['ha']['trust']['members'] if m != vote['member'])
    reject('wrong-signer', v=bad)
    bad = copy.deepcopy(vote); bad['receipt'] = sign(Ed25519PrivateKey.generate(), producer.KIND, vote['receipt']['body'])
    reject('unregistered-key', v=bad)
    bad = copy.deepcopy(vote); bad['receipt']['kind'] = 'native-source-ready'
    reject('old-ready-kind', v=bad)
    reject('expired-parent-replay', p=dict(seq=prefix['seq'] + 1, head='f' * 64))
    bad = copy.deepcopy(config); bad['regeneration']['descriptor']['exporter_sha256'] = 'f' * 64
    reject('different-program', c=bad)
    bad = copy.deepcopy(config); del bad['native_admission']['votes'][-1]
    reject('missing-parent-admission', c=bad)
    reject('deleted-receipt-row', r=rows[:-1], reason='READY_PREFIX')
    bad = copy.deepcopy(rows); bad[0][-1] = '{}'
    reject('deleted-commit-signature', r=bad, reason='MESSAGE_KIND')
    bad = copy.deepcopy(rows); message = json.loads(bad[0][3]); message['signature'] = 'AA=='
    bad[0][3] = canonical(message).decode()
    reject('forged-ledger-signature', r=bad, reason='InvalidSignature')
    bad = copy.deepcopy(rows); receipt = json.loads(bad[0][-1]); receipt['signature'] = 'AA=='
    bad[0][-1] = canonical(receipt).decode()
    reject('forged-commit-signature', r=bad, reason='InvalidSignature')
    bad = copy.deepcopy(rows); bad[-1][-1] = rows[0][-1]
    reject('duplicate-historical-receipt', r=bad)
    bad = copy.deepcopy(argument); bad['requests'][0]['query']['slots'] = 0
    reject('different-probe-input', a=bad)
    bad = copy.deepcopy(result); bad['status'] = 'BLOCKED'; bad['opening'] = False
    reject('blocked-as-opening', o=bad)
    bad = copy.deepcopy(result); del bad['next']
    reject('deleted-generated-next', o=bad)
    bad = copy.deepcopy(vote); del bad['receipt']['body']['legacy_backend']
    reject('deleted-replay-occurrence', v=bad)
    # Use the real new admission consumer when installed by its owning thread.
    import source_extension
    certificate = dict(point=vote['receipt']['body']['point'], votes=[vote])
    if source_extension.point(config, prefix) != certificate['point']:
        raise AssertionError('ADMISSION_POINT_DIVERGED')
    for label, votes in [('single-vote-is-not-admission', [vote]), ('duplicate-vote-is-not-quorum', [vote] * 4)]:
        try:
            source_extension.admission({**config, 'source_extension': {**certificate, 'votes': votes}})
        except ValueError as error:
            if str(error) != 'SOURCE_EXTENSION_COVERAGE':
                raise
            accepted.append(label)
        else:
            raise AssertionError('CONTROL_ACCEPTED:' + label)
    return accepted


def check(config, evidence, output):
    evidence = Path(evidence).resolve(); output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    config = producer.isolated(config, output)
    member, live_rows, prefix = producer.snapshot(config)
    rows = json.loads((evidence / 'rows.json').read_text())
    if rows != [list(row) for row in live_rows]:
        raise ValueError('READY_ORIGINAL_JOURNAL_REQUIRED')
    vote = json.loads((evidence / 'vote.json').read_text())
    argument = json.loads((evidence / 'input.json').read_text())
    result = json.loads((evidence / 'output.json').read_text())
    body = consume(config, rows, prefix, vote, argument, result)
    negatives = controls(config, rows, prefix, vote, argument, result)
    legacy = producer.LocalEngine(config['semantic']); source = producer.LocalEngine(config['regeneration'])
    try:
        legacy.sync([row[:4] for row in rows], deadline=time.monotonic() + 300)
        legacy_status = legacy.status()
        if legacy_status['prefix'] != prefix or not legacy_status['backend']:
            raise ValueError('READY_INDEPENDENT_LEGACY')
        source.start()
        actual = source.call(argument, time.monotonic() + 300)
        if canonical(actual) != canonical(result):
            raise ValueError('READY_INDEPENDENT_SOURCE')
        independent = source.status()['backend']
        if independent['pid'] == body['source_backend']['pid'] and independent['birth'] == body['source_backend']['birth']:
            raise ValueError('READY_INDEPENDENT_PROCESS')
        if producer.snapshot(config) != (member, live_rows, prefix):
            raise ValueError('READY_PREFIX_MOVED')
        report = dict(member=member, prefix=prefix, signed_rows=len(rows),
                      native_probe=body['probe'], independent_backend=independent,
                      legacy_backend=legacy_status['backend'], controls=negatives,
                      scope='one local readiness vote; no admission, event, lease or decision installed')
    finally:
        producer.close_all(source, legacy)
    producer.save(output / 'acceptance.json', report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('config', 'evidence', 'output'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    report = check(json.loads(Path(args.config).read_text()), args.evidence, args.output)
    print('INDEPENDENT SOURCE READINESS PASS ' + json.dumps(report))


if __name__ == '__main__':
    main()

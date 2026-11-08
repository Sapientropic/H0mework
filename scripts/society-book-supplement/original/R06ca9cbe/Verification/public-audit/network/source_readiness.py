"""Produce one local source-extension vote from the original signed journal.

This command never installs a certificate or appends an event. Its only signer
is the anchor identity already bound in the local journal.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import time

import anchor
from crypto import app_private, canonical, digest, sign
import energy
import governance
import handoff
import native_spare
from quorum import membership
from source_semantics import Engine

KIND = 'native-source-extension-ready'
FEATURE = 'energy-regeneration'
FACADE = ('SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.'
          'Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Wire.publicReadout')


def sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def save(path, value):
    # A failed attempt cannot overwrite a previously issued vote.
    with Path(path).open('x') as stream:
        stream.write(canonical(value).decode() + '\n')


def prepare(config, setup, exporter, output, fallback=()):
    """Bind the existing Lean import artifacts to a path-independent descriptor."""
    parent = native_spare.admission(config)
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    library = output / 'lib'; library.mkdir()
    inventory, artifacts, modules = {}, {}, {}
    for module, groups in json.loads(Path(setup).read_text())['importArts'].items():
        if any(not part or '/' in part or '\\' in part for part in module.split('.')):
            raise ValueError('SOURCE_MODULE_NAME')
        stem = Path(*module.split('.'))
        for group in groups:
            for filename in group:
                original = Path(filename).resolve(strict=True)
                suffix = original.name[len(stem.name):]
                if suffix not in {'.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig'}:
                    raise ValueError('SOURCE_ARTIFACT_KIND')
                relative = str(stem) + suffix
                if relative in artifacts:
                    raise ValueError('SOURCE_ARTIFACT_DUPLICATE')
                artifacts[relative] = original
                if suffix == '.olean': modules[module] = original
    helper = Path(__file__).resolve().parents[3] / 'Lean/scripts/verification/source-readiness-imports.lean'
    tool = config['semantic']['backend'][0]
    sysroot = Path(subprocess.check_output([tool, '--print-prefix'], text=True).strip()) / 'lib/lean'
    roots = [Path(path).resolve(strict=True) for path in fallback] + [sysroot]
    pending, seen = dict(modules), set()
    while pending:
        batch = dict(pending); pending = {}
        result = subprocess.run([tool, '--trust=0', '-j1', '--run', str(helper)],
            input=''.join(str(path) + '\n' for path in batch.values()), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True, timeout=120)
        imports = [json.loads(line) for line in result.stdout.splitlines()]
        if len(imports) != len(batch): raise ValueError('SOURCE_IMPORT_SCAN')
        seen.update(batch)
        for names in imports:
            for module in names:
                if module in seen or module in pending: continue
                if module not in modules:
                    relative = Path(*module.split('.')).with_suffix('.olean')
                    original = next((root / relative for root in roots if (root / relative).is_file()), None)
                    if original is None: raise ValueError('SOURCE_TRANSITIVE_IMPORT:' + module)
                    modules[module] = original
                    for suffix in ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig'):
                        sibling = original.with_name(original.stem + suffix)
                        if sibling.is_file(): artifacts[str(relative.with_suffix(suffix))] = sibling
                pending[module] = modules[module]
    for relative, original in artifacts.items():
        target = library / relative; target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(original)
        inventory[relative] = sha(original)
    required = FACADE.rsplit('.', 1)[0].replace('.', '/') + '.olean'
    if required not in inventory:
        raise ValueError('SUPPLY_WIRE_REQUIRED')
    save(output / 'closure.json', inventory)
    original_exporter = Path(exporter).resolve(strict=True)
    exporter = output / original_exporter.name
    with exporter.open('xb') as stream: stream.write(original_exporter.read_bytes())
    descriptor = dict(source=parent['source'], stream=parent['stream'],
                      compiler=parent['descriptors']['base']['compiler'], facade=FACADE,
                      exporter_sha256=sha(exporter), closure_sha256=sha(output / 'closure.json'))
    value = copy.deepcopy(config)
    value['regeneration'] = dict(descriptor=descriptor, exporter=str(exporter),
        closure=str(output / 'closure.json'), lean_path=str(library), cwd=str(exporter.parent),
        backend=[config['semantic']['backend'][0], '--trust=0', '-j1', '--run', str(exporter), 'private-one'],
        error_log=str(output / 'source.log'))
    save(output / 'candidate.json', value)
    return value


def snapshot(config):
    parent = native_spare.admission(config)
    if config['cluster'] != membership(config['ha']['trust']):
        raise ValueError('SOURCE_CLUSTER')
    members = [name for name, identity in config['ha']['trust']['members'].items()
               if identity == config['registry']['anchor']]
    if len(members) != 1:
        raise ValueError('SOURCE_LOCAL_IDENTITY')
    binding = dict(streams=config['streams'], identity=config['registry']['anchor'], cluster=config['cluster'])
    if 'transport_writer' in config:
        binding['transport_writer'] = config['transport_writer']
    path = Path(config['database']).resolve(strict=True)
    with sqlite3.connect(path.as_uri() + '?mode=ro', uri=True) as db:
        db.execute('PRAGMA query_only=ON'); db.execute('BEGIN')
        if db.execute('SELECT value FROM binding').fetchall() != [(canonical(binding).decode(),)]:
            raise ValueError('SOURCE_JOURNAL_BINDING')
        if db.execute('SELECT value FROM native_admission').fetchall() != [(canonical(config['native_admission']).decode(),)]:
            raise ValueError('SOURCE_PARENT_CERTIFICATE')
        rows = db.execute('SELECT seq,previous,hash,message,receipt FROM entries WHERE stream=? ORDER BY seq',
                          (parent['stream'],)).fetchall()
    previous = '0' * 64
    validator = object.__new__(anchor.Journal); validator.config = config
    for index, (seq, before, head, text, receipt) in enumerate(rows, 1):
        message = json.loads(text)
        validator.validate_message(parent['stream'], message)
        if seq != index or before != previous or anchor.ledger_hash(before, message) != head:
            raise ValueError('SOURCE_JOURNAL_CHAIN')
        anchor.verify_commit(config['registry']['anchor'], json.loads(receipt), source=parent['source'],
            stream=parent['stream'], seq=seq, head=head, previous=before, message=message, cluster=config['cluster'])
        previous = head
    cut = parent['prefix']['seq']
    if len(rows) < cut or rows[cut-1][2] != parent['prefix']['head']:
        raise ValueError('SOURCE_PARENT_PREFIX')
    return members[0], rows, dict(seq=len(rows), head=previous)


def point(config, prefix):
    parent = native_spare.admission(config); descriptor = config['regeneration']['descriptor']
    if (descriptor['source'], descriptor['stream'], descriptor['compiler']) != (
            parent['source'], parent['stream'], parent['descriptors']['base']['compiler']):
        raise ValueError('SOURCE_EXTENSION_DESCRIPTOR')
    if descriptor['facade'] != FACADE or 'private_exporter' in config['regeneration']:
        raise ValueError('SOURCE_PUBLIC_PROGRAM')
    exporter = Path(__file__).resolve().parents[3] / 'Lean/scripts/verification/public-supply-network-source.lean'
    if descriptor['exporter_sha256'] != sha(exporter):
        raise ValueError('SOURCE_PUBLIC_EXPORTER')
    return dict(version=1, feature=FEATURE, parent=digest(config['native_admission']), source=parent['source'],
                stream=parent['stream'], cluster=parent['cluster'], prefix=prefix, descriptor=descriptor)


def probe(config, rows):
    if not rows or json.loads(rows[-1][3])['body']['type'] != 'energy-handoff':
        raise ValueError('SOURCE_HANDOFF_ENDPOINT_REQUIRED')
    base, _, _ = handoff.context(config, rows)
    return dict(mode='regeneration', base={'mode': 'handoff', **base},
                requests=[dict(query={'slots': 63, 'fields': 3}, mode='normal')])


def isolated(config, output):
    value = copy.deepcopy(config)
    def visit(item):
        if isinstance(item, dict):
            if 'error_log' in item:
                item['error_log'] = str(Path(output) / ('worker-' + digest(item['descriptor']) + '.log'))
            for child in item.values():
                visit(child)
        elif isinstance(item, list):
            for child in item:
                visit(child)
    visit(value)
    return value


def stop(engine):
    process = engine.process
    if process is not None and process.poll() is None:
        process.stdin.close()
        try: process.wait(timeout=3)
        except subprocess.TimeoutExpired: pass
    engine.close()


class LocalEngine(Engine):
    def close(self):
        # EOF is the worker protocol's normal shutdown, including parse errors.
        process = self.process
        if process is not None and process.poll() is None:
            process.stdin.close()
            try: process.wait(timeout=3)
            except subprocess.TimeoutExpired: pass
        super().close()


def close_all(*engines):
    engines = [*engines, *governance._readers.values(), *energy._readers.values()]
    failures = []
    for engine in engines:
        try: stop(engine)
        except (OSError, subprocess.SubprocessError) as error: failures.append(error)
    governance._readers.clear()
    energy._readers.clear(); energy._cache.clear()
    if failures: raise failures[0]


def issue(config, output, seconds=300):
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    config = isolated(config, output)
    member, signed_rows, prefix = snapshot(config)
    value = point(config, prefix)
    rows = [row[:4] for row in signed_rows]
    argument = probe(config, rows)
    settings = dict(config['regeneration'])
    if settings['backend'][-1] != 'private-one' or settings.get('private_variant', 'private-one') != 'private-one':
        raise ValueError('SOURCE_PUBLIC_BRANCH')
    key = app_private(Path(config['pki']) / 'anchor')
    if key.public_key().public_bytes_raw().hex() != config['registry']['anchor']['app']:
        raise ValueError('SOURCE_SIGNER')
    legacy = LocalEngine(config['semantic']); source = LocalEngine(settings)
    try:
        legacy.sync(rows, deadline=time.monotonic() + seconds)
        old = legacy.status()
        if old['prefix'] != prefix or not old['backend']:
            raise ValueError('SOURCE_LEGACY_REPLAY')
        source.start()
        result = source.call(argument, time.monotonic() + seconds)
        new = source.status()
        if not new['backend'] or result.get('status') != 'OPENED' or result.get('opening') is not True:
            raise ValueError('SOURCE_PROBE_DID_NOT_OPEN')
        if snapshot(config) != (member, signed_rows, prefix):
            raise ValueError('SOURCE_PREFIX_MOVED')
        body = dict(point=value, member=member, compiler=value['descriptor']['compiler'], legacy_prefix=prefix,
                    probe=dict(input=digest(argument), output=digest(result)), legacy_backend=old['backend'],
                    source_backend=new['backend'], journal=digest(signed_rows), at=time.time())
    finally:
        close_all(source, legacy)
    vote = dict(member=member, receipt=sign(key, KIND, body))
    save(output / 'input.json', argument); save(output / 'output.json', result)
    save(output / 'rows.json', signed_rows); save(output / 'vote.json', vote)
    return vote


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='op', required=True)
    pack = sub.add_parser('prepare')
    pack.add_argument('--setup', required=True); pack.add_argument('--exporter', required=True)
    pack.add_argument('--fallback-library', action='append', default=[])
    for command in (pack, sub.add_parser('issue')):
        command.add_argument('--config', required=True); command.add_argument('--output', required=True)
    args = parser.parse_args(); config = json.loads(Path(args.config).read_text())
    if args.op == 'prepare':
        value = prepare(config, args.setup, args.exporter, args.output, args.fallback_library)
        print(json.dumps(dict(prepared=value['regeneration']['descriptor'])))
    else:
        vote = issue(config, args.output)
        print(json.dumps(dict(member=vote['member'], prefix=vote['receipt']['body']['legacy_prefix'],
                              kind=KIND, probe=vote['receipt']['body']['probe'])))


if __name__ == '__main__':
    main()

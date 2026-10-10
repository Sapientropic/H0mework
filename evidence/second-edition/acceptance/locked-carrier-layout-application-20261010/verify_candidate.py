from pathlib import Path
import copy
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tools'))
import first_release as fr
import source_view as sv

sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
write = lambda path, data: path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def main():
    parity = json.loads((BASE / 'recursive-producer-parity.json').read_bytes())
    assert parity['ok'] and len(parity['pairs']) == 20
    assert all(pair['equal'] and pair['resource_rewrites_equal'] for pair in parity['pairs'])
    ex = json.loads((ROOT / 'tools/export-map.json').read_bytes())
    rows = {row['target']: row for row in ex['modules']}
    inverse = dict(rows)
    target = ('H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.'
              'LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMSourceLockedCarrier')
    row = rows[target]
    before = (ROOT / row['path']).read_bytes()
    assert sha(ROOT / row['path']) == row['target_sha256']
    old_import = ('H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.'
                  'LowEnergyPhenomenology.AlphaSource.SourceLockedFieldReturn')
    new_import = ('H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.'
                  'LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFieldReturn')
    assert row['import_map'][old_import] == 'SourceLockedFieldReturn'
    prior = sv.module_views(row, inverse)
    forward = {module: (new_import if module == old_import else module)
               for _, _, module in sv.import_tokens(before.decode())}
    candidate = sv.transform(before.decode(), sv.import_tokens(before.decode()), forward)
    assert candidate != before
    backward = {module: (old_import if module == new_import else module)
                for _, _, module in sv.import_tokens(candidate.decode())}
    assert sv.transform(candidate.decode(), sv.import_tokens(candidate.decode()), backward) == before
    new_row = copy.deepcopy(row)
    new_row['target_sha256'] = hashlib.sha256(candidate).hexdigest()
    new_row['import_map'][new_import] = new_row['import_map'].pop(old_import)
    shadow = BASE / 'candidate-root'
    shadow_path = shadow / row['path']
    shadow_path.parent.mkdir(parents=True, exist_ok=True)
    shadow_path.write_bytes(candidate)
    sv.ROOT = shadow
    try:
        assert sv.module_views(new_row, inverse) == prior
    finally:
        sv.ROOT = ROOT
    out = fr.new_output(ROOT, BASE / 'environment-verification-62da11e0')
    src, lib = out / 'src', out / 'lib'
    src.mkdir()
    lib.mkdir()
    relative = Path(target.replace('.', '/')).with_suffix('.lean')
    candidate_path = src / relative
    candidate_path.parent.mkdir(parents=True)
    candidate_path.write_bytes(candidate)
    reserved = relative.with_suffix('.olean')
    ancestors = set(reserved.parents)
    def link_cache(public, private, relative=Path('.')):
        private.mkdir(exist_ok=True)
        for child in public.iterdir():
            part = relative / child.name
            if part.parent == reserved.parent and child.name.startswith(reserved.stem + '.'):
                continue
            dest = private / child.name
            if part in ancestors:
                link_cache(child, dest, part)
            else:
                dest.symlink_to(child, target_is_directory=child.is_dir())
    link_cache(ROOT / 'Lean/.lake/build/lib/lean', lib)
    canonical_pole = new_import.rsplit('.', 1)[0] + '.CanonicalPreparationSourceLockedPoleCurrent'
    expected = [
        ('LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceRestLockedMixing', canonical_pole),
        ('LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.actualRestState_locked_current', canonical_pole),
        ('LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceLockedField', new_import),
        ('LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceLockedField_lorentz', new_import),
        ('LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceLockedField_connection', new_import),
    ]
    imports = [module for _, _, module in sv.import_tokens(candidate.decode())]
    pairs = '[' + ', '.join('(' + json.dumps(name) + ', ' + json.dumps(owner) + ')' for name, owner in expected) + ']'
    probe = src / 'CanonicalLockedPayers.lean'
    probe.write_text(''.join('import ' + module + '\n' for module in imports) +
                     'import Lean\nset_option autoImplicit false\nopen Lean Elab Command\nrun_cmd do\n'
                     '  let env ← getEnv\n  for (text, owner) in ' + pairs + ' do\n'
                     '    let name := text.toName\n'
                     '    let some info := env.find? name | throwError "Missing original payer {name}"\n'
                     '    let some index := env.getModuleIdxFor? name | throwError "Missing owner {name}"\n'
                     '    unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong owner {name}"\n'
                     '    unless (info.value? true).isSome do throwError "Missing original value {name}"\n'
                     '    logInfo m!"OWNER {name} = {env.header.moduleNames[index]!}"\n'
                     '    logInfo m!"TYPE {name} = {info.type}"\n')
    original_text = before.decode()
    opening = original_text[original_text.index('set_option autoImplicit'):original_text.index('/-- The three original')]
    opening = opening.replace('namespace LowEnergy.GaussComposite.ActualEMSourceDirection',
                              'namespace LowEnergy.GaussComposite.IndependentLockedConsumer')
    opening += 'open LowEnergy.GaussComposite.ActualEMSourceDirection\n'
    consumer = src / 'IndependentLockedConsumer.lean'
    text = 'import ' + target + '\n' + opening
    statements = [('locked_amplitude_lorentz_read', 'mu n i'),
                  ('locked_actual_background', 'n point'),
                  ('locked_actual_charged_read', '')]
    for name, arguments in statements:
        assert original_text.count('theorem ' + name) == 1
        statement = original_text.split('theorem ' + name, 1)[1].split(' :=', 1)[0]
        text += 'example' + statement + ' := ' + name + ' ' + arguments + '\n\n'
    text += 'end LowEnergy.GaussComposite.IndependentLockedConsumer\n'
    for name, _ in statements:
        text += '#print axioms LowEnergy.GaussComposite.ActualEMSourceDirection.' + name + '\n'
    consumer.write_text(text)
    plan_path = ROOT / '.local/physics-acceptance-20261010/physics-runtime-overlap-plan-62da11e0.json'
    plan = json.loads(plan_path.read_bytes())
    paths = {path for packet in plan['packages'] if packet['id'].startswith('v2-9c73-')
             and packet['id'] in ('v2-9c73-prepared-actual', 'v2-9c73-signal-field',
                                  'v2-9c73-prepared-actual-certification-consumers',
                                  'v2-9c73-signal-field-certification-consumers')
             for path in packet['source_files']}
    paths.update({'Lean/lean-toolchain', 'Lean/lakefile.toml', 'Lean/lake-manifest.json',
                  'tools/source_view.py', Path(__file__).relative_to(ROOT).as_posix(),
                  (BASE / 'recursive-producer-parity.json').relative_to(ROOT).as_posix()})
    paths.update(path.relative_to(ROOT).as_posix() for path in (candidate_path, probe, consumer))
    def capture():
        return {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'files': {path: sha(ROOT / path) for path in sorted(paths)}}
    before_identity = capture()
    assert before_identity['head'] == '62da11e06ce55da48c1d8e6b8be8bd6047040eae'
    write(out / 'input-before.json', before_identity)
    (out / 'invocation-source.py').write_bytes(Path(__file__).read_bytes())
    settings = fr.settings(ROOT)
    flags = list(dict.fromkeys(settings['package_moreLeanArgs'] + settings['package_weakLeanArgs'] +
                               ['--trust=0', '-DwarningAsError=true']))
    env = fr.build_environment()
    assert env['LEAN_NUM_THREADS'] == '2'
    original_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT / 'Lean', text=True).strip()
    env['LEAN_PATH'] = str(lib) + ':' + original_path
    steps = []
    def execute(name, source, object_path):
        command = ['lean', '--root=' + str(src), *flags, str(source), '-o', str(object_path)]
        write(out / (name + '-command.json'), {'command': command, 'cwd': 'Lean', 'LEAN_NUM_THREADS': '2',
                                               'LEAN_PATH': env['LEAN_PATH'], 'settings': settings})
        start = time.monotonic()
        object_path.parent.mkdir(parents=True, exist_ok=True)
        log = out / (name + '.log')
        with log.open('x') as stream:
            process = subprocess.Popen(command, cwd=ROOT / 'Lean', env=env, stdout=stream, stderr=subprocess.STDOUT)
            write(out / 'handle.json', {'controller_pid': os.getpid(), 'lean_pid': process.pid, 'step': name})
            status = process.wait()
        step = {'name': name, 'exit_code': status, 'elapsed_seconds': round(time.monotonic() - start, 3),
                'command': command, 'source_sha256': sha(source), 'log_sha256': sha(log),
                'object_sha256': sha(object_path) if object_path.exists() else None}
        steps.append(step)
        write(out / 'steps.json', steps)
        print(json.dumps(step), flush=True)
        return status == 0
    ok = execute('actual-canonical-locked-payers', probe, out / 'payers.olean')
    if ok:
        ok = execute('complete-original-locked-carrier', candidate_path, lib / reserved)
    if ok:
        ok = execute('original-locked-statement-consumer', consumer, out / 'consumer.olean')
    after_identity = capture()
    write(out / 'input-after.json', after_identity)
    result = {'schema': 'h0mework/private-one-import-locked-carrier-verification@1',
              'ok': ok and before_identity == after_identity, 'inputs_unchanged': before_identity == after_identity,
              'formal_acceptance': False, 'original_source_sha256': row['source_sha256'],
              'before_target_sha256': row['target_sha256'], 'after_target_sha256': new_row['target_sha256'],
              'full_original_and_public_inverse_exact': True, 'candidate_row': new_row,
              'old_import': old_import, 'new_import': new_import, 'steps': steps,
              'source_options': [line for line in original_text.splitlines() if line.startswith('set_option ')],
              'recursive_parity_sha256': sha(BASE / 'recursive-producer-parity.json'),
              'private_source_files': len(paths)}
    write(out / 'result.json', result)
    print(json.dumps({'ok': result['ok'], 'inputs_unchanged': result['inputs_unchanged'], 'steps': len(steps)}), flush=True)
    return 0 if result['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

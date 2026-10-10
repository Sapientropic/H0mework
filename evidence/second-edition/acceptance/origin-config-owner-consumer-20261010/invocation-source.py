from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tools'))
import first_release as release


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def main():
    plan_path = BASE / 'plan.json'
    plan = json.loads(plan_path.read_bytes())
    row = next(row for row in plan['rows'] if '/R71e/' in row['path'])
    graph_path = BASE.parent / 'low-repair-current-plan-b0374cd0-preview/plan.json'
    graph = json.loads(graph_path.read_bytes())['graph']
    pending, reached = [row['target']], set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(graph[module])
    settings = release.settings(ROOT)
    flags = list(dict.fromkeys(settings['package_moreLeanArgs'] + settings['package_weakLeanArgs']
                               + ['--trust=0', '-DwarningAsError=true']))
    out = release.new_output(ROOT, BASE / 'environment-verification-b0374cd0')
    src, lib = out / 'src', out / 'lib'
    src.mkdir()
    lib.mkdir()
    raw = (ROOT / row['path']).read_text()
    candidate = src / Path(row['target'].replace('.', '/')).with_suffix('.lean')
    candidate.parent.mkdir(parents=True)
    candidate.write_bytes((ROOT / row['candidate_path']).read_bytes())
    reserved = Path(row['target'].replace('.', '/')).with_suffix('.olean')
    ancestors = set(reserved.parents)

    def link_cache(public, private, relative=Path('.')):
        private.mkdir(exist_ok=True)
        for child in public.iterdir():
            rel = relative / child.name
            if rel.parent == reserved.parent and child.name.startswith(reserved.stem + '.'):
                continue
            dest = private / child.name
            if rel in ancestors:
                link_cache(child, dest, rel)
            else:
                dest.symlink_to(child, target_is_directory=child.is_dir())

    link_cache(ROOT / 'Lean/.lake/build/lib/lean', lib)
    owner = row['provider_module']
    probe = src / 'OriginalPoleScaleOwner.lean'
    probe.write_text('import ' + row['canonical_import_shim'] + '''
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted := `LowEnergy.PreparationVacuumPoleConstraintReturn.source_scale
  let owner := "''' + owner + '''"
  let candidates := env.constants.toList.filter fun (name, _) => privateToUserName name == wanted
  logInfo m!"ALL {wanted}: {candidates.map Prod.fst}"
  let exact := candidates.filter fun (name, _) => name.toString.startsWith ("_private." ++ owner ++ ".")
  unless exact.length == 1 do throwError "Expected one actual canonical producer: {exact.map Prod.fst}"
  let (name, info) := exact[0]!
  let some index := env.getModuleIdxFor? name | throwError "No checked module for {name}"
  unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong owner for {name}"
  let some value := info.value? true | throwError "No checked value for {name}"
  logInfo m!"OWNER {name} MODULE {env.header.moduleNames[index]!}"
  logInfo m!"TYPE {name} = {info.type}"
  logInfo m!"VALUE {name} = {value}"
''')
    opening = raw[:raw.index('open Lean Elab Term in')]
    opening = opening[opening.index('set_option autoImplicit'):]
    opening = opening.replace('local instance OriginPotentialIndex', 'local instance IndependentOriginPotentialIndex')
    opening = opening.replace('local instance : Fintype', 'local instance IndependentOriginPotentialFintype : Fintype')
    name = 'sourceOriginConfigurationAmplitude_read'
    assert raw.count('theorem ' + name + ' ') == 1
    statement = raw.split('theorem ' + name, 1)[1].split(' := by', 1)[0]
    consumer = src / 'IndependentOriginConfigurationConsumer.lean'
    consumer.write_text('import ' + row['target'] + '\n' + opening + '\nexample' + statement
                        + ' := ' + name + ' q n l r\n'
                        + 'end LowEnergy.PreparationPhysicalOriginConfigurationReturn\n'
                        + '#print axioms LowEnergy.PreparationPhysicalOriginConfigurationReturn.' + name + '\n')
    marker_path = BASE.parent / 'cohort-freeze.json'
    marker = json.loads(marker_path.read_bytes())
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert marker['head'] == head == 'b0374cd097caa2d92987dacbb5ea20b08c780dc6'
    inputs = set(marker['files']) | {release.module_path(module) for module in reached}
    inputs.update(str(path.relative_to(ROOT)) for path in (plan_path, candidate, probe, consumer, Path(__file__)))

    def capture():
        return {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'files': {path: sha(ROOT / path) for path in sorted(inputs)}, 'settings': release.settings(ROOT)}

    before = capture()
    assert all(before['files'][path] == digest for path, digest in marker['files'].items())
    assert before['files'][row['path']] == row['before_target_sha256']
    write(out / 'input-before.json', before)
    (out / 'invocation-source.py').write_bytes(Path(__file__).read_bytes())
    original_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT / 'Lean', text=True).strip()
    environment = dict(os.environ, LEAN_NUM_THREADS='2', LEAN_PATH=str(lib) + ':' + original_path)
    steps = []

    def execute(label, path, object_path):
        command = ['lean', '--root=' + str(src), *flags, str(path), '-o', str(object_path)]
        write(out / (label + '-command.json'), {'argv': command, 'cwd': 'Lean', 'LEAN_NUM_THREADS': '2',
                                              'LEAN_PATH': environment['LEAN_PATH'], 'settings': settings})
        begin = time.monotonic()
        log = out / (label + '.log')
        object_path.parent.mkdir(parents=True, exist_ok=True)
        with log.open('x') as stream:
            process = subprocess.Popen(command, cwd=ROOT / 'Lean', env=environment, stdout=stream, stderr=subprocess.STDOUT)
            write(out / 'handle.json', {'controller_pid': os.getpid(), 'lean_pid': process.pid, 'step': label})
            code = process.wait()
        step = {'name': label, 'exit_code': code, 'elapsed_seconds': round(time.monotonic() - begin, 3),
                'command': command, 'source_sha256': sha(path), 'log_sha256': sha(log),
                'object_sha256': sha(object_path) if object_path.is_file() else None}
        steps.append(step)
        write(out / 'steps.json', steps)
        print(json.dumps({key: step[key] for key in ['name', 'exit_code', 'elapsed_seconds']}), flush=True)
        return code == 0

    ok = execute('actual-original-pole-scale-owner', probe, out / 'owner.olean')
    if ok:
        ok = execute('complete-origin-configuration-candidate', candidate, lib / reserved)
    if ok:
        ok = execute('independent-original-amplitude-consumer', consumer, out / 'consumer.olean')
    after = capture()
    write(out / 'input-after.json', after)
    result = {'schema': 'h0mework/private-origin-config-canonical-owner-verification@1',
              'formal_acceptance': False, 'ok': ok and before == after, 'inputs_unchanged': before == after,
              'head_before': before['head'], 'head_after': after['head'], 'source_modules': len(reached),
              'source_identity': {key: row[key] for key in ['source_path', 'source_revision', 'source_revisions', 'source_sha256']},
              'provider_module': owner, 'provider_source_sha256': row['provider_source_sha256'],
              'candidate_public_sha256': sha(candidate), 'settings': settings, 'lean_num_threads': 2,
              'statement_unchanged': True, 'budget_change': False, 'steps': steps}
    write(out / 'result.json', result)
    print(json.dumps({'ok': result['ok'], 'inputs_unchanged': result['inputs_unchanged'], 'steps': len(steps)}), flush=True)
    return 0 if result['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

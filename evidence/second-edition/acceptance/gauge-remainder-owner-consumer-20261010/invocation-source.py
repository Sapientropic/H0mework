from pathlib import Path
import hashlib
import json
import os
import re
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
    row = next(r for r in plan['rows'] if '/R9c73a630/' in r['path'])
    graph_path = BASE.parent / 'joint-price-membership-72d341e7/reused-and-gap-import-graph.json'
    graph = json.loads(graph_path.read_bytes())
    pending, reached = [row['target']], set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(graph[module])
    assert row['provider_module'] in reached
    settings = release.settings(ROOT)
    flags = list(dict.fromkeys(settings['package_moreLeanArgs'] + settings['package_weakLeanArgs']
                               + ['--trust=0', '-DwarningAsError=true']))
    out = release.new_output(ROOT, BASE / 'environment-verification-62da11e0')
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
    probe = src / 'OriginalChannelLinearOwner.lean'
    probe.write_text('import ' + row['canonical_import_shim'] + '''
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted := `LowEnergy.PreparationVacuumChargedLongRangeRead.linear_matrix
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
    counter = [0]

    def named_instance(match):
        counter[0] += 1
        return 'local instance IndependentGaugeRemainderInstance' + str(counter[0]) + ' :'

    opening = re.sub(r'local instance\s*:', named_instance, opening)
    statements = [
        ('sourceFirstLiteralField_generated', 'v row'),
        ('sourceFirstModeRemainder_original', 'imaginary omega k c'),
        ('sourceFirstModeRemainder_connection', 'imaginary omega k c x mu'),
    ]
    consumer_text = 'import ' + row['target'] + '\n' + opening
    statement_hashes = {}
    for name, args in statements:
        assert raw.count('theorem ' + name + ' ') == 1
        statement = raw.split('theorem ' + name, 1)[1].split(' := by', 1)[0]
        statement_hashes[name] = hashlib.sha256(statement.encode()).hexdigest()
        consumer_text += '\nexample' + statement + ' := ' + name + ' ' + args + '\n'
    consumer_text += '\nend LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder\n'
    for name, _ in statements:
        consumer_text += '#print axioms LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder.' + name + '\n'
    consumer = src / 'IndependentGaugeRemainderConsumer.lean'
    consumer.write_text(consumer_text)
    marker_path = BASE.parent / 'cohort-freeze.json'
    marker = json.loads(marker_path.read_bytes())
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert marker['head'] == head == '62da11e06ce55da48c1d8e6b8be8bd6047040eae'
    inputs = set(marker['files']) | {release.module_path(m) for m in reached}
    inputs.update(str(p.relative_to(ROOT)) for p in (plan_path, candidate, probe, consumer, Path(__file__)))
    for r in plan['rows']:
        inputs.update([r['path'], r['candidate_path'], r['provider_path'], release.module_path(r['canonical_import_shim'])])

    def capture():
        return {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'files': {p: sha(ROOT / p) for p in sorted(inputs)}, 'settings': release.settings(ROOT)}

    before = capture()
    assert all(before['files'][p] == digest for p, digest in marker['files'].items())
    assert all(before['files'][r['path']] == r['before_target_sha256'] for r in plan['rows'])
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
        print(json.dumps({k: step[k] for k in ['name', 'exit_code', 'elapsed_seconds']}), flush=True)
        return code == 0

    ok = execute('actual-original-channel-linear-owner', probe, out / 'owner.olean')
    if ok:
        ok = execute('complete-gauge-remainder-candidate', candidate, lib / reserved)
    if ok:
        ok = execute('independent-original-gauge-remainder-consumer', consumer, out / 'consumer.olean')
    after = capture()
    write(out / 'input-after.json', after)
    result = {'schema': 'h0mework/private-gauge-remainder-canonical-owner-verification@1',
              'formal_acceptance': False, 'ok': ok and before == after, 'inputs_unchanged': before == after,
              'head_before': before['head'], 'head_after': after['head'], 'source_modules': len(reached),
              'source_identity': {k: row[k] for k in ['source_path', 'source_revision', 'source_revisions', 'source_sha256']},
              'provider_module': owner, 'provider_source_sha256': row['provider_source_sha256'],
              'candidate_public_sha256': sha(candidate), 'settings': settings, 'lean_num_threads': 2,
              'statement_unchanged': True, 'statement_sha256': statement_hashes, 'budget_change': False, 'steps': steps}
    write(out / 'result.json', result)
    print(json.dumps({'ok': result['ok'], 'inputs_unchanged': result['inputs_unchanged'], 'steps': len(steps)}), flush=True)
    return 0 if result['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

"""Audit frozen key actor wiring and reporting ABI without activating its source."""
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

from check_content_full_kernel import DEPENDENCIES
from check_c3_integer_kernel import run, sha

HERE = Path(__file__).resolve().parent
OWNED = HERE.parent
REPO = OWNED.parents[2]
OUT = HERE/'.cache/c3-native-key-actor-audit'
COMPILER = OWNED/'.cache/C3/native-key-compiler600-attempt6'
CAPTURED = OWNED/'.cache/C3/resident-published-compiler-400'
RECOVERY = OWNED/'.cache/C3/resident-published-compiler-400-attempt2'
FILES = ['C3NativeMetrics.lean','C3NativeSourceReadout.lean','C3NativeKeyActor.lean',
         'C3NativeMetrics.c','C3NativeKeyActor.py']
PREFIX = 'SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.'
ROOTS = [PREFIX+'C3NativeSourceReadout.'+name for name in ['restore','originalRows','imageBytes']]+[
    'FlyCNS.C3NativeKeyActor.'+name for name in ['read500','recordImage','verifyImage','verifyClocks',
    'saveEvent','verifyActualRows','produce','run','resourceSample','begin','finish']]+[
    'FlyCNS.C3NativeMetrics.sample','main']
CONTROLS = r'''
namespace NativeKeyActorAuditControls
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open FlyCNS C3FiniteOccurrence C3NativeMinimum
variable (source : ContentReentryIO.Source)
example (restored : C3NativeSourceReadout.RestoredAt source) :
    ContentReentryIO.capture restored.current=ContentReentryIO.capture restored.original.next :=
  restored.sourceSame.trans restored.originalSame
example (restored : C3NativeSourceReadout.RestoredAt source) : restored.current.tick=400 := restored.tick
example (restored : C3NativeSourceReadout.RestoredAt source) : restored.current.visit=4 := restored.visit
example (recorded : C3NativeKeyActor.Recorded500 source) : recorded.current.tick=500 := recorded.tick
example (recorded : C3NativeKeyActor.Recorded500 source) : recorded.current.visit=5 := recorded.visit
example (recorded : C3NativeKeyActor.Recorded500 source) :
    ContentReentryIO.physicsTick source.material recorded.current.words=5000 := recorded.physics
variable {boundary : Boundary} (context : C3NativeCodec.Seal boundary) (installed : Installed boundary)
example (key : C3NativeCodec.Key context) : C3NativeCodec.parse context (C3NativeCodec.encode context key)=.ok key :=
  C3NativeCodec.parse_encode context key
example (cache : C3NativeCodec.ErrorCache context installed) (before : Ready boundary installed context.anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current) :
    (C3NativeCodec.savePublished context installed cache before event).bytes.size=8 :=
  C3NativeCodec.savedPublished_size context installed cache before event
end NativeKeyActorAuditControls
'''


def load(path): return json.loads(path.read_text())


def static_scope():
    source = (OWNED/'C3NativeSourceReadout.lean').read_text()
    old = (OWNED/'C3ContinuationAttempt2.lean').read_text()
    assert source[source.index('structure RestoredAt'):source.index('def imageBytes')] == \
        old[old.index('structure RestoredAt'):old.index('def save {')]
    assert source[source.index('def imageBytes'):source.index('\n\nend C3NativeSourceReadout')].strip() == \
        old[old.index('def imageBytes'):old.index('/-- The emitted occurrence')].strip()
    actor = (OWNED/'C3NativeKeyActor.lean').read_text()
    assert actor.count('let source ← reopenSource') == 1
    assert actor.count('← ContentReentryRoot.emitPublished') == 1
    assert actor.count('← BodyIO.checkedResult (C3NativeCodec.restore context bound') == 2
    assert 'saveAddress' not in actor
    read500 = actor[actor.index('def read500'):actor.index('def recordImage')]
    assert 'emitPublished' not in read500 and 'PublishedAt' not in read500 and '← generate' not in read500
    assert 'minimum-consumed-source-held' in read500 and 'rows != recordedRows 4 5 400 500 5000' in read500
    assert 'let saved:=C3NativeCodec.savePublished context bound cache before event' in actor
    assert 'for observer in List.finRange 69' in actor
    assert 'capture after.current.current != capture event.original.next' in actor
    held = actor[actor.index('structure HeldKey'):actor.index('/-- The comparison phase')]
    assert all(token in held for token in ['boundary : Boundary','context : C3NativeCodec.Seal boundary',
        'installed : Installed boundary','errors : C3NativeCodec.ErrorCache context installed','bytes : ByteArray'])
    assert all(token not in held for token in ['Snapshot','Recorded500','PublishedAt','target','actual'])
    assert 'return ⟨boundary,context,bound,saved.errors,bytes6⟩' in actor
    run_part = actor[actor.index('def run :'):actor.index('end FlyCNS.C3NativeKeyActor')]
    assert 'C3NativeCodec.restore' not in run_part and 'emitPublished' not in run_part
    assert 'let held ← produce' in run_part and 'source600-restored.json' not in run_part
    metrics = (OWNED/'C3NativeMetrics.c').read_text()
    assert 'lean_obj_res flycns_c3_process_metrics(void)' in metrics
    assert 'return lean_mk_string(text);' in metrics
    assert 'lean_io_result_mk_ok' not in metrics and 'lean_io_result_mk_error' not in metrics
    function = metrics[metrics.index('LEAN_EXPORT lean_obj_res'):]
    assert all(word not in function for word in ['flycns_c3_bulk','callback','generate','Source'])
    tree = ast.parse((OWNED/'C3NativeKeyActor.py').read_text())
    funcs = {n.name:n for n in tree.body if isinstance(n,ast.FunctionDef)}
    assert set(['original_binding','prepare','previous_completed','supervise','launch']) <= set(funcs)
    py = (OWNED/'C3NativeKeyActor.py').read_text()
    assert "lines = (COMPILER / 'commands.txt').read_text().splitlines()" in py
    assert "{'read', 'quit'}" in py and "actor.stdin.write" in py
    assert "new_source_births': 0" in py and 'start_new_session=True' in py
    assert py.count('subprocess.Popen(') == 2
    assert 'libproved-bulk.dylib' in py and 'libsource-metrics.dylib' in py
    return {'original400_restore_and_rows_literal_reuse': True,
        'existing500_save': 'Current/trace readout, no reconstructed PublishedAt',
        'decoder_inputs': 'original resident Source/installation/Anchor400/past error cache/key; no target input',
        'source_calls': 'one same-source reopen and one original emitPublished500→600',
        'cold_decoder_reexecutions': 'one pure macro for key5, two for key6',
        'same_event600_savePublished_zero_extra_F_and_full69_whole_next': True,
        'HeldKey_drops_comparison_targets_at_produce_return': True,
        'resource_scope': 'process RSS/VM and malloc-zone counters, resident references during validation',
        'reporting_ABI_isolated_from_numerical_Source_authority': True}


def provenance():
    binding = load(COMPILER/'binding.json')
    original = load(CAPTURED/'binding.json'); recovery = load(RECOVERY/'binding.json')
    assert binding['original_capture_binding_sha256'] == sha(CAPTURED/'binding.json')
    assert recovery['original_binding_sha256'] == sha(CAPTURED/'binding.json')
    assert binding['held_source500_programme'] == original['prebirth_source_sha256']
    assert binding['numerical_library_sha256'] == sha(CAPTURED/'libproved-bulk.dylib') == original['library_sha256']
    for key, directory in [('prebirth_source_sha256',CAPTURED), ('prebirth_recovery_source_sha256',RECOVERY)]:
        report = original if directory == CAPTURED else recovery
        for name, digest in report[key].items():
            assert sha(directory/'programme'/name) == sha(OWNED/name) == digest, name
    for name,digest in original['compiled_ABI_sources'].items(): assert sha(CAPTURED/name) == digest
    for name,digest in binding['prebirth_new_source_sha256'].items():
        assert sha(COMPILER/'programme'/name) == sha(OWNED/name) == digest, name
    assert sha(COMPILER/'metrics-generated.c') == binding['metrics_generated_wrapper_sha256']
    assert sha(COMPILER/'libsource-metrics.dylib') == binding['metrics_library_sha256']
    assert sha(COMPILER/'dependency-closure.json') == binding['dependency_closure_sha256']
    closure = load(COMPILER/'dependency-closure.json')
    for row in closure: assert sha(Path(row['path'])) == row['sha256'], row['path']
    return {'prebirth_binding_sha256': sha(COMPILER/'binding.json'),
        'original17_and_recovery_and_ABI_unchanged': True,
        'captured_new_sources': binding['prebirth_new_source_sha256'],
        'all_registered_dependency_files_checked': len(closure),
        'metrics_library_sha256': binding['metrics_library_sha256'],
        'original_numerical_library_sha256': binding['numerical_library_sha256']}


def main():
    expected = {}
    for name in FILES:
        raw = subprocess.check_output(['git','show','15177f8f68:Lean/scratch/FlyCNS/'+name],cwd=REPO)
        assert (OWNED/name).read_bytes() == raw, name
        expected[name] = hashlib.sha256(raw).hexdigest()
    scope, captured = static_scope(), provenance()
    overlay = OUT/'scratch/FlyCNS'; overlay.mkdir(parents=True,exist_ok=True)
    for cache in [HERE/'.cache/c3-native-key-codec-audit', OWNED/'.cache/content-full']:
        for source in (cache/'scratch/FlyCNS').glob('*.olean'):
            target = overlay/source.name
            if source.stem not in {Path(n).stem for n in FILES[:3]} and not target.exists(): target.symlink_to(source)
    env = os.environ.copy(); lake = shutil.which('lake'); assert lake
    lean = run([lake,'env','which','lean'],env)
    env['LEAN_PATH'] = str(OUT)+os.pathsep+run([lake,'env','printenv','LEAN_PATH'],env)
    wrapper = OUT/'metrics-generated.c'
    for name in FILES[:3]:
        command = [lean,'--trust=0','-DwarningAsError=true','-o',str(overlay/(Path(name).stem+'.olean'))]
        if name == 'C3NativeMetrics.lean': command += ['-c',str(wrapper)]
        run(command+['scratch/FlyCNS/'+name],env,OUT/(name+'.log'))
    assert wrapper.read_bytes() == (COMPILER/'metrics-generated.c').read_bytes()
    run([lean,'--trust=0','-DwarningAsError=true','--plugin='+str(COMPILER/'libsource-metrics.dylib')+
        '=initialize_scratch_FlyCNS_C3NativeMetrics','scratch/FlyCNS/C3NativeMetrics.lean'],env,OUT/'metrics-plugin-elaboration.log')
    controls = OUT/'Controls.lean'; controls.write_text('import scratch.FlyCNS.C3NativeKeyActor\nset_option autoImplicit false\n'+CONTROLS)
    run([lean,'--trust=0','-DwarningAsError=true',str(controls)],env,OUT/'controls.log')
    dependencies = DEPENDENCIES.replace('(env.getModuleFor? name)',
        '((env.getModuleIdxFor? name).map (fun index => env.header.moduleNames[index.toNat]!))')
    target = OUT/'KernelAudit.lean'; log = OUT/'dependencies.log'
    target.write_text('import scratch.FlyCNS.C3NativeKeyActor\nset_option autoImplicit false\n'+dependencies+'\n'+
        '\n'.join('#print axioms '+root+'\n#content_full_dependencies '+root for root in ROOTS)+'\n')
    run([lean,'--trust=0','-DwarningAsError=true',str(target)],env,log)
    sizes, axioms = {}, {}
    for line in log.read_text().splitlines():
        if line.startswith('CONTENT_FULL_DEP\t'):
            _,root,name,_,_,kind = line.split('\t')
            if kind == 'axiom': axioms.setdefault(root,set()).add(name)
        elif line.startswith('CONTENT_FULL_DONE\t'):
            _,root,count = line.split('\t'); sizes[root] = int(count)
    assert set(sizes) == set(ROOTS)
    for name,digest in expected.items(): assert sha(OWNED/name) == digest, name
    result = {'schema':'flycns-c3-preinstalled-key-actor-independent-kernel-certification/v1',
        'candidate_commit':'15177f8f68','candidate_sha256':expected,
        'fresh_modules':3,'focused_controls':CONTROLS.count('example '),
        'complete_dependency_closures':len(ROOTS),'trust':0,'warning_as_error':True,
        'no_project_axiom_unsafe_sorry_control_dependency':True,
        'wiring':scope,'provenance':captured,'fresh_reporting_ABI_wrapper_byte_equal':True,
        'reporting_plugin_elaboration_without_metrics_or_Source_execution':True,
        'mouths':{root:{'dependencies':sizes[root],'axioms':sorted(axioms.get(root,[]))} for root in ROOTS},
        'Source_commands':0,'NN_updates':0,'physics_updates':0,'graph_loads':0,
        'actual_cold_decoder_source600_or_resource_result_certified':False,
        'scope':'preinstalled source-owned codec400/current500 readout/cold5/source600 same-event key/cold6/full69 and whole-next runtime contract, local target lifetimes and isolated reporting ABI; actual terminal results separately certified'}
    (HERE/'c3-native-key-actor-kernel-summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'fresh_modules':3,'controls':result['focused_controls'],'closures':len(ROOTS),
        'ABI_wrapper_same':True,'Source_NN_physics_graph_updates':0}))


if __name__ == '__main__': main()

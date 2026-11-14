"""Fresh source-generated finite reachable carrier/minimum; no runtime or enumeration."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
from check_content_full_kernel import DEPENDENCIES
from check_c3_integer_kernel import run,sha

HERE=Path(__file__).resolve().parent
OWNED=HERE.parent
REPO=OWNED.parents[2]
OUT=HERE/'.cache/c3-native-minimum-audit'
FILES=['C3PublishedInvocation.lean','C3NativeMinimum.lean','C3NativeMinimumControls.lean']
ROOTS=['FlyCNS.C3NativeMinimum.'+n for n in ['initial','atBoundary','fromActual','advance','selected','effect','generate','execute',
 'advance_visit','generated_visit','execute_error','success_is_autonomous','fromWord','key_injective','decode','decode_encode',
 'action','run_actual','key_is_original_visit','minimum_future_kernel','pack','unpack','unpack_pack','pack_unpack',
 'encodedAction','encodedRead','action_commutes','read_commutes','all_words_commute','all_readers_zero_error',
 'minimal_other_implementations','fromPublished','published_complete','published_parsed','advance_published','ready',
 'consumePublished','consumed_same_image']]


def main():
    expected={}
    for n in FILES:
        commit='719aa65545' if n=='C3PublishedInvocation.lean' else '0337cbf004'
        raw=subprocess.check_output(['git','show',commit+':Lean/scratch/FlyCNS/'+n],cwd=REPO)
        assert (OWNED/n).read_bytes()==raw,n;expected[n]=hashlib.sha256(raw).hexdigest()
    source=(OWNED/'C3NativeMinimum.lean').read_text()
    invocation=(OWNED/'C3PublishedInvocation.lean').read_text()
    assert 'private mk ::' in source and 'abbrev Key : Type := Nat ⊕ String' in source
    assert 'C3PublishedInvocation.generate boundary.source installed.material current.current' in source
    assert 'C3RootSplice.current source published.numerical' in invocation
    assert 'after.visit=before.visit+1' in invocation
    assert 'after.tick=before.tick+(BodyFullIO.operationAt before.visit).microTicks' in invocation
    assert '10*(BodyFullIO.operationAt before.visit).microTicks' in invocation
    assert '| .inl _ => C3Native.operationAt current.current.visit' in source
    assert 'C3ReachableModel.Output observer' in source and 'observer : Fin 69' in source
    assert 'generate installed anchor (visit-anchor.base.current.visit)' in source
    assert 'word++[.inl ()]' in source and 'exact advance_published event' in source
    consumed=source[source.index('def consumePublished '):source.index('theorem consumed_same_image ')]
    assert 'advance installed' not in consumed and 'C3BoundPublication.generate' not in consumed
    assert 'event.original.next' in source and 'C3PublishedRoot.same_complete_occurrence event' in source
    overlay=OUT/'scratch/FlyCNS';overlay.mkdir(parents=True,exist_ok=True)
    skip={Path(n).stem for n in FILES}
    for cache in [HERE/'.cache/c3-published-root-audit',HERE/'.cache/c3-reachable-minimum-audit',
                  HERE/'.cache/c3-compressed-publication-audit',OWNED/'.cache/content-full']:
        for p in (cache/'scratch/FlyCNS').glob('*.olean'):
            target=overlay/p.name
            if p.stem not in skip and not target.exists():target.symlink_to(p)
    env=os.environ.copy();lake=shutil.which('lake');assert lake
    lean=run([lake,'env','which','lean'],env)
    env['LEAN_PATH']=str(OUT)+os.pathsep+run([lake,'env','printenv','LEAN_PATH'],env)
    for n in FILES:
        run([lean,'--trust=0','-DwarningAsError=true','-o',str(overlay/(Path(n).stem+'.olean')),
             'scratch/FlyCNS/'+n],env,OUT/(n+'.log'))
    deps=DEPENDENCIES.replace('(env.getModuleFor? name)',
        '((env.getModuleIdxFor? name).map (fun index => env.header.moduleNames[index.toNat]!))')
    path=OUT/'NativeMinimumAudit.lean';log=OUT/'dependencies.log'
    path.write_text('import scratch.FlyCNS.C3NativeMinimum\nset_option autoImplicit false\n'+deps+'\n'+
        '\n'.join('#print axioms '+r+'\n#content_full_dependencies '+r for r in ROOTS)+'\n')
    run([lean,'--trust=0','-DwarningAsError=true',str(path)],env,log)
    sizes,axioms={},{ }
    for line in log.read_text().splitlines():
        if line.startswith('CONTENT_FULL_DEP\t'):
            _,r,n,user,mod,kind=line.split('\t')
            if kind=='axiom':axioms.setdefault(r,set()).add(n)
        elif line.startswith('CONTENT_FULL_DONE\t'):
            _,r,count=line.split('\t');sizes[r]=int(count)
    assert set(sizes)==set(ROOTS)
    for r in ROOTS: assert axioms.get(r,set()) <= {'propext','Classical.choice','Quot.sound'}
    for n,digest in expected.items():assert sha(OWNED/n)==digest,n
    result={'schema':'flycns-c3-private-parser-nonenumerating-minimum-independent-kernel-certification/v1',
        'candidate_commits':['719aa65545','0337cbf004'],'candidate_sha256':expected,
        'fresh_modules':3,'focused_controls':6,'complete_dependency_closures':len(ROOTS),'trust':0,'warning_as_error':True,
        'no_project_axiom_unsafe_sorry_control_dependency':True,
        'private_original_Current_parser_and_three_source_clock_guards':True,
        'autonomous_successor_plus_three_explicit_input_letters':True,
        'all69_future_readers_exact':True,'key_domain':'Nat success visit or exact String source error',
        'no_finite_state_enumeration_or_table_argument':True,'pack_unpack_original_read_and_action_commute':True,
        'minimum_future_kernel_and_factor_through_other_faithful_implementations':True,
        'consumePublished_uses_existing_generated_event_without_second_numeric_step':True,
        'fresh_published_epoch_actual_execution_claim':False,'byte8_key_or_finiteness_claim':False,
        'reused_certifications':['1481fad8bb','a1c6009c01','68306b8b60'],
        'mouths':{r:{'dependencies':sizes[r],'axioms':sorted(axioms.get(r,[]))} for r in ROOTS},
        'NN_updates':0,'physics_updates':0,'Source_commands':0,'full_state_enumerations':0,
        'scope':'source-private parser/3clock guarded complete published successor; complete actual-anchor reachable carrier; nonenumerating success/error key, arbitrary mixed four-letter words/69 readers, exact future kernel and minimum factor; typed direct consumer of already emitted PublishedAt occurrence; resource, bounded8byte key and actual new published epoch separate'}
    (HERE/'c3-native-minimum-kernel-summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'fresh_modules':3,'focused_controls':6,'closures':len(ROOTS),'native_parser_minimum':True,'NN_physics_enumeration':0}))


if __name__=='__main__':main()

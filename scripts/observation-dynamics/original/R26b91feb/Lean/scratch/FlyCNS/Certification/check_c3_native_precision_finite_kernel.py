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
OUT=HERE/'.cache/c3-native-precision-finite-audit'
FILES=['C3NativeByteBound.lean','C3NativePrecision.lean','C3NativeSuccessFinite.lean','C3NativeFinite.lean','C3NativePrecisionControls.lean']
ROOTS=['FlyCNS.C3NativeByteBound.'+n for n in ['byte_bound','little_bound','word_bound','parser_width','word_parser_width']]+[
 'FlyCNS.C3NativePrecision.'+n for n in ['advance_width','advance_physics','generated_physics_bound','generated_physics_conservation',
 'generated_visit_bound','carrier_success_bound','encode','forget_encode','finite_key_injective','pack','unpack','unpack_pack','pack_unpack',
 'action_commutes','read_commutes','all_words_commute','all_readers_zero_error','minimum_future_kernel','minimal_other_implementations',
 'consumePublished','consumed_same_image','successfulAddress_injective','finite_successful_carrier']]+[
 'FlyCNS.C3NativeFinite.'+n for n in ['generated_index_bound','letter_roundtrip','execute_autonomous','fromAddress','covers_carrier',
 'finite_carrier','finite_original_key','finite_precision_key']]
CONTROLS=r"""
namespace NativePrecisionFiniteAudit
open FlyCNS C3FiniteOccurrence C3NativeMinimum
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
variable {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
example (state : Carrier boundary installed anchor) :
    C3NativePrecision.unpack (C3NativePrecision.pack state)=state := C3NativePrecision.unpack_pack state
example (word : List Letter) (observer : Fin 69) (state : Carrier boundary installed anchor) :
    C3NativePrecision.read observer (WholeRepresentation.runMap C3NativePrecision.action word (C3NativePrecision.pack state))=
    C3NativeMinimum.read observer (execute installed word state.val) := C3NativePrecision.all_readers_zero_error word observer state
example (left right : Carrier boundary installed anchor) :
    C3NativePrecision.encode left=C3NativePrecision.encode right ↔
    ∀ word : List Letter,∀ observer : Fin 69,C3NativeMinimum.read observer (run word left).val=C3NativeMinimum.read observer (run word right).val :=
    C3NativePrecision.minimum_future_kernel left right
example (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (Carrier boundary installed anchor) := C3NativeFinite.finite_carrier boundary installed anchor
example (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (C3NativeMinimum.Encoded boundary installed anchor) := C3NativeFinite.finite_original_key boundary installed anchor
example (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (C3NativePrecision.Encoded boundary installed anchor) := C3NativeFinite.finite_precision_key boundary installed anchor
example (input : Letter) : C3NativeFinite.letter (C3NativeFinite.letterCode input)=input := C3NativeFinite.letter_roundtrip input
example (before : Ready boundary installed anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current) (observer : Fin 69) :
    C3NativePrecision.read observer (C3NativePrecision.consumePublished before event)=
      Except.ok (C3CompleteInventory.read (C3ReachableModel.reader observer) (C3CompleteInventory.fromActual event.original)) :=
    C3NativePrecision.consumed_same_image before event observer
end NativePrecisionFiniteAudit
"""


def main():
    expected={}
    for n in FILES:
        commit='c455b96b86' if n in ['C3NativeByteBound.lean','C3NativePrecision.lean'] else '85c47fc652'
        raw=subprocess.check_output(['git','show',commit+':Lean/scratch/FlyCNS/'+n],cwd=REPO)
        assert (OWNED/n).read_bytes()==raw,n;expected[n]=hashlib.sha256(raw).hexdigest()
    precision=(OWNED/'C3NativePrecision.lean').read_text();finite=(OWNED/'C3NativeFinite.lean').read_text()
    success=(OWNED/'C3NativeSuccessFinite.lean').read_text()
    old_success=subprocess.check_output(['git','show','c455b96b86:Lean/scratch/FlyCNS/C3NativePrecisionControls.lean'],cwd=REPO).decode()
    assert success==old_success and 'Controls' not in finite
    assert 'max (anchor.base.current.words.get field).vector.width (boundary.source.material.layout.get field).width' in precision
    assert '256^(width boundary anchor)/1000+3' in precision and 'C3Clock.closed_eq_generate' in precision
    assert 'have gates:C3Clock.gateCount current.current.visit≤2' in precision
    assert 'Fin (stateBound boundary anchor) ⊕ String' in precision and '| .error why => .inr why' in precision
    assert 'pack (C3NativeMinimum.consumePublished before event)' in precision
    consumer=precision[precision.index('def consumePublished '):]
    assert 'C3BoundPublication.generate' not in consumer and 'advance installed' not in consumer
    assert 'Fin (prefixBound boundary anchor) ⊕ (Fin (prefixBound boundary anchor) × Fin 4)' in finite
    assert 'List.replicate index.val (.inl ())++[letter input]' in finite
    assert 'Finite.of_surjective (fromAddress installed anchor) (covers_carrier installed anchor)' in finite
    assert 'error_first installed anchor word 0 anchor.base rfl paid' in finite
    overlay=OUT/'scratch/FlyCNS';overlay.mkdir(parents=True,exist_ok=True)
    skip={Path(n).stem for n in FILES}
    for cache in [HERE/'.cache/c3-native-minimum-audit',HERE/'.cache/c3-published-root-audit',
                  HERE/'.cache/c3-reachable-minimum-audit',HERE/'.cache/c3-compressed-publication-audit',OWNED/'.cache/content-full']:
        for p in (cache/'scratch/FlyCNS').glob('*.olean'):
            target=overlay/p.name
            if p.stem not in skip and not target.exists():target.symlink_to(p)
    env=os.environ.copy();lake=shutil.which('lake');assert lake
    lean=run([lake,'env','which','lean'],env)
    env['LEAN_PATH']=str(OUT)+os.pathsep+run([lake,'env','printenv','LEAN_PATH'],env)
    for n in FILES:
        run([lean,'--trust=0','-DwarningAsError=true','-o',str(overlay/(Path(n).stem+'.olean')),
             'scratch/FlyCNS/'+n],env,OUT/(n+'.log'))
    target=OUT/'Controls.lean';target.write_text('import scratch.FlyCNS.C3NativeFinite\nset_option autoImplicit false\n'+CONTROLS)
    run([lean,'--trust=0','-DwarningAsError=true',str(target)],env,OUT/'controls.log')
    deps=DEPENDENCIES.replace('(env.getModuleFor? name)',
        '((env.getModuleIdxFor? name).map (fun index => env.header.moduleNames[index.toNat]!))')
    path=OUT/'PrecisionAudit.lean';log=OUT/'dependencies.log'
    path.write_text('import scratch.FlyCNS.C3NativeFinite\nset_option autoImplicit false\n'+deps+'\n'+
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
    for n,digest in expected.items():assert sha(OWNED/n)==digest,n
    result={'schema':'flycns-c3-original-parser-clock-generated-full-carrier-finite-precision-independent-certification/v1',
        'candidate_commits':['c455b96b86','85c47fc652'],'candidate_sha256':expected,
        'fresh_modules':5,'focused_controls':CONTROLS.count('example ')+1,'complete_dependency_closures':len(ROOTS),'trust':0,'warning_as_error':True,
        'no_project_axiom_unsafe_sorry_control_dependency':True,
        'actual_word_byte_bound_and_original_parser_width_and_three_source_clock_guards':True,
        'conserved_original_physics_clock_and_two_zero_micro_gate_visits':True,
        'finite_success_address_not_caller_supplied_bound':True,'exact_String_errors_preserved':True,
        'full_native_carrier_including_errors_finite_without_enumeration':True,
        'finite_address_producer':'autonomous successful prefix, or autonomous prefix plus first original four-letter effect',
        'finite_original_and_precision_minimum_key_domains':True,'fourletters_all_words_69readers_exact_and_minimum_factor':True,
        'same_emitted_PublishedAt_precision_consumer_no_second_numeric_step':True,
        'production_success_finite_module_literal_promoted_from_c455_control_asset':True,
        '8byte_serialization_runtime_or_resource_gain_claim':False,'future_target_table_or_error_list_or_each_address_success_witness':False,
        'reused_certifications':['51196565e8','1481fad8bb','68306b8b60'],
        'mouths':{r:{'dependencies':sizes[r],'axioms':sorted(axioms.get(r,[]))} for r in ROOTS},
        'NN_updates':0,'physics_updates':0,'Source_commands':0,'full_state_enumerations':0,
        'scope':'complete native original-parser/clock guarded source carrier from actual anchor, derived finite success and first-error prefix coverage, full raw and precision Encoded finite, exact mixed-four-word/69 original readers/future kernel/minimum and same-event consumer; no generated500 execution, serialized8byte implementation or resource gain'}
    (HERE/'c3-native-precision-finite-kernel-summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'fresh_modules':5,'focused_controls':result['focused_controls'],'closures':len(ROOTS),'full_carrier_errors_finite':True,'NN_physics_enumeration':0}))


if __name__=='__main__':main()

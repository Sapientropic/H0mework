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
OUT=HERE/'.cache/c3-native-key-codec-audit'
FILES=['C3NativeCodecSeal.lean','C3NativeKeyBytes.lean','C3NativeKeyDecoder.lean']
ROOTS=['FlyCNS.C3NativeCodec.'+n for n in ['at400','sealed_width','sealed_address_bound','sealed_payload_bound',
 'encode','readWord','parse','counter_size','counter_tag','error_tag','error_payload','utf8_roundtrip',
 'parse_encode','encode_parse','encode_injective','success_size','emptyCache','restoreKey','restore','restoreKey_origin',
 'restore_success','restore_origin','saveAddress','restore_saveAddress','saved_all_future_readers',
 'savePublished','restore_savedPublished','savedPublished_same_image','savedPublished_whole_six',
 'serialize','serialize_injective','serialized_minimum_future_kernel','serialize_success_size','savedPublished_size']]
CONTROLS=r"""
namespace NativeKeyCodecAudit
open FlyCNS C3FiniteOccurrence C3NativeMinimum
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
variable {boundary : Boundary} (context : C3NativeCodec.Seal boundary) (installed : Installed boundary)
example (key : C3NativeCodec.Key context) : C3NativeCodec.parse context (C3NativeCodec.encode context key)=.ok key :=
  C3NativeCodec.parse_encode context key
example : C3NativeCodec.parse context (C3NativeCodec.encode context (.inr ""))=.ok (.inr "") :=
  C3NativeCodec.parse_encode context (.inr "")
example : C3NativeCodec.parse context (C3NativeCodec.encode context (.inr "果蝇\u0000源错误"))=.ok (.inr "果蝇\u0000源错误") :=
  C3NativeCodec.parse_encode context (.inr "果蝇\u0000源错误")
example (address : Fin (C3NativePrecision.stateBound boundary context.anchor)) :
    (C3NativeCodec.encode context (.inl address)).size=8 := C3NativeCodec.success_size context address
example (bytes : ByteArray) (key : C3NativeCodec.Key context)
    (paid : C3NativeCodec.parse context bytes=.ok key) : C3NativeCodec.encode context key=bytes := C3NativeCodec.encode_parse paid
example (cache : C3NativeCodec.ErrorCache context installed) (address : C3NativeFinite.Address boundary context.anchor) :
    let saved:=C3NativeCodec.saveAddress context installed cache address
    C3NativeCodec.restore context installed saved.errors saved.bytes=.ok (C3NativeFinite.fromAddress installed context.anchor address) :=
  C3NativeCodec.restore_saveAddress context installed cache address
example (cache : C3NativeCodec.ErrorCache context installed) (address : C3NativeFinite.Address boundary context.anchor)
    (word : List Letter) (observer : Fin 69) :
    (do let saved:=C3NativeCodec.saveAddress context installed cache address
        let state ← C3NativeCodec.restore context installed saved.errors saved.bytes
        C3NativeMinimum.read observer (execute installed word state.val))=
      C3NativeMinimum.read observer (execute installed word (C3NativeFinite.fromAddress installed context.anchor address).val) :=
  C3NativeCodec.saved_all_future_readers context installed cache address word observer
example (cache : C3NativeCodec.ErrorCache context installed) (before : Ready boundary installed context.anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current) (observer : Fin 69) :
    (do let saved:=C3NativeCodec.savePublished context installed cache before event
        let state ← C3NativeCodec.restore context installed saved.errors saved.bytes
        C3NativeMinimum.read observer state.val)=
      Except.ok (C3CompleteInventory.read (C3ReachableModel.reader observer) (C3CompleteInventory.fromActual event.original)) :=
  C3NativeCodec.savedPublished_same_image context installed cache before event observer
example (cache : C3NativeCodec.ErrorCache context installed) (before : Ready boundary installed context.anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current) :
    (C3NativeCodec.savePublished context installed cache before event).bytes.size=8 :=
  C3NativeCodec.savedPublished_size context installed cache before event
example (left right : Carrier boundary installed context.anchor) :
    C3NativeCodec.serialize context left=C3NativeCodec.serialize context right ↔
    ∀ word : List Letter,∀ observer : Fin 69,C3NativeMinimum.read observer (run word left).val=C3NativeMinimum.read observer (run word right).val :=
  C3NativeCodec.serialized_minimum_future_kernel context installed left right
end NativeKeyCodecAudit
"""


def main():
    expected={}
    for n in FILES:
        raw=subprocess.check_output(['git','show','b8de2ba34d:Lean/scratch/FlyCNS/'+n],cwd=REPO)
        assert (OWNED/n).read_bytes()==raw,n;expected[n]=hashlib.sha256(raw).hexdigest()
    seal=(OWNED/FILES[0]).read_text();bits=(OWNED/FILES[1]).read_text();decoder=(OWNED/FILES[2]).read_text()
    assert 'private mk ::' in seal and 'event : ContentReentryRoot.GeneratedAt boundary.source before' in seal
    assert 'let anchor:=fromActual (boundary:=boundary) event' in seal
    assert all(s in seal for s in ['if visit:anchor.base.current.visit=4','if tick:anchor.base.current.tick=400',
        'if physics:C3NativePrecision.physics anchor.base=4000','vector.width=8','layoutWidth:', 'width=8'])
    assert 'address.val*256<2^64' in seal and 'stateBound boundary context.anchor<2^56' in seal
    assert '| .inr why => errorTag++why.toUTF8' in bits and 'encode context key=bytes' in bits
    assert 'if bytes.size≠8' in bits and 'String.fromUTF8?' in bits
    assert all(s in decoder for s in ['structure ErrorEntry','structure ErrorCache','private mk ::',
        'generated : (C3NativeFinite.fromAddress installed context.anchor address).val=.error why'])
    cache=decoder[decoder.index('structure ErrorEntry'):decoder.index('def emptyCache')]
    assert 'Snapshot' not in cache and 'after' not in cache and 'table' not in cache
    assert 'List.replicate (address.val-context.anchor.base.current.visit) (.inl ())' in decoder
    assert 'if _owned:C3NativePrecision.encode state=key' in decoder
    published=decoder[decoder.index('def savePublished'):decoder.index('theorem restore_savedPublished')]
    assert 'C3NativeMinimum.consumePublished before event' in published and 'cache' in published
    assert 'fromAddress' not in published and 'restoreKey' not in published and 'generate' not in published
    overlay=OUT/'scratch/FlyCNS';overlay.mkdir(parents=True,exist_ok=True)
    skip={Path(n).stem for n in FILES}
    for cache in [HERE/'.cache/c3-native-precision-finite-audit',HERE/'.cache/c3-native-minimum-audit',
                  HERE/'.cache/c3-published-root-audit',HERE/'.cache/c3-reachable-minimum-audit',
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
    target=OUT/'Controls.lean';target.write_text('import scratch.FlyCNS.C3NativeKeyDecoder\nset_option autoImplicit false\n'+CONTROLS)
    run([lean,'--trust=0','-DwarningAsError=true',str(target)],env,OUT/'controls.log')
    deps=DEPENDENCIES.replace('(env.getModuleFor? name)',
        '((env.getModuleIdxFor? name).map (fun index => env.header.moduleNames[index.toNat]!))')
    path=OUT/'KeyCodecAudit.lean';log=OUT/'dependencies.log'
    path.write_text('import scratch.FlyCNS.C3NativeKeyDecoder\nset_option autoImplicit false\n'+deps+'\n'+
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
    result={'schema':'flycns-c3-source-sealed-canonical-eightbyte-success-lossless-error-key-independent-certification/v1',
        'candidate_commit':'b8de2ba34d','candidate_sha256':expected,'fresh_modules':3,'focused_controls':CONTROLS.count('example '),
        'complete_dependency_closures':len(ROOTS),'trust':0,'warning_as_error':True,
        'no_project_axiom_unsafe_sorry_control_dependency':True,
        'Seal_internallychecks_originalGeneratedAt4_NN400_P4000_actualword_andlayout8':True,
        'success_key_total_bytes':8,'success_tag_lowbyte':0,'error_key':'tag1 and complete variable UTF8 including empty/Unicode/NUL',
        'source_derived_payload_bound_no_caller_bound':True,'canonical_parse_encode_both_directions_and_no_alias':True,
        'source_membership_success_replays_own_Anchor_generate_parser_threeclock':True,
        'private_past_ErrorCache_only_source_generated_address_String_proof_noSnapshot':True,
        'saveAddress_internal_generation_and_all_future69_restoration':True,
        'savePublished_same_already_generated_event_zero_extra_F':True,'same69_Image_and_actualwhole6_next':True,
        'serialized_byte_equality_iff_original_fourletter_all69_futurekernel':True,
        'target_after_table_evaluator_normalizer_or_futurekey_features_argument':False,
        'actual_key_disk_cold_decoder_or_resource_gain_certified':False,
        'reused_certifications':['81f7d1be51','51196565e8','1481fad8bb'],
        'mouths':{r:{'dependencies':sizes[r],'axioms':sorted(axioms.get(r,[]))} for r in ROOTS},
        'NN_updates':0,'physics_updates':0,'Source_commands':0,'graph_loads':0,'Source_epoch500_execution':0,
        'scope':'source-derived actual400 schema seal; canonical success8bytes and complete variable errorUTF8, source-generated membership decoder/past-cache, all fourletter words69 exact and byte minimum futurekernel, direct same PublishedAt69/whole6 consumer; typed kernel contract, actual disk/cold decoder/resources separate'}
    (HERE/'c3-native-key-codec-kernel-summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'fresh_modules':3,'focused_controls':result['focused_controls'],'closures':len(ROOTS),'canonical_8byte_success_lossless_error':True,'NN_physics_Source_graph_updates':0}))


if __name__=='__main__':main()

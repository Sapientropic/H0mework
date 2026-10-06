#!/usr/bin/env python3
"""Source-law consumers adjudicate public experiment claims and nominal model."""
from concurrent.futures import ThreadPoolExecutor
from contextlib import redirect_stdout
import argparse
import hashlib
import gzip
import io
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PUB=HERE/"nominal-replay/public-review"
ROOT=HERE.parents[4]
sys.path.insert(0,str(HERE))
from nominal_environment_optimum import VERSION,assess_nominal_replay

READERS={
    "complete_public_count_statistics":("multi-window/verify.py","multi-window/cross-verification.json","p23-public-multi-window-evidence/v1",
        ("public_count_review_certified",)),
    "complete_public_source_fibre":("multi-window/source_verify.py","multi-window/source-cross-verification.json","p23-public-multi-window-source-evidence/v1",
        ("source_outer_cover_and_all_72_CI_certified","complete_original_domain_partition_certified","all_32_positive_Born_members_regenerated",
         "source_family_has_positive_and_negative_CH_N5_members","common_phase_before_window_certified")),
    "original_source_statistical_review":("prefix_review.py","original-source-review.json","p23-original-source-review-evidence/v1",
        ("original_public_prefix_source_review_certified","source_negative_CH_null_rejected")),
    "cut_free_public_source_signature":("anytime-source/consume.py","anytime-source/certification.json","p23-anytime-public-source-evidence/v1",
        ("cut_free_public_family_source_signature_certified","full_run_counts_and_one_step_source_law_consumed")),
    "heralding_source_law":("../observable-closure/full-statistical-fiber/public-calibration/heralding_bound_certify.py",
        "../observable-closure/full-statistical-fiber/public-calibration/heralding-bound-certification.json","p23-heralding-bound-evidence/v1",
        ("conditional_heralding_source_law_kernel_certified","qualified_eta_necessary_bounds_kernel_certified","all_angles_full_lambda_and_zero_source_herald_preserved")),
    "calibrated_source_count_review":("calibrated-counts/verify.py","calibrated-counts/verification.json","public-calibrated-count-evidence/v1",
        ("nominal_continuous_source_domain_rejected","all_19_source_count_readouts_independently_verified","public_72_CI_consumed"))}


def require(value,reason):
    if not value:raise ValueError(reason)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path):
    rel=Path(path).resolve().relative_to(ROOT).as_posix()
    commit=subprocess.check_output(["git","log","-1","--format=%H","--",rel],cwd=ROOT,text=True).strip()
    require(commit and subprocess.check_output(["git","show",commit+":"+rel],cwd=ROOT)==Path(path).read_bytes(),"unfrozen_public_review:"+rel)
    return {"path":rel,"commit":commit,"sha256":digest(path)}


def reader(name,certificate=None,disabled=False):
    program,canonical,schema,flags=READERS[name]
    rejected={"evidence_valid":False,"name":name,"review_completed":False}
    if disabled:return {**rejected,"reason":"explicitly_disabled"}
    target=PUB/canonical if certificate is None else Path(certificate)
    if not target.is_file():return {**rejected,"reason":"required_public_certificate_missing"}
    try:
        if name=="cut_free_public_source_signature":
            # Its CLI prints a summary; the public API carries the certified intake fields.
            code=("import importlib.util,json,sys; "
                  "s=importlib.util.spec_from_file_location('_public_anytime_intake',sys.argv[1]); "
                  "m=importlib.util.module_from_spec(s); sys.modules[s.name]=m; s.loader.exec_module(m); "
                  "r=m.consume(certificate_path=sys.argv[2]); print(json.dumps(r)); "
                  "sys.exit(0 if r['evidence_valid'] else 1)")
            command=[sys.executable,"-c",code,str(PUB/program),str(target)]
        else:
            command=[sys.executable,str(PUB/program),"--check-only","--certificate",str(target)]
        run=subprocess.run(command,
                           text=True,capture_output=True,timeout=60)
        row=json.loads(run.stdout)
        require(run.returncode==0 and row.get("schema")==schema and row.get("evidence_valid") is True and
                all(row.get(f) is True for f in flags),"invalid_or_wrong_public_review_scope:"+name)
        return {**row,"name":name,"review_completed":True}
    except (ValueError,OSError,KeyError,subprocess.SubprocessError) as error:
        return {**rejected,"reason":str(error)}


def verify_source_roles():
    source_roles=json.loads((PUB/"sources-public-review.json").read_text())
    roles=frozen(PUB/"sources-public-review.json")
    require(source_roles["schema"]=="p23-public-experiment-source-role-review/v1","changed_public_input_roles")
    for item in source_roles["bindings"]:
        require(digest(ROOT/item["path"])==item["sha256"],"public_input_role_binding_changed:"+item["path"])
    return roles


def generate():
    bindings=[frozen(PUB/"criterion-final-review.md"),frozen(__file__)]
    roles=verify_source_roles()
    with ThreadPoolExecutor(max_workers=3) as pool:
        values=list(pool.map(reader,READERS))
    rows={name:value for name,value in zip(READERS,values)}
    prior=PUB/"complete-review-current.json"
    prior_binding=frozen(prior)
    nominal=json.loads(prior.read_text())["nominal_replay"]
    verify_nominal_storage(nominal["bindings"])
    verify_nominal_binding_tree(nominal["bindings"])
    require(nominal["evaluator"]["sha256"]==digest(HERE/"nominal_environment_optimum.py") and
            nominal["evidence_valid"] is True and nominal["status"]=="certified_deviation_exceeds_predeclared_band",
            "bound_prior_nominal_verdict_changed")
    bindings.append(prior_binding)
    nominal_complete=nominal.get("evidence_valid") is True and nominal.get("production_eligible") is True
    completed=all(v.get("review_completed") is True for v in values) and nominal_complete
    optimum=nominal.get("verified") is True
    return {"schema":"p23-complete-public-experiment-review/v1","version":"p23-final-public-experiment-review-pr0001",
            "bindings":bindings,"public_source_roles":roles,"reviews":rows,"nominal_replay":nominal,
            "public_review_completed":completed,"evidence_valid":completed,
            "public_statistical_source_signature_certified":rows["cut_free_public_source_signature"].get("cut_free_public_family_source_signature_certified") is True,
            "hidden_cut_log_required_for_public_signature":False,
            "nominal_continuous_count_model_accepted":False,
            "nominal_apparatus_optimum_verified":optimum,
            "decision":"COMPLETED_WITH_NOMINAL_MODEL_REJECTION" if completed and not optimum else
                       "COMPLETED_WITH_NOMINAL_MODEL_ACCEPTANCE" if completed else "PUBLIC_REVIEW_INCOMPLETE",
            "pending_reviews":[name for name,row in rows.items() if row.get("review_completed") is not True]+
                              ([] if nominal_complete else ["original_nominal_replay"]),
            "new_external_data_dependency":False,"private_instrument_parameters_used":False,"raw_event_files_read":0,
            "source_models_combined_as_same_actual_source":False,"actual_hardware_identity_claimed":False,
            "original_CI_modified":False,"nominal_optimum_contract_replaced":False}


def verify_nominal_storage(bindings):
    directory=HERE/"nominal-replay/observable-closure/environment-source"
    names={"original_primary_first":"replay-r0006", "original_independent_first":"independent-replay-r0006",
           "independent_completion_first":"independent-replay-r0006.1"}
    for name,stem in names.items():
        row=bindings[name];stored=directory/(stem+".json.gz");sidecar=directory/(stem+"-storage.json")
        frozen(sidecar)
        meta=json.loads(sidecar.read_text());raw=gzip.decompress(stored.read_bytes())
        primary=name=="original_primary_first"
        require(meta["schema"]==("p23-nominal-environment-primary-storage/v1" if primary else "p23-environment-replay-independent-storage/v1"),
                "wrong_nominal_storage_schema:"+name)
        stored_name=meta["stored_receipt"] if primary else meta["gzip_path"]
        logical_hash=meta["logical_json_sha256"] if primary else meta["logical_sha256"]
        original_commit=meta["original_first_receipt_commit"] if primary else meta["original_first_result_commit"]
        require(row["gzip_path"]==stored_name==stored.name and
                stored.stat().st_size==row["gzip_bytes"]==meta["gzip_bytes"] and
                digest(stored)==row["gzip_sha256"]==meta["gzip_sha256"] and
                len(raw)==row["logical_bytes"]==meta["raw_bytes"] and
                hashlib.sha256(raw).hexdigest()==row["logical_sha256"]==logical_hash and
                row["original_commit"]==original_commit and
                row["logical_path"]==str((directory/(stem+".json")).relative_to(ROOT)),
                "nominal_scientific_first_storage_changed:"+name)
        original=subprocess.check_output(["git","show",row["original_commit"]+":"+row["logical_path"]],cwd=ROOT)
        require(original==raw,"nominal_first_is_not_original_Git_blob:"+name)


def verify_nominal_binding_tree(value):
    if isinstance(value,dict):
        if "path" in value and "sha256" in value:
            path=(ROOT/value["path"]).resolve()
            require(path.is_relative_to(ROOT) and digest(path)==value["sha256"],"nominal_review_dependency_changed")
        for item in value.values():verify_nominal_binding_tree(item)
    elif isinstance(value,list):
        for item in value:verify_nominal_binding_tree(item)


def consume(certificate_path=None,disabled=False):
    result={"schema":"p23-complete-public-experiment-review-evidence/v1","evidence_valid":False,
            "public_review_completed":False,"public_statistical_source_signature_certified":False,
            "apparatus_optimum_verified":False,"disabled":disabled}
    if disabled:return {**result,"reason":"explicitly_disabled"}
    try:
        canonical=PUB/"complete-review-final.json";binding=frozen(canonical)
        candidate=Path(certificate_path) if certificate_path is not None else canonical
        require(digest(candidate)==binding["sha256"],"unbound_or_lookalike_public_review_certificate")
        report=json.loads(candidate.read_text())
        require(report["schema"]=="p23-complete-public-experiment-review/v1" and
                report["public_review_completed"] is True,"public_review_is_not_complete")
        for row in report["bindings"]+[report["public_source_roles"]]:
            require(digest(ROOT/row["path"])==row["sha256"],"completed_review_source_changed")
        require(verify_source_roles()==report["public_source_roles"],"public_input_roles_do_not_reverify")
        with ThreadPoolExecutor(max_workers=3) as pool:
            values=list(pool.map(reader,READERS))
        require({name:value for name,value in zip(READERS,values)}==report["reviews"],"public_review_does_not_reverify")
        verify_nominal_binding_tree(report["nominal_replay"]["bindings"])
        verify_nominal_storage(report["nominal_replay"]["bindings"])
        require(report["nominal_replay"]["evaluator"]["sha256"]==digest(HERE/"nominal_environment_optimum.py") and
                report["nominal_replay"]["evidence_valid"] is True and
                report["nominal_replay"]["status"]=="certified_deviation_exceeds_predeclared_band",
                "nominal_review_verdict_or_evaluator_changed")
        result.update(evidence_valid=True,public_review_completed=True,public_statistical_source_signature_certified=report["public_statistical_source_signature_certified"],
                      decision=report["decision"],source=binding,reviews=report["reviews"],new_external_data_dependency=False,
                      actual_hardware_identity_claimed=False,original_CI_modified=False,
                      hidden_cut_log_required_for_public_signature=False,
                      nominal_continuous_count_model_accepted=False,reason="complete_source_driven_public_claim_review")
    except (OSError,ValueError,KeyError,TypeError,subprocess.SubprocessError) as error:
        result["reason"]=str(error)
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--output",type=Path)
    parser.add_argument("--check-only",action="store_true");parser.add_argument("--certificate",type=Path);parser.add_argument("--disabled",action="store_true")
    args=parser.parse_args()
    if args.check_only:
        result=consume(args.certificate,args.disabled);print(json.dumps(result,sort_keys=True));return 0 if result["evidence_valid"] else 1
    require(args.output is not None and not args.output.exists(),"new_public_review_output_required")
    report=generate();args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"decision":report["decision"],"public_review_completed":report["public_review_completed"],"sha256":digest(args.output),
                      "pending_reviews":report["pending_reviews"]}));return 0 if report["public_review_completed"] else 1


if __name__=="__main__":raise SystemExit(main())

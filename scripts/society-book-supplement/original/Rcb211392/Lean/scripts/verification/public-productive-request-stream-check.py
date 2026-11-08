#!/usr/bin/env python3
"""Independent exact ledger consumer for paid request windows and their actual stream."""
import argparse
import copy
import importlib.util
import hashlib
import json
from fractions import Fraction
from pathlib import Path

_spec=importlib.util.spec_from_file_location("synthesis",Path(__file__).with_name("public-productive-synthesis-check.py"))
_base=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_base)
require,snapshot,quantities=_base.require,_base.snapshot,_base.quantities


def actions(state, rows):
    state=copy.deepcopy(state)
    for index,row in enumerate(rows):
        require(row["index"]==index and snapshot(row["before"])==state,"actual instruction before/index")
        request=row["request"];op=request["operation"];kind=op["kind"]
        require(request["consents"]==[] and request["gates"]==[],"source authority shape")
        debit,credit,delta={},{},{}
        permitted=True
        if kind=="issue":
            require(op=={"kind":"issue","instrument":"delivery","debtor":"provider:0","creditor":"audit:3","quantity":"2"}
                    and request["signer"]=="provider:0" and request["purpose"]=={"kind":"exchange"},"original issue")
            permitted=state["claims"][("delivery","provider:0","audit:3")]==0
            delta[("delivery","provider:0","audit:3")]=Fraction(2)
        elif kind=="transfer":
            require(op=={"kind":"transfer","from":"audit:0","to":"provider:0","bundle":[["feed","1"]]}
                    and request["signer"]=="audit:0" and request["purpose"]=={"kind":"exchange"},"original feed")
            permitted=state["claims"][("delivery","provider:0","audit:3")]>0
            debit={("audit:0","feed"):Fraction(1)};credit={("provider:0","feed"):Fraction(1)}
        elif kind=="produce":
            require(op=={"kind":"produce","actor":"provider:0"} and request["signer"]=="provider:0"
                    and request["purpose"]=={"kind":"provider","base":"reserve","owner":0},"original production")
            permitted=state["technology"]["provider"]["technology"] is True
            debit={("provider:0","feed"):Fraction(1),("provider:0","labor"):Fraction(1)}
            credit={("provider:0","energy"):Fraction(2),("provider:0","labor"):Fraction(3)}
        elif kind=="settle":
            require(op=={"kind":"settle","instrument":"delivery","debtor":"provider:0","creditor":"audit:3","quantity":"2"}
                    and request["signer"]=="provider:0" and request["purpose"]=={"kind":"exchange"},"original shipment")
            permitted=state["claims"][("delivery","provider:0","audit:3")]>=2
            debit={("provider:0","energy"):Fraction(2)};credit={("audit:3","energy"):Fraction(2)}
            delta[("delivery","provider:0","audit:3")]=Fraction(-2)
        elif kind=="present":
            require(request["signer"]=="audit:3" and request["purpose"]=={"kind":"audit","base":"common","query":None},"request registration")
        elif kind=="use":
            actor=op["actor"]
            if actor=="provider:0":
                require(op["bundle"]==[["labor","1"]] and op["purpose"]=="external"
                        and request["purpose"]=={"kind":"provider","base":"reserve","owner":0},"planning price")
            else:
                require(actor=="audit:3" and request["purpose"]=={"kind":"audit","base":"common","query":None},"requester service port")
                require((op["purpose"],op["bundle"]) in (("investment",[["energy","1"]]),("external",[["energy","2"]])),"application/service unit")
            require(request["signer"]==actor,"own payment signer")
            debit={(actor,g):Fraction(q) for g,q in op["bundle"]}
        else:
            raise ValueError("unexpected primitive")
        accepted=permitted and all(state["stock"].get(k,0)>=q for k,q in debit.items())
        require(row["accepted"] is accepted,"actual resource admission")
        require(quantities(row["debit"])==(debit if accepted else {}) and quantities(row["credit"])==(credit if accepted else {}),"actual debit/credit")
        if accepted:
            for k,q in debit.items():state["stock"][k]-=q
            for k,q in credit.items():state["stock"][k]+=q
            for k,q in delta.items():state["claims"][k]+=q
    return state


def window(window,before,after,rows,old_id,cursor,old_slots):
    require(window["id"]==old_id+1+cursor and window["nonce"]==before["round"],"fresh actual request identity")
    require(Fraction(window["requestBeforeClock"])==before["clock"] and window["requestBeforeRound"]==before["round"],"request source before")
    task=window["task"]
    require(Fraction(task["earliest"])==after["clock"]+1 and Fraction(task["deadline"])==after["clock"]+6,"source-born legal window")
    require(task["slots"]==[{"bearer":"audit:3","goods":[["energy","2"]],"purpose":"external"}],"requested service")
    reg,fee=window["registrationIndex"],window["feeIndex"]
    require(0<=reg<fee<len(rows) and rows[reg]["accepted"] and rows[fee]["accepted"],"actual registration before payment")
    require(rows[reg]["request"]==window["registration"] and rows[reg]["request"]["operation"]=={"kind":"present"},"registration source item")
    require(rows[fee]["request"]==window["fee"] and rows[fee]["request"]["operation"]=={
        "kind":"use","actor":"audit:3","bundle":[["energy","1"]],"purpose":"investment"},"actual application fee")
    require(Fraction(window["feeBeforeClock"])==before["clock"],"fee actual clock")
    role=window["role"]
    require(any(all(slot[k]==v for k,v in role.items()) for slot in old_slots),"original native creditor role")
    require(role["holder"]=="audit:3","requester original role")


def finance(before,after,rows,state):
    require(after[:len(before)]==before,"old delivery archives changed")
    issues=[row for row in rows if row["accepted"] and row["request"]["operation"]["kind"]=="issue"]
    payments=[row for row in rows if row["accepted"] and row["request"]["operation"]["kind"]=="settle"]
    require(len(after)==len(before)+len(issues),"native complete inventory")
    for slot in after[len(before):]:
        require(slot["instrument"]=="delivery" and slot["debtor"]=="provider:0" and slot["holder"]=="audit:3"
                and Fraction(slot["quantity"])==2,"native original claim")
        birth=[r for r in issues if r["index"]==slot["instruction"] and r["before"]["round"]==slot["birthRound"]
               and r["before"]["clock"]==slot["birthClock"] and r["request"]==slot["request"]]
        require(len(birth)==1,"actual native birth")
        if slot["terminal"]:
            require(slot["fulfilled"] and Fraction(slot["balance"])==0,"native fulfilled disposition")
            payment=slot["payment"]
            match=[r for r in payments if r["index"]==payment["index"] and r["before"]["round"]==payment["round"] and r["request"]==payment["request"]]
            require(len(match)==1 and payment["payment"] and Fraction(payment["quantity"])==Fraction(payment["cap"])==2,"native actual payment")
            require((slot["birthRound"],slot["instruction"])<(payment["round"],payment["index"]),"native payment order")
        else:
            require(not slot["fulfilled"] and Fraction(slot["balance"])==2 and slot["payment"] is None,"unpaid responsibility erased")
    require(sum(Fraction(s["balance"]) for s in after)==state["claims"][("delivery","provider:0","audit:3")],"native/raw debt alignment")


def verify_case(value):
    old_id=value["oldTaskId"];old_task=value["oldTask"];previous=snapshot(value["initial"])
    require(old_id==2 and Fraction(old_task["deadline"])==56 and previous["clock"]==59,"inherited actual cut")
    require(value["oldCompleted"]==[0,1],"inherited task wrongly completed")
    original_due={"id":old_id,"task":old_task,"observedClock":"59","ordinal":0,"inherited":True}
    expected_protocol={"received":0,"pending":None,"expired":[original_due],"completed":[],"event":"idle"}
    opened,served,application,planning,all_rows=0,0,Fraction(0),Fraction(0),[]
    for ordinal,tick in enumerate(value["ticks"]):
        before,after=snapshot(tick["before"]),snapshot(tick["after"])
        require(tick["ordinal"]==ordinal and before==previous and tick["protocolBefore"]==expected_protocol,"same stream successor")
        expected=actions(before,tick["rows"]);expected["clock"]+=1;expected["round"]+=1
        require(after==expected==snapshot(tick["publishedAfter"]),"actual root after / published state")
        protocol=tick["protocolAfter"];event=protocol["event"];prior=expected_protocol
        require(protocol["expired"][:len(prior["expired"])]==prior["expired"] and original_due in protocol["expired"],"inherited overdue responsibility lost")
        expected_protocol=copy.deepcopy(prior);expected_protocol["event"]=event
        if event=="admitted":
            require(prior["pending"] is None and protocol["pending"] is not None,"request admission phase")
            window(protocol["pending"],before,after,tick["rows"],old_id,prior["received"],value["accountBefore"])
            expected_protocol["pending"]=protocol["pending"];expected_protocol["received"]+=1;opened+=1
        elif event=="served":
            pending=prior["pending"];require(pending is not None,"unrequested service")
            require(Fraction(pending["task"]["earliest"])<=before["clock"] and after["clock"]<=Fraction(pending["task"]["deadline"]),"service original window")
            goods=[r for r in tick["rows"] if r["request"]["operation"].get("purpose")=="external" and r["request"]["operation"].get("actor")=="audit:3"]
            require(len(goods)==1 and goods[0]["accepted"],"real requested service")
            require(protocol["completed"]==prior["completed"]+[{"window":pending,"beforeClock":str(before["clock"]),"fees":2}],"same requested obligation fulfillment")
            expected_protocol["pending"]=None;expected_protocol["completed"]=protocol["completed"];served+=1
        elif event=="past-due":
            pending=prior["pending"];require(pending is not None and Fraction(pending["task"]["deadline"])<before["clock"] and tick["rows"]==[],"actual expiry")
            due={"id":pending["id"],"task":pending["task"],"observedClock":str(before["clock"]),"ordinal":ordinal,"inherited":False}
            expected_protocol["pending"]=None;expected_protocol["expired"].append(due)
        elif event=="refused-request":
            require(prior["pending"] is None and protocol["pending"] is None,"refusal cannot open task")
            expected_protocol["received"]+=1
        elif event=="waiting":
            require(prior["pending"] is not None and before["clock"]<Fraction(prior["pending"]["task"]["earliest"]) and tick["rows"]==[],"premature service")
        elif event=="refused-service":
            require(prior["pending"] is not None and not any(r["request"]["operation"].get("actor")=="audit:3" and r["request"]["operation"].get("purpose")=="external" for r in tick["rows"]),"false service refusal/fulfillment")
        else:
            require(event in ("bootstrap","idle") and tick["rows"]==[],"unrecognized stream event")
        require(protocol==expected_protocol,"complete protocol successor")
        require(all(c["window"]["id"]>old_id for c in protocol["completed"]),"new delivery erased old liability")
        for row in tick["rows"]:
            op=row["request"]["operation"]
            if row["accepted"] and op["kind"]=="use":
                if op["purpose"]=="investment":application+=1
                if op["actor"]=="provider:0":planning+=1
        previous=after;all_rows+=tick["rows"]
    finance(value["accountBefore"],value["accountAfter"],all_rows,previous)
    for key,principal in (("nativeAudit",1),("nativeProvider",7)):
        require(len(value[key])==1 and Fraction(value[key][0]["quantity"])==principal and value[key][0]["fulfilled"]
                and Fraction(value[key][0]["balance"])==0,"paid original native debt changed")
    return {"opened":opened,"served":served,"application_energy":str(application),"planning_labor":str(planning),"final_clock":str(previous["clock"]),"expired":len(expected_protocol["expired"]),"stock":previous["stock"]}


def verify(value,settlement):
    require(value["schema"]=="productive-request-stream/v1" and value["scope"]=="original-base-local-continuation","scope")
    require(snapshot(value["normal"]["initial"])==snapshot(settlement["final"]),"not inherited actual clock59")
    normal_initial=snapshot(value["normal"]["initial"])
    for name in ("replay","forged","lookalike"):
        require(snapshot(value[name]["initial"])==normal_initial,"request override changed original inventory")
    no_material=copy.deepcopy(normal_initial);no_material["stock"][("audit:0","feed")]=Fraction(0)
    require(snapshot(value["noMaterial"]["initial"])==no_material,"missing-material fixture")
    no_labor=copy.deepcopy(no_material);no_labor["stock"][("provider:0","labor")]=Fraction(0);no_labor["stock"][("audit:3","energy")]=Fraction(3)
    require(snapshot(value["expiredNew"]["initial"])==no_labor,"expired-window fixture")
    for name in ("replay","forged","lookalike","noMaterial","expiredNew"):
        require(value[name]["accountBefore"]==value["normal"]["accountBefore"],"request override changed original account")
    results={name:verify_case(value[name]) for name in ("normal","replay","forged","lookalike","noMaterial","expiredNew")}
    normal=results["normal"]
    require((normal["opened"],normal["served"],normal["application_energy"],normal["planning_labor"],normal["final_clock"],normal["expired"])==(3,3,"3","6","69",1),"continuous paid delivery")
    require(normal["stock"][("audit:0","feed")]==15 and normal["stock"][("provider:0","labor")]==5 and normal["stock"][("audit:3","energy")]==1,"source resource balance")
    require(results["replay"]["opened"]==results["replay"]["served"]==1 and results["replay"]["application_energy"]=="1","replay charged again")
    for name in ("forged","lookalike","noMaterial"):
        require(results[name]["opened"]==results[name]["served"]==0 and results[name]["application_energy"]=="0","refused request admitted")
    require(results["expiredNew"]["opened"]==1 and results["expiredNew"]["served"]==0 and results["expiredNew"]["expired"]==2,"new overdue obligation lost")
    return {"result":"PASS","real_requests":3,"legal_windows":3,"delivered":3,"application_energy":3,"planning_labor":6,"source_feed":5,"old_due_retained":True,"native_old_debt":0,"replay_extra_fee":0,"economic_rpc":0}


def negatives(value,settlement):
    changes={
      "refreshed_old_deadline":lambda v:v["normal"]["ticks"][3]["protocolAfter"]["expired"][0]["task"].update(deadline="999"),
      "missing_application_fee":lambda v:v["normal"]["ticks"][1]["rows"][-1].update(debit=[]),
      "wrong_request_signer":lambda v:v["normal"]["ticks"][1]["rows"][-1]["request"].update(signer="provider:0"),
      "old_task_fulfilled_by_new":lambda v:v["normal"]["ticks"][3]["protocolAfter"]["completed"][0]["window"].update(id=2),
      "invented_window":lambda v:v["normal"]["ticks"][1]["protocolAfter"]["pending"]["task"].update(earliest="0"),
      "fee_not_in_actual_source":lambda v:v["normal"]["ticks"][1]["protocolAfter"]["pending"].update(feeIndex=0),
      "wrong_native_role":lambda v:v["normal"]["ticks"][1]["protocolAfter"]["pending"]["role"].update(holder="audit:1"),
      "free_planning":lambda v:v["normal"]["ticks"][3]["rows"][0].update(debit=[]),
      "old_archive_dropped":lambda v:v["normal"]["accountAfter"].pop(0),
      "erased_unpaid_funding":lambda v:v["noMaterial"]["accountAfter"][-1].update(balance="0"),
      "dropped_new_overdue":lambda v:v["expiredNew"]["ticks"][-1]["protocolAfter"].update(expired=[]),
      "unrelated_published_after":lambda v:v["normal"]["ticks"][3].update(publishedAfter=v["normal"]["initial"]),
    }
    for name,mutate in changes.items():
        changed=copy.deepcopy(value);mutate(changed)
        try:verify(changed,settlement)
        except (ValueError,KeyError,IndexError):continue
        raise ValueError("accepted mutation: "+name)
    return list(changes)


def verify_bundle(box,evidence):
    root=Path(__file__).resolve().parents[3]
    require(box["schema"]=="productive-request-stream/1" and box["result"]=="PASS","bundle scope")
    prefix="Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Regeneration/Supply/Material/Productive/Synthesis/Settlement/"
    modules={prefix+name+".lean" for name in ("Requests","Stream","Stream/Runtime")}
    scripts={"Lean/scripts/verification/public-productive-request-stream-"+name for name in ("source.lean","check.py","kernel.lean")}
    require(set(box["source_sha256"])==modules|scripts,"complete source inventory")
    sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
    for name,digest in box["source_sha256"].items():require(sha(root/name)==digest,"source binding")
    require(set(box["strict_modules"])==modules,"strict artifact inventory")
    for name,receipt in box["strict_modules"].items():
        artifact=evidence/"lib"/Path(name).relative_to("Lean").with_suffix(".olean")
        require(sha(root/name)==receipt["source"] and sha(artifact)==receipt["artifact"],"strict source/artifact binding")
    require(set(box["evidence_sha256"])=={"actual.json","actual-exit.json","kernel.json","kernel.log","independent.json"},"complete evidence inventory")
    summary=box["actual"]
    require(summary["requests"]==3 and summary["windows"]==[[62,67],[65,70],[68,73]] and summary["delivered_at"]==[63,66,69]
            and summary["application_energy"]==3 and summary["service_energy"]==6 and summary["planning_labor"]==6
            and summary["source_feed"]==5 and summary["native_delivery_archives"]==7 and summary["final_clock"]==69
            and summary["inherited_task"]=={"id":2,"deadline":56,"observed_at":59,"status":"outstanding past due"},"bundle actual summary")
    for name,digest in box["evidence_sha256"].items():
        require(Path(name).name==name and sha(evidence/name)==digest,"retained evidence binding")
    require(box["kernel"]["roots"]==15 and set(box["kernel"]["axioms"])=={"Quot.sound","Classical.choice","propext"},"kernel contract")
    receipt=json.loads((evidence/"kernel.json").read_text());log=(evidence/"kernel.log").read_text()
    require(receipt["exit"]==0 and "REPLAY PASS: roots=15," in log
            and "axioms=[Quot.sound, Classical.choice, propext]" in log,"actual kernel replay")
    actual=json.loads((evidence/"actual-exit.json").read_text())
    require(actual["exit"]==0 and actual["source"]==box["source_sha256"]["Lean/scripts/verification/public-productive-request-stream-source.lean"]
            and actual["output"]==sha(evidence/"actual.json")==box["actual_output_sha256"],"actual source output binding")
    return "PASS"


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("transcript",type=Path);parser.add_argument("settlement",type=Path);parser.add_argument("--report",type=Path)
    parser.add_argument("--box",type=Path);parser.add_argument("--evidence",type=Path)
    args=parser.parse_args();value=json.loads(args.transcript.read_text());settlement=json.loads(args.settlement.read_text())
    report=verify(value,settlement);report["negative_controls"]=negatives(value,settlement)
    if args.box:
        require(args.evidence is not None,"evidence required")
        box=json.loads(args.box.read_text())
        sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
        require(sha(args.transcript)==box["actual_output_sha256"] and sha(args.settlement)==box["inherited_settlement_sha256"],"consumer input bindings")
        report["bundle_provenance"]=verify_bundle(box,args.evidence)
    if args.report:args.report.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,ensure_ascii=False))


if __name__=="__main__":main()

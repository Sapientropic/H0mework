#!/usr/bin/env python3
"""Exact independent consumption of the original productive continuation."""
import argparse
import copy
import hashlib
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

_spec = importlib.util.spec_from_file_location("stream", Path(__file__).with_name("public-productive-request-stream-check.py"))
_stream = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_stream)
require, snapshot, quantities = _stream.require, _stream.snapshot, _stream.quantities
KEY = ("delivery", "provider:0", "audit:3")
ROUTES = ["ordinary", "recycle", "factory", "reserve+ordinary", "reserve+recycle", "reserve+factory"]


def action(actor, operation, purpose=None):
    return {"signer": actor, "consents": [], "gates": [], "purpose": purpose or
            ({"kind": "provider", "base": "reserve", "owner": int(actor[-1])} if actor.startswith("provider:")
             else {"kind": "audit", "base": "common", "query": None}), "operation": operation}


def transfer(sender, target, bundle, exchange=False):
    return action(sender, {"kind": "transfer", "from": sender, "to": target, "bundle": bundle},
                  {"kind": "exchange"} if exchange else None)


def financial(kind):
    return action("provider:0", {"kind": kind, "instrument": "delivery", "debtor": "provider:0",
                                "creditor": "audit:3", "quantity": "2"}, {"kind": "exchange"})


def produce(actor="provider:0"):
    return action(actor, {"kind": "produce", "actor": actor})


def primitive(before, request):
    state = copy.deepcopy(before)
    require(request["consents"] == [] and request["gates"] == [], "unregistered authority")
    op = request["operation"]; kind = op["kind"]; debit = {}; credit = {}; delta = {}
    permitted = True
    if kind in ("issue", "settle"):
        require(request == financial(kind), "original financial key and signer")
        if kind == "issue":
            permitted = state["claims"][KEY] == 0; delta[KEY] = Fraction(2)
        else:
            permitted = state["claims"][KEY] >= 2; delta[KEY] = Fraction(-2)
            debit[("provider:0", "energy")] = Fraction(2); credit[("audit:3", "energy")] = Fraction(2)
    elif kind == "transfer":
        sender, target, bundle = op["from"], op["to"], op["bundle"]
        exchange = sender == "audit:0"
        require(request == transfer(sender, target, bundle, exchange), "material owner/port")
        permitted = ((sender == "audit:0" and target in ("provider:0", "provider:1") and bundle == [["feed", "1"]]
                      and state["claims"][KEY] > 0) or
                     (sender == "provider:0" and target in ("provider:1", "provider:2") and bundle == [["energy", "1"], ["labor", "1"]]) or
                     (sender == "provider:1" and target == "provider:2" and bundle == [["waste", "1"]]) or
                     (sender == "provider:2" and target == "provider:0" and bundle == [["feed", "1"]]) or
                     (sender == "audit:3" and target == "audit:0" and bundle == [["feed", "6"]]))
        debit = {(sender, g): Fraction(q) for g, q in bundle}
        credit = {(target, g): Fraction(q) for g, q in bundle}
    elif kind == "produce":
        actor = op["actor"]
        require(actor in ("provider:0", "provider:1", "provider:2") and request == produce(actor), "original producer")
        if actor == "provider:0":
            debit = {(actor, "feed"): Fraction(1), (actor, "labor"): Fraction(1)}
            credit = {(actor, "energy"): Fraction(2), (actor, "labor"): Fraction(3)}
        elif actor == "provider:1":
            debit = {(actor, g): Fraction(1) for g in ("feed", "energy", "labor")}
            credit = {(actor, "life"): Fraction(3), (actor, "waste"): Fraction(1)}
        else:
            debit = {(actor, g): Fraction(1) for g in ("waste", "energy", "labor")}
            credit = {(actor, "feed"): Fraction(1)}
        if actor != "provider:1": permitted = state["technology"]["provider"]["technology"] is True
    elif kind == "present":
        require(request == action("audit:3", {"kind": "present"}), "original registration")
    elif kind == "use":
        actor, bundle, purpose = op["actor"], op["bundle"], op["purpose"]
        require(request == action(actor, op), "own fee/service signer")
        require((actor, bundle, purpose) in (("provider:0", [["labor", "1"]], "external"),
                ("audit:3", [["energy", "1"]], "investment"), ("audit:3", [["energy", "2"]], "external")), "original fee/service units")
        debit = {(actor, g): Fraction(q) for g, q in bundle}
    else:
        raise ValueError("unexpected primitive")
    paid = permitted and all(state["stock"][k] >= q for k, q in debit.items())
    if paid:
        for k, q in debit.items(): state["stock"][k] -= q
        for k, q in credit.items(): state["stock"][k] += q
        for k, q in delta.items(): state["claims"][k] += q
    return state, paid, debit if paid else {}, credit if paid else {}


def execute(before, commands):
    state = before; paid = True
    for command in commands:
        state, accepted, _, _ = primitive(state, command); paid &= accepted
    return state, paid


def attempt(before, commands):
    state = before; result = []
    for command in commands:
        result.append(command); state, paid, _, _ = primitive(state, command)
        if not paid: break
    return result


def recycling_stages(before):
    stock = before["stock"]; stages = []
    if stock[("provider:2", "feed")] >= 1:
        return [transfer("provider:2", "provider:0", [["feed", "1"]])]
    funding = stock[("provider:2", "energy")] < 1 or stock[("provider:2", "labor")] < 1
    if funding and stock[("provider:0", "energy")] < 1:
        if stock[("provider:0", "feed")] < 1: stages.append(transfer("audit:0", "provider:0", [["feed", "1"]], True))
        stages.append(produce())
    if funding: stages.append(transfer("provider:0", "provider:2", [["energy", "1"], ["labor", "1"]]))
    if stock[("provider:2", "waste")] < 1: stages.append(transfer("provider:1", "provider:2", [["waste", "1"]]))
    return stages + [produce("provider:2"), transfer("provider:2", "provider:0", [["feed", "1"]])]


def lot(before, recipe):
    initial = [financial("issue")] if before["claims"][KEY] == 0 else []
    current, paid = execute(before, initial)
    if not paid: return initial
    stock = current["stock"]; needed = stock[("provider:0", "energy")] < current["claims"][KEY]
    if recipe == "recycle" and needed and stock[("provider:0", "feed")] < 1:
        stages = recycling_stages(current) + [produce(), financial("settle")]
    else:
        stages = ([transfer("audit:0", "provider:0", [["feed", "1"]], True)] if needed and stock[("provider:0", "feed")] < 1 else [])
        stages += ([produce()] if needed else []) + [financial("settle")]
    return initial + attempt(current, stages)


def factory(before):
    s = before["stock"]
    f = s[("provider:1", "energy")] < 1 or s[("provider:1", "labor")] < 1
    d = s[("provider:2", "energy")] < 1 or s[("provider:2", "labor")] < 1
    stages = [financial("issue")] if before["claims"][KEY] == 0 else []
    if s[("provider:0", "energy")] < int(f) + int(d):
        if s[("provider:0", "feed")] < 1: stages.append(transfer("audit:0", "provider:0", [["feed", "1"]], True))
        stages.append(produce())
    if s[("provider:1", "feed")] < 1: stages.append(transfer("audit:0", "provider:1", [["feed", "1"]], True))
    if f: stages.append(transfer("provider:0", "provider:1", [["energy", "1"], ["labor", "1"]]))
    stages.append(produce("provider:1"))
    if d: stages.append(transfer("provider:0", "provider:2", [["energy", "1"], ["labor", "1"]]))
    stages += [transfer("provider:1", "provider:2", [["waste", "1"]]), produce("provider:2"),
               transfer("provider:2", "provider:0", [["feed", "1"]]), produce(), financial("settle")]
    return attempt(before, stages)


def route(before, name):
    offer = [transfer("audit:3", "audit:0", [["feed", "6"]])] if name.startswith("reserve+") else []
    state, _ = execute(before, offer)
    recipe = name.removeprefix("reserve+")
    return offer + (factory(state) if recipe == "factory" else lot(state, recipe))


def material_due(before, protocol):
    s = before["stock"]
    return (s[("audit:0", "feed")] < 1 and s[("provider:0", "feed")] < 1 and
            (s[("audit:3", "energy")] < 3 or s[("provider:0", "labor")] < 2) and
            (protocol["pending"] is None or before["clock"] <= Fraction(protocol["pending"]["task"]["deadline"])))


def original_word(before, protocol, limit):
    s = before["stock"]; pending = protocol["pending"]
    live = (before["clock"] + 1 <= Fraction(pending["task"]["deadline"])) if pending else (limit is None or protocol["received"] < limit)
    if live and s[("audit:3", "energy")] < 2 and s[("provider:0", "feed")] < 1 and s[("provider:2", "feed")] < 1:
        return lot(before, "recycle"), True
    resume_live = (before["clock"] <= Fraction(pending["task"]["deadline"])) if pending else (limit is None or protocol["received"] < limit)
    if resume_live and material_due(before, protocol):
        return [transfer("audit:3", "audit:0", [["feed", "6"]])], True
    if pending:
        if before["clock"] < Fraction(pending["task"]["earliest"]) or Fraction(pending["task"]["deadline"]) < before["clock"]:
            return [], False
        charge = action("provider:0", {"kind": "use", "actor": "provider:0", "bundle": [["labor", "1"]], "purpose": "external"})
        service = action("audit:3", {"kind": "use", "actor": "audit:3", "bundle": [["energy", "2"]], "purpose": "external"})
        current = before; commands = []
        for candidate in ([], [service]):
            next_state, paid, _, _ = primitive(current, charge)
            if not paid: break
            commands.append(charge); current = next_state
            target, valid = execute(current, candidate)
            if candidate and valid and target["claims"][KEY] == 0 and before["clock"] + 1 <= Fraction(pending["task"]["deadline"]):
                return commands + candidate, False
        return commands, False
    if limit is not None and protocol["received"] >= limit: return [], False
    required = max(3, s[("audit:3", "energy")] + 2 if s[("provider:0", "labor")] < 2 else 3)
    current = before; commands = []
    for _ in range(-(-required.numerator // (2 * required.denominator)) + 1 if isinstance(required, Fraction) else (required + 1) // 2 + 1):
        if required <= current["stock"][("audit:3", "energy")] and current["claims"][KEY] == 0: break
        word = lot(current, "ordinary"); commands += word; current, paid = execute(current, word)
        if not paid: break
    return commands + [action("audit:3", {"kind": "present"}),
        action("audit:3", {"kind": "use", "actor": "audit:3", "bundle": [["energy", "1"]], "purpose": "investment"})], False


def expected_word(before, protocol, limit, recovery):
    if recovery and before["claims"][KEY] > 0 and not (protocol["pending"] and Fraction(protocol["pending"]["task"]["deadline"]) < before["clock"]):
        for name in ROUTES:
            if name.startswith("reserve+") and not material_due(before, protocol): continue
            commands = route(before, name); after, valid = execute(before, commands)
            if valid and after["claims"][KEY] == 0: return commands, name, True
        return [], "blocked", True
    commands, holds = original_word(before, protocol, limit)
    return commands, "original", holds


def finance(before, after, rows, current):
    expected = copy.deepcopy(before)
    for row in rows:
        if not row["accepted"]: continue
        op = row["request"]["operation"]
        if op["kind"] == "issue":
            expected.append({"instrument": "delivery", "debtor": "provider:0", "holder": "audit:3", "quantity": "2",
                "instruction": row["index"], "birthRound": row["before"]["round"], "birthClock": row["before"]["clock"],
                "request": row["request"], "balance": "2", "fulfilled": False, "payment": None, "terminal": False})
        elif op["kind"] == "settle":
            live = next((slot for slot in expected if not slot["terminal"] and Fraction(slot["balance"]) > 0), None)
            require(live is not None and Fraction(live["balance"]) == 2, "original live native key")
            live.update(balance="0", fulfilled=True, terminal=True,
                payment={"request": row["request"], "round": row["before"]["round"], "index": row["index"],
                         "quantity": "2", "cap": "2", "payment": True})
    require(after == expected, "complete original native slots, payments and origins")
    require(sum(Fraction(s["balance"]) for s in after) == current["claims"][KEY], "native/raw live principal")


def trace(initial, protocol, ticks, old_slots, limit, recovery, source_start):
    state = snapshot(initial); protocol = copy.deepcopy(protocol); all_rows = []; served = []; reserve = 0
    for ordinal, tick in enumerate(ticks):
        require(tick["ordinal"] == ordinal and snapshot(tick["before"]) == state and tick["protocolBefore"] == protocol, "actual contiguous predecessor")
        require(tick["sourceOrdinal"] == source_start + ordinal, "original source ordinal")
        commands, branch, holds = expected_word(state, protocol, limit, recovery)
        require([r["request"] for r in tick["rows"]] == commands, "source-generated exact programme")
        require(tick["branch"] == (branch if recovery else "regeneration"), "source-selected disposition")
        before = copy.deepcopy(state); expected_protocol = copy.deepcopy(protocol)
        for index, row in enumerate(tick["rows"]):
            require(index == row["index"] and snapshot(row["before"]) == state, "same actual instruction")
            state, paid, debit, credit = primitive(state, row["request"])
            require(row["accepted"] is paid and quantities(row["debit"]) == debit and quantities(row["credit"]) == credit, "real debit/credit and authority")
            if paid and row["request"]["operation"].get("from") == "audit:3": reserve += 6
        state["clock"] += 1; state["round"] += 1
        require(snapshot(tick["after"]) == state, "exact full-state actual successor")
        next_protocol = tick["protocolAfter"]; event = next_protocol["event"]; pending = protocol["pending"]
        if not holds:
            expected_protocol["event"] = event
            if event == "admitted":
                require(pending is None, "request admitted over old pending")
                _stream.window(next_protocol["pending"], before, state, tick["rows"], 2, protocol["received"], old_slots)
                expected_protocol["pending"] = next_protocol["pending"]; expected_protocol["received"] += 1
            elif event == "served":
                require(pending is not None and before["clock"] >= Fraction(pending["task"]["earliest"]) and state["clock"] <= Fraction(pending["task"]["deadline"]), "own live service window")
                require(any(r["accepted"] and r["request"]["operation"] == {"kind": "use", "actor": "audit:3", "bundle": [["energy", "2"]], "purpose": "external"} for r in tick["rows"]), "actual service payment")
                expected_protocol["completed"].append({"window": pending, "beforeClock": str(before["clock"]), "fees": 2})
                expected_protocol["pending"] = None; served.append(str(state["clock"]))
            elif event == "past-due":
                require(pending is not None and Fraction(pending["task"]["deadline"]) < before["clock"] and not commands, "real expiry")
                expected_protocol["expired"].append({"id": pending["id"], "task": pending["task"], "observedClock": str(before["clock"]), "ordinal": tick["sourceOrdinal"], "inherited": False})
                expected_protocol["pending"] = None
            elif event == "refused-request":
                require(pending is None and not (len(tick["rows"]) >= 2 and all(r["accepted"] for r in tick["rows"][-2:])), "paid request falsely refused")
                expected_protocol["received"] += 1
            elif event == "waiting":
                require(pending is not None and before["clock"] < Fraction(pending["task"]["earliest"]), "waiting deadline")
            elif event == "refused-service":
                require(pending is not None and not any(r["request"]["operation"].get("bundle") == [["energy", "2"]] for r in tick["rows"]), "false refusal")
            else: require(event == "idle" and not commands and pending is None, "unexpected protocol event")
        require(next_protocol == expected_protocol, "complete responsibility and request cursor transition")
        protocol = expected_protocol; all_rows += tick["rows"]
    return state, protocol, all_rows, served, reserve


def verify(value, previous):
    require(value["schema"] == "productive-recursive/v1" and value["scope"] == "original-base-local-private-audit", "scope")
    require((len(value["regenerationPrefix"]), len(value["prefix"]), len(value["ticks"])) == (5, 4, 24), "complete registered source trace")
    old = previous["normal"]
    require(value["predecessor117"] == old["publishedFinal"] and value["predecessor117Protocol"] == old["publishedProtocol"] and value["predecessor117Account"] == old["accountAfter"], "exact paid predecessor117")
    s122, p122, rows122, _, _ = trace(value["predecessor117"], value["predecessor117Protocol"], value["regenerationPrefix"], value["predecessor117Account"], 20, False, 1)
    require(s122 == snapshot(value["before122"]) and p122 == value["protocol122"] and s122["clock"] == 122, "original 122 frame")
    finance(value["predecessor117Account"], value["account122"], rows122, s122)
    s126, p126, rows126, _, _ = trace(value["before122"], value["protocol122"], value["prefix"], value["account122"], 20, True, 6)
    require(s126 == snapshot(value["initial"]) and p126 == value["protocolInitial"] and s126["clock"] == 126 and len(p126["completed"]) == p126["received"] == 20, "complete actual clock126 handoff")
    finance(value["account122"], value["accountBefore"], rows126, s126)
    state, protocol, rows, served, reserve = trace(value["initial"], value["protocolInitial"], value["ticks"], value["accountBefore"], None, True, 10)
    require(state == snapshot(value["publishedFinal"]) and protocol == value["publishedProtocol"], "actual coface publication")
    finance(value["accountBefore"], value["accountAfter"], rows, state)
    require(all(slot["fulfilled"] for slot in value["accountAfter"]) and state["claims"][KEY] == 0, "finite final native fulfillment")
    require(len(served) >= 3 and len(protocol["completed"]) >= 23, "continuous new paid deliveries")
    require(protocol["expired"][:len(p126["expired"])] == p126["expired"] and p126["expired"][0]["id"] == 2 and p126["expired"][0]["task"]["deadline"] == "56", "old overdue responsibility")
    for key in ("nativeAudit", "nativeProvider"): require(value[key] == old[key], "original native paid debts")
    for key, amount in s126["claims"].items():
        if key[0] != "delivery": require(state["claims"][key] == amount, "old claim coordinate")
    uses = [r["request"]["operation"] for r in rows if r["accepted"] and r["request"]["operation"]["kind"] == "use"]
    return {"result": "PASS", "from_clock": 126, "final_clock": str(state["clock"]), "new_deliveries": len(served),
        "delivered_at": served, "total_deliveries": len(protocol["completed"]), "native_slots": len(value["accountAfter"]),
        "native_fulfilled": sum(slot["fulfilled"] for slot in value["accountAfter"]), "native_delivery_principal": "0",
        "application_energy": sum(o["purpose"] == "investment" for o in uses),
        "planning_labor": sum(o["actor"] == "provider:0" for o in uses), "service_energy": 2 * len(served),
        "reserve_feed_transferred": reserve, "old_due_retained": True, "consumer_native_or_economic_replay": 0}


def negative_controls(value, previous):
    admitted = next(i for i, t in enumerate(value["ticks"]) if t["protocolAfter"]["event"] == "admitted" and t["protocolBefore"]["event"] != "admitted")
    service = next(i for i, t in enumerate(value["ticks"]) if t["protocolAfter"]["completed"] != t["protocolBefore"]["completed"])
    changes = {
        "missing_application_debit": lambda v: v["ticks"][admitted]["rows"][-1].update(debit=[]),
        "wrong_request_actor": lambda v: v["ticks"][admitted]["rows"][-1]["request"].update(signer="audit:1"),
        "stale_nonce": lambda v: v["ticks"][admitted]["protocolAfter"]["pending"].update(nonce=0),
        "invented_window": lambda v: v["ticks"][admitted]["protocolAfter"]["pending"]["task"].update(deadline="999"),
        "dropped_old_due": lambda v: v["ticks"][service]["protocolAfter"].update(expired=[]),
        "free_planning": lambda v: v["ticks"][service]["rows"][0].update(debit=[]),
        "reissued_old_archive": lambda v: v["accountAfter"][0].update(birthRound=0),
        "changed_126_native_slot": lambda v: v["accountBefore"][0].update(balance="1"),
        "false_final": lambda v: v.update(publishedFinal=copy.deepcopy(v["initial"])),
        "replayed_tick": lambda v: v["ticks"].insert(1, copy.deepcopy(v["ticks"][0])),
        "cursor_jump": lambda v: v["ticks"][service]["protocolAfter"].update(received=999),
        "forgot_old_117_prefix": lambda v: v["predecessor117Account"].pop(0),
        "forged_source_ordinal": lambda v: v["ticks"][0].update(sourceOrdinal=999),
    }
    for name, mutate in changes.items():
        changed = copy.deepcopy(value); mutate(changed)
        try: verify(changed, previous)
        except (ValueError, KeyError, IndexError, TypeError): continue
        raise ValueError("accepted mutation: " + name)
    return list(changes)


def verify_bundle(box, evidence):
    root = Path(__file__).resolve().parents[3]
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    require(box["schema"] == "productive-recursive/1" and box["result"] == "PASS", "bundle scope")
    base = "Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Regeneration/Supply/Material/Productive/Synthesis/Settlement/Stream/Resume/Regen/Recovery/Future"
    modules = {base + ".lean", base + "/Preservation.lean", base + "/Runtime.lean", base + "/Continuation.lean"}
    scripts = {"Lean/scripts/verification/public-productive-recursive-" + name for name in ("source.lean", "check.py", "kernel.lean", "suffix-kernel.lean")}
    require(set(box["source_sha256"]) == modules | scripts and set(box["strict_modules"]) == modules, "complete candidate inventory")
    for path, digest in box["source_sha256"].items(): require(sha(root / path) == digest, "exact candidate source")
    for path, record in box["strict_modules"].items():
        require(record["exit"] == 0 and record["source"] == sha(root / path) and
                record["artifact"] == sha(evidence / "lib" / Path(path).relative_to("Lean").with_suffix(".olean")), "strict source/artifact binding")
        require("--trust=0" in record["command"] and "-DwarningAsError=true" in record["command"], "strict kernel gate")
    old_box = root / "Verification/public-audit/regeneration/productive/stream-material.json"
    predecessor = json.loads(old_box.read_text())
    require(sha(old_box) == box["predecessor_bundle_sha256"] and predecessor["actual_output_sha256"] == box["predecessor_output_sha256"], "paid predecessor binding")
    for path, digest in box["reused_source_sha256"].items(): require(sha(root / path) == digest, "original source retained")
    actual = json.loads((evidence / "actual-exit.json").read_text())
    require(actual["exit"] == 0 and actual["source"] == box["source_sha256"]["Lean/scripts/verification/public-productive-recursive-source.lean"] and
            actual["input"] == predecessor["original_input_sha256"] and actual["output"] == sha(evidence / "actual.json") == box["actual_output_sha256"], "actual occurrence input/output/source")
    kernel = json.loads((evidence / "kernel.json").read_text()); log = " ".join((evidence / "kernel.log").read_text().split())
    require(kernel["exit"] == 0 and kernel["source"] == box["source_sha256"]["Lean/scripts/verification/public-productive-recursive-kernel.lean"] and
            kernel["output"] == sha(evidence / "kernel.log") and "REPLAY PASS: roots=17," in log and
            "axioms=[Quot.sound, Classical.choice, propext]" in log, "complete empty-kernel replay")
    suffix = json.loads((evidence / "suffix-kernel.json").read_text())
    suffix_log = " ".join((evidence / "suffix-kernel.log").read_text().split())
    require(box["kernel"]["suffix_roots"] == 4 and suffix["exit"] == 0 and
            suffix["source"] == box["source_sha256"]["Lean/scripts/verification/public-productive-recursive-suffix-kernel.lean"] and
            suffix["output"] == sha(evidence / "suffix-kernel.log") and "SUFFIX KERNEL REPLAY PASS: roots=4," in suffix_log and
            "axioms=[Quot.sound, Classical.choice, propext]" in suffix_log, "complete carrier suffix kernel replay")
    require(set(box["evidence_sha256"]) == {"actual.json", "actual-exit.json", "kernel.json", "kernel.log", "suffix-kernel.json", "suffix-kernel.log", "independent.json", "running-bindings.json"}, "complete evidence inventory")
    for path, digest in box["evidence_sha256"].items():
        require(Path(path).name == path and sha(evidence / path) == digest, "retained occurrence evidence")
    report = json.loads((evidence / "independent.json").read_text())
    require(report["result"] == "PASS" and box["actual"] == {k: v for k, v in report.items() if k not in ("negative_controls", "actual_sha256")} and
            len(report["negative_controls"]) == 13 and report["actual_sha256"] == actual["output"], "independent actual acceptance")
    return "PASS"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("actual", type=Path); parser.add_argument("previous", type=Path)
    parser.add_argument("--box", type=Path); parser.add_argument("--evidence", type=Path)
    args = parser.parse_args()
    value = json.loads(args.actual.read_text()); previous = json.loads(args.previous.read_text())
    report = verify(value, previous); report["negative_controls"] = negative_controls(value, previous)
    report["actual_sha256"] = hashlib.sha256(args.actual.read_bytes()).hexdigest()
    if args.box:
        require(args.evidence is not None, "evidence directory required")
        box = json.loads(args.box.read_text())
        require(hashlib.sha256(args.previous.read_bytes()).hexdigest() == box["predecessor_output_sha256"], "same paid predecessor file")
        report["bundle"] = verify_bundle(box, args.evidence)
    print(json.dumps(report, indent=2))


if __name__ == "__main__": main()

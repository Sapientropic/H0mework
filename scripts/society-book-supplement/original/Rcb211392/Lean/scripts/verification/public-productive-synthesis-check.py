#!/usr/bin/env python3
"""Consume the local source transcript without Lean, search, or ledger writes."""
import argparse
import copy
import json
from fractions import Fraction
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def quantities(rows):
    result = {}
    for *key, value in rows:
        key = tuple(key)
        require(key not in result, "duplicate coordinate")
        result[key] = Fraction(value)
    return result


def snapshot(value):
    return {
        "stock": quantities(value["stock"]),
        "claims": quantities(value["claims"]),
        "clock": Fraction(value["clock"]),
        "round": value["round"],
        "technology": value["technology"],
    }


def actions(state, rows):
    state = copy.deepcopy(state)
    for index, row in enumerate(rows):
        require(row["index"] == index, "source instruction index")
        require(snapshot(row["before"]) == state, "instruction before")
        action = row["request"]
        op = action["operation"]
        require(action["consents"] == [] and action["gates"] == [], "unexpected authority")
        debit, credit, claim_delta = {}, {}, {}
        permitted = True
        kind = op["kind"]
        if kind == "produce":
            actor = op["actor"]
            require(actor in ("provider:0", "provider:1", "provider:2") and action["signer"] == actor, "production owner")
            require(action["purpose"] == {"kind": "provider", "base": "reserve", "owner": int(actor[-1])}, "production port")
            if actor == "provider:1":
                debit = {(actor, good): Fraction(1) for good in ("feed", "energy", "labor")}
                credit = {(actor, "life"): Fraction(3), (actor, "waste"): Fraction(1)}
            elif actor == "provider:0":
                debit = {(actor, good): Fraction(1) for good in ("feed", "labor")}
                credit = {(actor, "energy"): Fraction(2), (actor, "labor"): Fraction(3)}
                permitted = state["technology"]["provider"]["technology"] is True
            else:
                debit = {(actor, good): Fraction(1) for good in ("waste", "energy", "labor")}
                credit = {(actor, "feed"): Fraction(1)}
                permitted = state["technology"]["provider"]["technology"] is True
        elif kind == "use":
            actor = op["actor"]
            require(action["signer"] == actor and op["purpose"] == "external", "use owner/purpose")
            if actor in ("audit:0", "provider:0"):
                port = ({"kind": "audit", "base": "common", "query": None} if actor == "audit:0" else
                        {"kind": "provider", "base": "reserve", "owner": 0})
                require(action["purpose"] == port, "planning port")
                require(op["bundle"] == [["labor", "1"]], "planning unit")
            elif actor == "audit:3":
                require(op["bundle"] == [["energy", "2"]] and action["purpose"] ==
                        {"kind": "audit", "base": "common", "query": None}, "original new service")
            else:
                require(actor == "provider:1" and op["bundle"] == [["life", "3"]], "new service")
                require(action["purpose"] == {"kind": "provider", "base": "reserve", "owner": 1}, "service port")
            debit = {(actor, good): Fraction(amount) for good, amount in op["bundle"]}
        elif kind in ("issue", "settle"):
            require(action["purpose"] == {"kind": "exchange"}, "financial port")
            require(op["instrument"] == "delivery" and op["debtor"] == "provider:0"
                    and op["creditor"] == "audit:3" and Fraction(op["quantity"]) == 2, "original financial coordinates")
            require(action["signer"] == "provider:0", "financial signer")
            key = ("delivery", "provider:0", "audit:3")
            if kind == "issue":
                require(state["claims"][key] == 0, "duplicate issue")
                claim_delta[key] = Fraction(2)
            else:
                require(state["claims"][key] >= 2, "unbacked settlement")
                debit[("provider:0", "energy")] = Fraction(2)
                credit[("audit:3", "energy")] = Fraction(2)
                claim_delta[key] = Fraction(-2)
        elif kind == "transfer":
            sender, recipient = op["from"], op["to"]
            require(action["signer"] == sender, "transfer signer")
            if sender == "audit:0":
                require(recipient in ("provider:0", "provider:1") and op["bundle"] == [["feed", "1"]]
                        and action["purpose"] == {"kind": "exchange"}, "original material transfer")
                permitted = state["claims"][("delivery", "provider:0", "audit:3")] > 0
            else:
                require(action["purpose"] == {"kind": "provider", "base": "reserve", "owner": int(sender[-1])}, "transfer port")
                allowed = ((sender == "provider:0" and recipient in ("provider:1", "provider:2")
                            and op["bundle"] == [["energy", "1"], ["labor", "1"]]) or
                           (sender == "provider:1" and recipient == "provider:2" and op["bundle"] == [["waste", "1"]]) or
                           (sender == "provider:2" and recipient == "provider:0" and op["bundle"] == [["feed", "1"]]))
                require(allowed, "original provider transfer")
            debit = {(sender, g): Fraction(q) for g, q in op["bundle"]}
            credit = {(recipient, g): Fraction(q) for g, q in op["bundle"]}
        else:
            raise ValueError("unexpected primitive")
        accepted = permitted and all(state["stock"].get(key, 0) >= quantity for key, quantity in debit.items())
        require(row["accepted"] is accepted, "admission/stock mismatch")
        require(quantities(row["debit"]) == (debit if accepted else {}), "actual debit")
        require(quantities(row["credit"]) == (credit if accepted else {}), "actual credit")
        if accepted:
            for key, quantity in debit.items():
                state["stock"][key] -= quantity
            for key, quantity in credit.items():
                state["stock"][key] += quantity
            for key, quantity in claim_delta.items():
                state["claims"][key] += quantity
    return state


def account(value, balance, terminal, origin=None):
    require(len(value) == 1, "original slot inventory")
    slot = value[0]
    require(slot["instrument"] == "delivery" and slot["debtor"] == "provider:0"
            and slot["holder"] == "audit:3" and Fraction(slot["quantity"]) == 2, "original claim")
    require(Fraction(slot["balance"]) == balance and slot["terminal"] is terminal, "native disposition")
    require(slot["fulfilled"] is terminal, "native fulfillment")
    if terminal:
        payment = slot["payment"]
        require(payment["payment"] is True and Fraction(payment["quantity"]) == 2
                and Fraction(payment["cap"]) == 2 and payment["request"]["operation"]["kind"] == "settle", "native actual payment")
    identity = {k: v for k, v in slot.items() if k not in ("balance", "terminal", "fulfilled", "payment")}
    if origin is not None:
        require(identity == origin, "original admission changed")
    return identity


def step(value, expected_fees=None):
    initial, before, after = map(snapshot, (value["initial"], value["before"], value["after"]))
    prepared = copy.deepcopy(initial)
    prepared["clock"] += 1
    prepared["round"] += 1
    require(before == prepared, "original bootstrap")
    actual = actions(before, value["rows"])
    actual["clock"] += 1
    actual["round"] += 1
    require(after == actual, "actual next")
    require(all(row["accepted"] for row in value["rows"]), "unpaid submitted instruction")
    fees = value["fees"]
    if expected_fees is not None:
        require(fees == expected_fees, "source-generated fee count")
    prefix, work = value["rows"][:fees], value["rows"][fees:]
    require(len(prefix) == fees, "missing planning payment")
    require(all(row["request"]["operation"] == {
        "kind": "use", "actor": "audit:0", "bundle": [["labor", "1"]], "purpose": "external"
    } for row in prefix), "planning prefix")
    require(before["stock"][("audit:0", "labor")] - after["stock"][("audit:0", "labor")] == fees,
            "planning labor not actually spent")
    require(not any(row["request"]["signer"] == "audit:0" for row in work), "planning budget reused")
    succeeded = value["succeeded"]
    task = value["task"]
    origin = account(value["accountBefore"], initial["claims"][("delivery", "provider:0", "audit:3")],
                     initial["claims"][("delivery", "provider:0", "audit:3")] == 0)
    account(value["accountAfter"], after["claims"][("delivery", "provider:0", "audit:3")],
            after["claims"][("delivery", "provider:0", "audit:3")] == 0, origin)
    if succeeded:
        require(Fraction(task["earliest"]) <= before["clock"] and after["clock"] <= Fraction(task["deadline"]), "service window")
        for slot in task["slots"]:
            require(any(row["request"]["operation"] == {
                "kind": "use", "actor": slot["bearer"], "bundle": slot["goods"], "purpose": slot["purpose"]
            } for row in work), "new task has no actual payment")
        require(after["claims"][("delivery", "provider:0", "audit:3")] == 0, "old obligation unpaid")
        require(value["nextTaskId"] == value["taskId"] + 1, "new task identity")
        require(value["nextTask"]["slots"] == task["slots"]
                and Fraction(value["nextTask"]["earliest"]) == after["clock"]
                and Fraction(value["nextTask"]["deadline"]) == after["clock"] + 3, "next demand")
    else:
        require(not work and value["nextTask"] == task and value["nextTaskId"] == value["taskId"], "failed task reset")
    return after


def verify(value):
    require(value["schema"] == "productive-synthesis/v1" and value["scope"] == "original-law-local-application", "scope")
    require(len(value["checks"]) == 29 and all(x is True for x in value["checks"]), "kernel regression")
    debt = value["oldDelivery"]
    seed = snapshot(value["seed"])
    before = copy.deepcopy(seed)
    before["clock"] += 1
    before["round"] += 1
    require(snapshot(debt["before"]) == before, "debt genesis")
    debt_after = actions(before, debt["rows"])
    debt_after["clock"] += 1
    debt_after["round"] += 1
    require(snapshot(debt["after"]) == debt_after, "old issue next")
    origin = account(debt["account"], Fraction(2), False)
    reference = value["reference"]
    ref_after = actions(snapshot(reference["before"]), reference["rows"])
    require(any(not row["accepted"] for row in reference["rows"])
            and ref_after["claims"][("delivery", "provider:0", "audit:3")] == 2, "reference not blocked")
    rounds = value["rounds"]
    require(len(rounds) == 3, "three actual cuts")
    previous = debt_after
    for index, (cut, fees) in enumerate(zip(rounds, (10, 11, 19))):
        require(snapshot(cut["initial"]) == previous and cut["taskId"] == min(index, 2), "recursive successor")
        previous = step(cut, fees)
        require(cut["completed"] == ([0] if index == 0 else [0, 1]), "completion inventory")
        account(cut["accountAfter"], Fraction(0), True, origin)
    require(previous["stock"][("audit:0", "labor")] == 0
            and previous["stock"][("provider:1", "feed")] == 0, "exhaustion")
    for cut in value["negative"].values():
        require(cut["succeeded"] is False, "negative admission")
        step(cut)
    return {"result": "PASS", "rounds": 2, "new_service": 6, "old_native_fulfilled": 2,
            "planning_labor": [10, 11, 19], "remaining_labor": 0, "economic_rpc": 0}


def native_prefix(before, after, rows):
    require(len(after) >= len(before), "native inventory truncated")
    identities = []
    for index, slot in enumerate(after):
        identity = {k: v for k, v in slot.items() if k not in ("balance", "terminal", "fulfilled", "payment")}
        require(identity not in identities, "duplicate native admission")
        identities.append(identity)
        require(slot["instrument"] == "delivery" and slot["debtor"] == "provider:0"
                and slot["holder"] == "audit:3" and Fraction(slot["quantity"]) == 2, "native claim coordinates")
        require(slot["terminal"] is True and slot["fulfilled"] is True
                and Fraction(slot["balance"]) == 0, "native fulfilled archive")
        payment = slot["payment"]
        require(payment["payment"] is True and Fraction(payment["quantity"]) == 2
                and Fraction(payment["cap"]) == 2, "native payment receipt")
        if index < len(before):
            require(slot == before[index], "old native archive changed")
        else:
            births = [row for row in rows if row["request"] == slot["request"] and row["index"] == slot["instruction"]
                      and row["before"]["round"] == slot["birthRound"] and row["before"]["clock"] == slot["birthClock"]]
            payments = [row for row in rows if row["request"] == payment["request"] and row["index"] == payment["index"]
                        and row["before"]["round"] == payment["round"]]
            require(len(births) == 1 and births[0]["request"]["operation"]["kind"] == "issue", "actual native birth")
            require(len(payments) == 1 and payments[0]["request"]["operation"]["kind"] == "settle", "actual native settlement")
            require((slot["birthRound"], slot["instruction"]) < (payment["round"], payment["index"]), "native temporal order")
    require(len(after) - len(before) == sum(row["request"]["operation"]["kind"] == "issue" for row in rows), "native birth count")


def original_cut(cut):
    initial, before, after = map(snapshot, (cut["initial"], cut["before"], cut["after"]))
    expected = copy.deepcopy(initial)
    expected["clock"] += 1
    expected["round"] += 1
    require(before == expected, "original cut bootstrap")
    expected = actions(before, cut["rows"])
    expected["clock"] += 1
    expected["round"] += 1
    require(after == expected and all(row["accepted"] for row in cut["rows"]), "original cut actual after")
    require(after["claims"] == initial["claims"], "old raw financial positions changed")
    native_prefix(cut["accountBefore"], cut["accountAfter"], cut["rows"])
    return after


def verify_original(value):
    require(value["schema"] == "productive-synthesis-original/v1" and value["result"] == "PASS", "original scope")
    require(value["firstHistory"] == value["originalHistory"] + 2
            and value["secondHistory"] == value["originalHistory"] + 4, "original session history")
    require(value["preservedScope"] == value["originalScope"], "original mandate window changed")
    previous = snapshot(value["original"])
    origin_count, service, planning = 0, Fraction(0), Fraction(0)
    for label, funding_label in (("first", "fundingFirst"), ("second", "fundingSecond")):
        funding, cut = value[funding_label], value[label]
        require(funding["executed"] is True and snapshot(funding["initial"]) == previous, "actual original producer")
        require(funding["task"] == funding["nextTask"] == cut["task"], "funding reset demand")
        funded = original_cut(funding)
        require(snapshot(cut["initial"]) == funded and cut["accountBefore"] == funding["accountAfter"], "funding not consumed")
        after = original_cut(cut)
        require(cut["succeeded"] is True and cut["fees"] == 2 and len(cut["rows"]) == 3
                and cut["planningPayer"] == "provider:0", "paid original planning")
        for row in cut["rows"][:2]:
            require(row["request"]["operation"] == {"kind": "use", "actor": "provider:0",
                    "bundle": [["labor", "1"]], "purpose": "external"}, "original planning debit")
        require(funded["stock"][("provider:0", "labor")] - after["stock"][("provider:0", "labor")] == 2, "planning material")
        op = cut["rows"][-1]["request"]["operation"]
        require(op == {"kind": "use", "actor": "audit:3", "bundle": [["energy", "2"]], "purpose": "external"}, "new service use")
        require(cut["task"]["slots"] == [{"bearer": "audit:3", "goods": [["energy", "2"]], "purpose": "external"}], "new task identity")
        require(Fraction(cut["task"]["earliest"]) <= snapshot(funding["initial"])["clock"]
                and after["clock"] <= Fraction(cut["task"]["deadline"]), "whole funded service window")
        require(cut["nextTaskId"] == cut["taskId"] + 1
                and Fraction(cut["nextTask"]["earliest"]) == after["clock"]
                and Fraction(cut["nextTask"]["deadline"]) == after["clock"] + 5, "actual next demand")
        require(cut["taskId"] == origin_count and cut["completed"] == list(range(origin_count + 1)), "actual service archive")
        require(len(cut["accountAfter"]) == origin_count + 1, "new native claim inventory")
        service += 2
        planning += 2
        origin_count += 1
        previous = after
    seed = snapshot(value["original"])
    require(seed["stock"][("audit:0", "feed")] == 24
            and previous["stock"][("audit:0", "feed")] == 20, "original source feed")
    require(previous["stock"][("provider:1", "life")] - seed["stock"][("provider:1", "life")] == 6, "real production")
    require(previous["claims"] == seed["claims"], "all original positions")
    return {"result": "PASS", "original_package": True, "rounds": origin_count,
            "source_feed": 4, "produced_life": 6, "new_service_energy": str(service),
            "planning_labor": str(planning), "native_fulfilled_slots": 2, "economic_rpc": 0}


def negative_controls(value):
    mutations = {
        "free_fee": lambda x: x["rounds"][0]["rows"][0].update(debit=[]),
        "missing_fee": lambda x: x["rounds"][0]["rows"].pop(0),
        "invented_feed": lambda x: x["rounds"][1]["initial"]["stock"].append(["provider:1", "feed", "9"]),
        "wrong_recursive_cut": lambda x: x["rounds"][1].update(initial=x["rounds"][0]["initial"]),
        "native_live_after_zero": lambda x: x["rounds"][0]["accountAfter"][0].update(terminal=False),
        "native_balance_erased": lambda x: x["rounds"][0]["accountAfter"][0].update(balance="2"),
        "native_origin_replaced": lambda x: x["rounds"][0]["accountAfter"][0].update(instruction=7),
        "native_quantity_changed": lambda x: x["rounds"][0]["accountAfter"][0].update(quantity="3"),
        "failed_marked_complete": lambda x: x["rounds"][2].update(completed=[0, 1, 2]),
        "failed_window_refreshed": lambda x: x["rounds"][2]["nextTask"].update(deadline="999"),
        "old_slot_dropped": lambda x: x["rounds"][1].update(accountAfter=[]),
        "service_not_delivered": lambda x: x["rounds"][0]["rows"][-1]["request"]["operation"].update(purpose="contribution"),
    }
    for label, mutate in mutations.items():
        altered = copy.deepcopy(value)
        mutate(altered)
        try:
            verify(altered)
        except (ValueError, KeyError, IndexError):
            continue
        raise ValueError("accepted mutation: " + label)
    return list(mutations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("transcript", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--original", type=Path)
    args = parser.parse_args()
    value = json.loads(args.transcript.read_text())
    report = verify(value)
    report["negative_controls"] = negative_controls(value)
    if args.original:
        original = json.loads(args.original.read_text())
        report["original_package"] = verify_original(original)
        changes = {
            "free_original_planning": lambda x: x["first"]["rows"][0].update(debit=[]),
            "unpaid_original_native": lambda x: x["first"]["accountAfter"][0].update(terminal=False),
            "funding_window_reset": lambda x: x["fundingFirst"]["nextTask"].update(deadline="999"),
            "cloned_original_input": lambda x: x["fundingSecond"].update(initial=x["original"]),
            "original_history_dropped": lambda x: x.update(secondHistory=x["originalHistory"]),
            "native_birth_cloned": lambda x: x["second"]["accountAfter"][1].update(birthRound=x["second"]["accountAfter"][0]["birthRound"]),
        }
        for label, mutate in changes.items():
            altered = copy.deepcopy(original)
            mutate(altered)
            try:
                verify_original(altered)
            except (ValueError, KeyError, IndexError):
                continue
            raise ValueError("accepted original mutation: " + label)
        report["original_negative_controls"] = list(changes)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()

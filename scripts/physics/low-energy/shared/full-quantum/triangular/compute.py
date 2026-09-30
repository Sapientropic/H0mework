#!/usr/bin/env python3
"""Source-generated exact spectral Duhamel coefficients, including the Jordan crossing."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import time

import sympy as s

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
spec = importlib.util.spec_from_file_location("full_source", HERE.parent / "compute.py")
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
decode, encode, clean, zero = source.decode, source.encode, source.clean, source.zero


def canonical(value):
    return s.radsimp(s.simplify(value))


def components(matrix):
    neighbors = {i: set() for i in range(matrix.rows)}
    for i, j in matrix.todok():
        neighbors[i].add(j)
        neighbors[j].add(i)
    unseen = set(neighbors)
    result = []
    while unseen:
        pending = [min(unseen)]
        block = set()
        while pending:
            i = pending.pop()
            if i in block:
                continue
            block.add(i)
            pending.extend(neighbors[i] - block)
        unseen -= block
        result.append(sorted(block))
    return result


def block_inverse(matrix, groups):
    result = s.MutableSparseMatrix(matrix.rows, matrix.cols, {})
    cache = {}
    for group in groups:
        block = s.ImmutableMatrix(matrix.extract(group, group))
        inverse = cache.setdefault(block, block.inv())
        for i, row in enumerate(group):
            for j, col in enumerate(group):
                if inverse[i, j]:
                    result[row, col] = canonical(inverse[i, j])
    return s.SparseMatrix(result)


def spectral_projectors(matrix, groups):
    projectors = {}
    for group in groups:
        block = matrix.extract(group, group)
        values = [canonical(x) for x in block.eigenvals()]
        for rate in values:
            projector = s.eye(len(group))
            for other in values:
                if other != rate:
                    projector = projector * (block - other * s.eye(len(group))) / (rate - other)
            projector = projector.applyfunc(canonical)
            zero(projector * projector - projector)
            zero(block * projector - rate * projector)
            target = projectors.setdefault(rate, s.MutableSparseMatrix(matrix.rows, matrix.cols, {}))
            for i, row in enumerate(group):
                for j, col in enumerate(group):
                    if projector[i, j]:
                        target[row, col] += projector[i, j]
    projectors = {key: s.SparseMatrix(value) for key, value in projectors.items()}
    zero(sum(projectors.values(), s.zeros(matrix.rows)) - s.eye(matrix.rows))
    return projectors


def add_term(terms, rate, degree, matrix):
    key = (canonical(rate), degree)
    terms[key] = clean(terms.get(key, s.zeros(matrix.rows)) + matrix)


def time_coefficients(free, interaction, groups):
    projectors = spectral_projectors(free, groups)
    terms = {(rate, 0): matrix for rate, matrix in projectors.items()}
    resonant = []
    for left, pleft in projectors.items():
        for right, pright in projectors.items():
            block = clean(pleft * interaction * pright)
            if not block.todok():
                continue
            if left == right:
                add_term(terms, left, 1, -s.I * block)
                resonant.append(str(left))
            else:
                weight = block.applyfunc(lambda value: canonical(value / (right - left)))
                add_term(terms, right, 0, weight)
                add_term(terms, left, 0, -weight)
    terms = {key: value.applyfunc(canonical) for key, value in terms.items() if value.todok()}
    full = free + interaction
    for (rate, degree), value in terms.items():
        derivative = -s.I * rate * value + (degree + 1) * terms.get((rate, degree + 1), s.zeros(252))
        zero((derivative + s.I * full * value).applyfunc(canonical))
    zero(sum((value for (_, degree), value in terms.items() if degree == 0), s.zeros(252)) - s.eye(252))
    return {"rates": [{"rate": str(rate), "multiplicity": int(s.trace(projector))}
                       for rate, projector in sorted(projectors.items(), key=lambda pair: str(pair[0]))],
            "nonzero_resonant_rates": resonant,
            "coefficients": [{"rate": str(rate), "time_power": degree, "matrix": encode(value)}
                             for (rate, degree), value in sorted(terms.items(), key=lambda pair: str(pair[0]))],
            "exact_full_ODE_and_initial_value": True}


def main():
    started = time.monotonic()
    source.source_matrices(ROOT)
    _, _, _, hashes = source.source.parse_source(ROOT)
    parent = json.loads((HERE.parent / "receipt.json").read_text())
    phase = json.loads((HERE.parents[1] / "full-phase/receipt.json").read_text())
    assert parent["source_sha256"] == phase["source_sha256"] == hashes
    principal = [decode(value) for value in phase["principal_coefficients"]]
    lapse = s.sympify(phase["source_lapse"])
    gamma0 = clean(lapse * principal[0] / s.I)
    spatial = [clean(-lapse * gamma0 * principal[j + 1] / s.I) for j in range(3)]
    h0 = decode(parent["original_H_free"])
    interaction = decode(parent["original_H_yukawa"])
    zero(interaction * interaction)
    z = 1 + 2 * s.I
    momenta = [[0, 0, 0], [0, 0, 3 * s.sqrt(2) / 2],
               [s.sqrt(2) / 3, 2 * s.sqrt(2) / 5, -s.sqrt(2) / 7]]
    cases = []
    for index, momentum in enumerate(momenta):
        free = clean(h0 + sum((x * h for x, h in zip(momentum, spatial)), s.zeros(252)))
        zero(free.H - free)
        groups = components(free)
        kernel = z * s.eye(252) - free
        inverse = block_inverse(kernel, groups)
        zero(kernel * inverse - s.eye(252))
        zero(inverse * kernel - s.eye(252))
        zero(interaction * inverse * interaction)
        whole = clean(inverse + inverse * interaction * inverse)
        zero(((kernel - interaction) * whole - s.eye(252)).applyfunc(canonical))
        zero((whole * (kernel - interaction) - s.eye(252)).applyfunc(canonical))
        assert s.simplify(s.trace(interaction * inverse)) == 0
        assert clean(inverse * interaction * inverse).todok()
        case = {"momentum": [str(x) for x in momentum], "energy": str(z),
                "source_free_components": [len(group) for group in groups],
                "two_sided_full_inverse": True, "Y_R0_Y_zero": True,
                "closed_Y_R0_trace_zero": True, "open_Y_response_nonzero": True}
        if index < 2:
            case["time"] = time_coefficients(free, interaction, groups)
        cases.append(case)
        print(json.dumps({"case": index, "momentum": case["momentum"],
                          "inverse": True, "time": index < 2,
                          "resonances": case.get("time", {}).get("nonzero_resonant_rates", [])}), flush=True)
    assert cases[1]["time"]["nonzero_resonant_rates"]
    receipt = {"scope": "ORIGINAL_252_TRIANGULAR_RESOLVENT_AND_EXACT_TIME_COEFFICIENTS",
               "source_sha256": hashes, "time_convention": "U(t)=sum exp(-i rate t)*t^power*coefficient",
               "projectors_generated_from_source_free_blocks": True,
               "full_real_dual_action_not_replaced_by_Hermitian_part": True,
               "cases": cases, "elapsed_seconds": round(time.monotonic() - started, 3)}
    (HERE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()

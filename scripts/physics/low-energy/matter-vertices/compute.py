#!/usr/bin/env python3
"""Full source matter bilinears coupled to every bosonic primitive.

All vertices come from det(e), adj(e), the actual Dirac connection and the
one-way Yukawa map.  The dual remains an independent complex-linear field.
"""
from __future__ import annotations
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import sys
import sympy as s

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / "nonlinear-contact"))
import exact_readout as source
from slice_checks import GAMMA, PAIRS


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def encode(matrix):
    return {"shape": list(matrix.shape), "entries": [
        [int(i), int(j), str(value)] for (i, j), value in sorted(s.SparseMatrix(matrix).todok().items())]}


def decode(record):
    return s.SparseMatrix(*record["shape"], {(i, j): s.sympify(value) for i, j, value in record["entries"]})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    _, vacuum, degrees, hashes = source.parse_source(args.root)
    original = json.loads((HERE.parent / "active-gauge/receipt.json").read_text())
    phase = json.loads((HERE.parent / "full-phase/receipt.json").read_text())
    n = s.sympify(original["source_lapse"])
    omega = s.sympify(original["source_frequency"])
    p = s.symbols("p0 p1 p2 p3", real=True)
    r = s.symbols("r0 r1 r2 r3", real=True)
    zero_p = dict.fromkeys(p, 0)
    pairs = list(PAIRS)
    bases = {degree: list(itertools.combinations(range(7), degree)) for degree in degrees}
    inside = [(degree, word) for degree in degrees for word in bases[degree]]
    gamma = [s.SparseMatrix(g) for g in GAMMA]
    Gamma = [clean(s.kronecker_product(g, s.eye(63))) for g in gamma]
    Q = decode(phase["phase_generator"])
    Y = decode(phase["original_Y"])
    C = list(map(decode, phase["principal_coefficients"]))
    D = clean(decode(phase["stationary_primal_constant"])+sum((p[mu]*C[mu] for mu in range(4)), s.zeros(252)))
    seed = s.MutableSparseMatrix(252, 1, {})
    for spin, word, value in [(0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)]:
        seed[63*spin+inside.index((2,word))] = value
    S = clean(s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1),s.eye(63)))
    dual = s.sqrt(2)*seed.T*S
    native = source.generators([(0,1,2),(3,4)])
    labels = [label for label, _, _ in native]
    assert labels == original["native_P286_labels"]
    rho = []
    rho4 = []
    for _, imaginary, matrix in native:
        factor = s.I if imaginary else 1
        internal = s.diag(*[s.SparseMatrix(source.exterior_action(matrix, degree))*factor for degree in degrees])
        rho.append(clean(s.kronecker_product(s.eye(4),internal)))
        rho4.append(s.SparseMatrix(source.exterior_action(matrix,4))*factor)
    spins = [clean(s.kronecker_product(gamma[a]*gamma[b]/2,s.eye(63))) for a,b in pairs]
    A0 = s.Matrix(original["actual_background"]["gauge_connection"]).applyfunc(s.sympify)
    O0 = s.Matrix(original["actual_background"]["lowered_Lorentz_connection"]).applyfunc(s.sympify)
    connections = [clean(sum((A0[mu,a]*rho[a] for a in range(12)),s.zeros(252))+
        sum((O0[mu,a]*spins[a] for a in range(6)),s.zeros(252))) for mu in range(4)]
    assert clean(sum((C[mu]*connections[mu] for mu in range(4)),s.zeros(252))-
        decode(phase["original_constant_B"])) == s.zeros(252)
    # Primitive jets retain the original graded time derivative under live coframe variation.
    jets = [[clean(s.I*Gamma[a]*(p[mu]*s.eye(252)+connections[mu])+
        (omega*Gamma[a]*Q if mu == 0 else s.zeros(252))) for a in range(4)] for mu in range(4)]
    e0 = s.diag(n,1,1,1)
    assert clean(sum((e0.adjugate()[mu,a]*jets[mu][a] for mu in range(4) for a in range(4)),s.zeros(252))+n*Y-n*D) == s.zeros(252)
    scalar = []
    for word in bases[4]:
        _, _, raw, _ = source.yukawa(Counter({word:1}))
        entry = s.MutableSparseMatrix(63,63,{})
        entry[:7,7:28] = s.SparseMatrix(raw)
        scalar.append(clean(s.kronecker_product(s.diag(0,0,1,1),entry)))
    vertices = []
    def append(group, coordinate, operator):
        vertices.append({"group":group,"coordinate":list(coordinate),"operator":clean(operator)})
    for mu in range(4):
        for a in range(12):
            append("gauge_A",(mu,a),n*C[mu]*rho[a])
    for mu in range(4):
        for a in range(6):
            append("Lorentz",(mu,a),n*C[mu]*spins[a])
    coframe_jets = []
    epsilon = s.symbols("epsilon", real=True)
    for a, nu in itertools.product(range(4), repeat=2):
        h = s.zeros(4); h[a,nu] = 1
        curve = e0+epsilon*h
        dadj = curve.adjugate().diff(epsilon).subs(epsilon,0)
        dvol = s.diff(curve.det(),epsilon).subs(epsilon,0)
        vertex = clean(sum((dadj[mu,b]*jets[mu][b] for mu in range(4) for b in range(4)),s.zeros(252))+dvol*Y)
        append("coframe",(a,nu),vertex)
        coframe_jets.append({"coordinate":[a,nu],"adjugate_derivative":encode(dadj),"volume_derivative":str(dvol)})
    for imaginary in range(2):
        for col in range(35):
            append("scalar",(imaginary,col),n*s.I**imaginary*scalar[col])
    assert len(vertices) == 158
    indexed = {(v["group"],tuple(v["coordinate"])):v["operator"] for v in vertices}
    vc = s.Matrix([vacuum.get(word,0) for word in bases[4]])
    orbit = [rho4[a]*vc for a in range(12)]
    source_vertices = {}
    for field_index, field in enumerate(original["fields"]):
        key = (field["group"],tuple(field["coordinate"]))
        if key in indexed:
            source_vertices[field_index] = indexed[key]
        elif field["group"] == "scalar_J":
            a = original["J_independent_columns"][field["coordinate"][0]]
            source_vertices[field_index] = clean(n*sum((orbit[a][col]*scalar[col] for col in range(35)),s.zeros(252)))
    # Actual occupied legs restore every boson/matter Hessian coefficient, including its momentum sign.
    occupied = [63*spin+inside.index((2,(color,5))) for spin in range(4) for color in range(3)]
    cross = {}
    for boson, vertex in source_vertices.items():
        left = clean(dual*vertex)
        right = clean(vertex.subs(zero_p)*seed)
        for index, field in enumerate(original["fields"]):
            if field["group"] not in ("primal_H","dual_H"):
                continue
            imaginary, spin, color = field["coordinate"]
            coord = occupied[spin*3+color]
            value = left[coord]*s.I**imaginary if field["group"] == "primal_H" else right[coord]*s.I**imaginary
            value = s.expand(s.re(value))
            if value:
                cross[boson,index] = value
    actual = {}
    for row,col,power,value in original["Fourier_Jacobi_entries"]:
        if row in source_vertices and original["fields"][col]["group"] in ("primal_H","dual_H"):
            actual[row,col] = actual.get((row,col),0)+s.sympify(value)*s.prod(v**degree for v,degree in zip(p,power))
    assert all(s.expand(cross.get(key,0)-actual.get(key,0)) == 0 for key in set(cross)|set(actual))
    print("PASS: all original97 bosonic vertices recover every original active matter Hessian leg",flush=True)
    # Full local internal gauge Ward identity: the background connection commutator is retained.
    def y_of(vector):
        return clean(sum((vector[col]*scalar[col] for col in range(35)),s.zeros(252)))
    shifted_D = D.subs(dict(zip(p,[p[mu]+r[mu] for mu in range(4)])),simultaneous=True)
    gauge_checks = []
    for a in range(12):
        action_variation = n*y_of(orbit[a])
        for mu in range(4):
            action_variation += n*C[mu]*(rho[a]*connections[mu]-connections[mu]*rho[a]-r[mu]*rho[a])
        residual = clean(action_variation+n*shifted_D*rho[a]-n*rho[a]*D)
        assert residual == s.zeros(252)
        gauge_checks.append(True)
        print("gauge Ward",labels[a],"verified",flush=True)
    print("PASS: all12 full252 local gauge Ward identities retain scalar and background commutators",flush=True)
    eta = s.diag(-1,1,1,1)
    lorentz_fundamental = []
    for a,b in pairs:
        generator = s.zeros(4)
        generator[a,b] = eta[a,a]; generator[b,a] = -eta[b,b]
        lorentz_fundamental.append(generator)
    lorentz_checks = []
    for a, generator in enumerate(lorentz_fundamental):
        h = generator*e0
        action_variation = sum((h[i,j]*indexed["coframe",(i,j)] for i,j in itertools.product(range(4),repeat=2)),s.zeros(252))
        for mu in range(4):
            action_variation += n*C[mu]*(spins[a]*connections[mu]-connections[mu]*spins[a]-r[mu]*spins[a])
        assert clean(action_variation+n*shifted_D*spins[a]-n*spins[a]*D) == s.zeros(252)
        lorentz_checks.append(True)
    print("PASS: all6 full252 local Lorentz identities include coframe and torsion sources",flush=True)
    result = {
        "scope":"FULL_ORIGINAL_MATTER_TO_BOSON_CUBIC_SOURCE_VERTICES",
        "source_sha256":hashes,
        "matter_coordinate_order":"spin-major; degrees6,2,4; lexicographic exterior basis",
        "source_convention":"L_cubic=sum_b delta_b * Re[zeta V_b(p) xi]; p differentiates primal; dual independent",
        "source_lapse":str(n),"source_frequency":str(omega),
        "full_stationary_Dirac_operator":encode(D),
        "primitive_vertices":[{"group":v["group"],"coordinate":v["coordinate"],"operator":encode(v["operator"])} for v in vertices],
        "coframe_actual_adjugate_and_volume_derivatives":coframe_jets,
        "active_289_bosonic_source_operators":[{"field":index,"operator":encode(value)} for index,value in source_vertices.items()],
        "all_original_boson_matter_Hessian_legs_match":True,
        "all_twelve_local_gauge_Ward_identities":all(gauge_checks),
        "all_six_local_Lorentz_Ward_identities":all(lorentz_checks),
        "canonical_real_source_kernel":"sqrt(2)/2 * (S V(p) + V(q)^dagger S), for Fourier-conjugate bra q and ket p",
        "metric_only_source_is_not_assumed":True,
        "complete_mediated_amplitude_generated":False,
        "empirical_state_or_unit_identification":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")


if __name__ == "__main__":
    main()

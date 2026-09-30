#!/usr/bin/env python3
"""Canonical reaction of the complete matter carrier to the source fields.

The temporal principal varies with the coframe.  Differentiating its inverse
is part of the Legendre transform, so a density vertex is not itself the
Hamiltonian vertex.  The independent canonical momentum is retained.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, P, decode, read

K = s.symbols("k1:4", real=True)


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    residual = clean(left-right)
    assert not residual.todok(), list(residual.todok().items())[:3]


def encode(matrix):
    return {"shape": list(matrix.shape), "entries": [
        [int(i), int(j), str(value)] for (i, j), value in sorted(clean(matrix).todok().items())]}


def affine(matrix):
    constant = clean(matrix.subs(dict.fromkeys(K, 0)))
    coefficients = [clean(matrix.diff(k)) for k in K]
    assert all(not value.free_symbols for value in coefficients)
    equal(matrix, constant+sum((k*A for k,A in zip(K,coefficients)), s.zeros(*matrix.shape)))
    return {"constant": constant, **dict(zip(map(str,K),coefficients))}


def orthogonal_complement(free, projector):
    complement = s.eye(252)-projector
    vectors, pivots = [], []
    for column in range(252):
        vector = complement[:, column]
        for previous in vectors:
            vector = clean(vector-previous*(previous.H*vector)[0])
        norm = s.simplify((vector.H*vector)[0])
        if norm:
            assert norm.is_positive
            vectors.append(clean(vector/s.sqrt(norm)))
            pivots.append(column)
    frame = s.SparseMatrix.hstack(*vectors)
    assert frame.shape == (252,36)
    equal(frame.H*frame,s.eye(36))
    equal(frame*frame.H,complement)
    equal(free.H*frame,s.zeros(216,36))
    return frame,pivots


class MatterPorts:
    def __init__(self):
        self.vertices = read("matter-vertices/receipt.json")
        self.phase = read("full-phase/receipt.json")
        self.quantum = read("full-quantum/receipt.json")
        self.modes = read("matter-modes/source.json")
        self.N = s.sympify(self.vertices["source_lapse"])
        self.D = decode(self.vertices["full_stationary_Dirac_operator"])
        self.E = clean(self.N*self.D.diff(P[0]))
        self.inverse_E = clean(decode(self.quantum["time_principal_inverse"])/self.N)
        equal(self.E*self.inverse_E,s.eye(252))
        equal(self.inverse_E*self.E,s.eye(252))
        self.spatial_substitution = {P[0]:0, **dict(zip(P[1:], [s.I*k for k in K]))}
        self.drift = clean(self.N*self.D.subs(self.spatial_substitution))
        equal(self.N*self.D.subs(dict(zip(P[1:],[s.I*k for k in K]))),
              P[0]*self.E+self.drift)
        self.H = clean(-s.I*self.inverse_E*self.drift)
        equal(self.E*(-s.I*self.H)+self.drift,s.zeros(252))
        # This is the same stationary generator, not a Hermitian part or an
        # independently chosen positive-metric replacement.
        H_original = decode(self.quantum["original_H_full"])
        Q = decode(self.phase["phase_generator"])
        omega = s.sympify(self.phase["source_frequency"])
        equal(self.H.subs(dict.fromkeys(K,0)),H_original-omega*Q)
        self.F = decode(self.modes["source_isometry"])
        self.Pfree = decode(self.modes["free_projection"])
        equal(self.F.H*self.F,s.eye(216))
        equal(self.F*self.F.H,self.Pfree)
        self.G,self.complement_pivots = orthogonal_complement(self.F,self.Pfree)
        equal(self.Pfree*self.H,self.H*self.Pfree)

    def port(self, operator):
        temporal = clean(operator.diff(P[0]))
        constant = clean(operator.subs(self.spatial_substitution))
        equal(operator.subs(dict(zip(P[1:],[s.I*k for k in K]))),P[0]*temporal+constant)
        assert not temporal.free_symbols
        inverse_correction = clean(-self.inverse_E*temporal*self.H)
        direct = clean(-s.I*self.inverse_E*constant)
        reaction = clean(inverse_correction+direct)
        # The derivative of E(epsilon)(-i H(epsilon))+K(epsilon)=0.
        equal(self.E*(-s.I*reaction)+temporal*(-s.I*self.H)+constant,s.zeros(252))
        # At fixed independent canonical momentum pi=-i chi E, the variation
        # of the original density on a matter solution is -pi W psi.
        equal(s.I*self.inverse_E*(constant-s.I*temporal*self.H),-reaction)
        return {"temporal":temporal,"drift":constant,"reaction":reaction,
                "inverse_correction":inverse_correction}


def main():
    started=time.monotonic()
    source=MatterPorts()
    charges=read("matter-charge-selection/receipt.json")
    for receipt in [source.vertices,source.phase,source.quantum,source.modes,charges]:
        for name,digest in receipt["source_sha256"].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    sectors=charges["matter_commutant"]["diagonal_sectors"]
    assert sorted(i for sector in sectors for i in sector)==list(range(63))
    charge_of={spin*63+i:a for a,sector in enumerate(sectors) for spin in range(4) for i in sector}
    for matrix in [source.E,source.inverse_E,source.H]:
        assert all(charge_of[i]==charge_of[j] for i,j in matrix.todok())
    assert all(charge_of[i]==0 for i,_ in source.G.todok())
    ports,summary,spanning,labels=[],{},[],[]
    complement_generators=[]
    for monomial,matrix in affine(clean(source.G.H*source.H*source.G)).items():
        if matrix.todok():
            complement_generators.append(({"kind":"source_H","coefficient":monomial},matrix))
    correction_witness=None
    for number,entry in enumerate(source.vertices["primitive_vertices"]):
        port=source.port(decode(entry["operator"]))
        W=port["reaction"]
        assert all(charge_of[i]==charge_of[j] for i,j in W.todok())
        outgoing=clean(source.G.H*W*source.F)
        returning=clean(source.F.H*W*source.G)
        for monomial,matrix in affine(clean(source.G.H*W*source.G)).items():
            if matrix.todok():
                complement_generators.append(({"kind":"primitive_reaction","vertex":number,
                    "group":entry["group"],"coordinate":entry["coordinate"],
                    "coefficient":monomial},matrix))
        count=summary.setdefault(entry["group"],{"count":0,"free_to_complement_nonzero":0,
                                                "complement_to_free_nonzero":0})
        count["count"]+=1
        count["free_to_complement_nonzero"]+=bool(outgoing.todok())
        count["complement_to_free_nonzero"]+=bool(returning.todok())
        for monomial,matrix in affine(outgoing).items():
            for column in sorted({j for _,j in matrix.todok()}):
                spanning.append(matrix[:,column])
                labels.append({"primitive_vertex":number,"group":entry["group"],
                               "coordinate":entry["coordinate"],"momentum_coefficient":monomial,
                               "free_input_coordinate":column})
        if port["inverse_correction"].todok() and correction_witness is None:
            (i,j),value=next(iter(port["inverse_correction"].todok().items()))
            correction_witness={"primitive_vertex":number,"group":entry["group"],
                "coordinate":entry["coordinate"],"row":i,"column":j,"missing_term":str(value)}
        ports.append({"group":entry["group"],"coordinate":entry["coordinate"],
            "temporal_principal_variation":encode(port["temporal"]),
            "Hamiltonian_coefficients":{k:encode(v) for k,v in affine(W).items()},
            "free_to_complement":{k:encode(v) for k,v in affine(outgoing).items()},
            "complement_to_free":{k:encode(v) for k,v in affine(returning).items()}})
    assert len(ports)==158 and correction_witness is not None
    print("PASS all158 full252 Legendre tangents, coframe principal correction and original charge sectors",flush=True)
    reach=s.SparseMatrix.hstack(*spanning)
    # Positive Gram spans exactly the actual source-generated outgoing image.
    gram=clean(reach*reach.H)
    rank=gram.rank()
    _,pivots=reach.rref()
    basis=reach[:,list(pivots)]
    assert basis.rank()==rank
    print("PASS first source-generated nonfree image rank",rank,"of36",flush=True)
    closure_basis=basis
    closure_trace=[{"stage":0,"complement_rank":0},{"stage":1,"complement_rank":rank}]
    closure_steps=[]
    while True:
        images=[closure_basis]+[clean(matrix*closure_basis) for _,matrix in complement_generators]
        enlarged=s.SparseMatrix.hstack(*images)
        _,new_pivots=enlarged.rref()
        new_basis=enlarged[:,list(new_pivots)]
        assert new_basis.cols>=closure_basis.cols
        closure_steps.append({"old_rank":closure_basis.cols,"new_rank":new_basis.cols,
                              "selected_image_columns":list(new_pivots)})
        if new_basis.cols==closure_basis.cols:
            break
        closure_basis=new_basis
        closure_trace.append({"stage":len(closure_trace),"complement_rank":closure_basis.cols})
    # One actual projector certifies closure under every source coefficient.
    closure_projector=clean(closure_basis*(closure_basis.H*closure_basis).inv()*closure_basis.H)
    equal(closure_projector*reach,reach)
    for _,matrix in complement_generators:
        equal(closure_projector*matrix*closure_basis,matrix*closure_basis)
    assert closure_projector.rank()==closure_basis.cols
    print("PASS full source reaction closure:",[item["complement_rank"] for item in closure_trace],
          "final matter carrier",216+closure_basis.cols,flush=True)
    active=[]
    for entry in source.vertices["active_289_bosonic_source_operators"]:
        port=source.port(decode(entry["operator"]))
        active.append({"field":entry["field"],"Hamiltonian_coefficients":{
            k:encode(v) for k,v in affine(port["reaction"]).items()},
            "temporal_principal_variation":encode(port["temporal"])})
    assert len(active)==97
    paths=[BASE/name for name in ["matter-vertices/receipt.json","full-phase/receipt.json",
        "full-quantum/receipt.json","matter-modes/source.json","matter-charge-selection/receipt.json"]]
    result={"root":ROOT_ID,"scope":"FULL252_SOURCE_LEGENDRE_REACTION_PORTS_AND_FREE_CARRIER_COMPLETION",
        "source_sha256":source.vertices["source_sha256"],
        "input_sha256":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        "physical_lapse":str(source.N),"physical_momentum_variables":list(map(str,K)),
        "density_temporal_principal":encode(source.E),"density_temporal_inverse":encode(source.inverse_E),
        "stationary_Hamiltonian_coefficients":{k:encode(v) for k,v in affine(source.H).items()},
        "original_time_identity":"H_original=H_stationary+omega*Q; source clock unchanged",
        "canonical_momentum":"pi=-i*chi*(N*C0), chi independent; no positive-adjoint identification supplied",
        "Hamiltonian_variation":"W_a=-E^-1 E_a H-i E^-1 K_a, V_a=E_a*p0+K_a(k)",
        "original_equation_variation":"E*(-i W_a)+E_a*(-i H)+K_a=0",
        "action_reaction_pairing":"on psi_dot=-i H psi, chi*V_a*psi=-pi*W_a*psi",
        "primitive_ports":ports,"active_97_ports":active,
        "all158_original_equations_and_Legendre_pairings_checked":True,
        "coframe_inverse_derivative_negative_control":correction_witness,
        "all158_preserve_original12_matter_sector_numbers":True,
        "vertex_group_transport":summary,
        "free_frame_dimension":216,"complement_frame":encode(source.G),
        "complement_frame_coordinate_pivots":source.complement_pivots,
        "complement_original_sector":0,"complement_image_rank":rank,
        "first_reaction_carrier_dimension":216+rank,
        "source_generated_invariant_carrier_dimension":216+closure_basis.cols,
        "invariant_closure_trace":closure_trace,"invariant_closure_steps":closure_steps,
        "complement_generator_labels":[label for label,_ in complement_generators],
        "complement_closure_basis":encode(closure_basis),
        "complement_closure_projector":encode(closure_projector),
        "image_basis":encode(basis),"image_basis_source_columns":[labels[i] for i in pivots],
        "image_gram":encode(gram),
        "free_family_interaction_invariant":rank==0,
        "Fock_consumer":"the source coefficient W_a enters the existing full252 dGamma; its bosonic coefficient remains the original field variable",
        "reaction_scope":"derivative of the original canonical matter generator in every source field direction, with full field equation readback; coupled field feedback and spectral measure remain separate consumers",
        "lifetime_status":"SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED",
        "elapsed_seconds":round(time.monotonic()-started,3)}
    (HERE/"full-matter-ports.json").write_text(json.dumps(result,separators=(",",":"))+"\n")
    print("PASS all97 active reaction ports and constructive full matter carrier feed",flush=True)


if __name__=="__main__":
    main()

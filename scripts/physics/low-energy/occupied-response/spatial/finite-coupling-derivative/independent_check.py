#!/usr/bin/env python3
"""Differentiate an exact noncommuting finite source flow, rather than an affine path."""
import argparse
import json
from pathlib import Path
import re

import mpmath as mp
import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    root=parser.parse_args().root.resolve()
    base=root/"Verification/physics/low-energy-phenomenology"
    audit=base/"occupied-response/spatial/finite-coupling/derivative/audit"
    receipt=json.loads((base/"occupied-response/receipt.json").read_text())
    def decode(value):return s.Matrix(*value["shape"],lambda i,j:0) if not value["entries"] else s.SparseMatrix(
        *value["shape"],{(i,j):s.sympify(v) for i,j,v in value["entries"]})
    def scalar(value):return s.factor(s.trigsimp(s.simplify(value)))
    def clean(value):return s.Matrix(value).applyfunc(scalar)
    def equal(left,right):
        difference=clean(left-right)
        if difference!=s.zeros(left.rows,left.cols):
            difference=difference.applyfunc(lambda x:s.trigsimp(s.expand_complex(x)))
        assert difference==s.zeros(left.rows,left.cols)
    text=(root/"Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean").read_text()
    literal=re.search(r"def diracGammaZero\s*:.*?:=\s*!!\[(.*?)\]",text,re.S).group(1)
    gamma0=s.Matrix([[s.sympify(v.strip()) for v in row.split(",")] for row in literal.split(";")])
    N=3*s.sqrt(30)/25;omega=18*s.sqrt(15)/125;spin=s.sqrt(2)
    Q=s.kronecker_product(s.diag(-1,-1,1,1),s.eye(3))
    swap=s.kronecker_product(gamma0*s.diag(-1,-1,1,1),s.eye(3))
    rho=s.Matrix([[0,1,0],[-1,0,0],[0,0,0]])
    dirac=s.I*s.kronecker_product(gamma0,rho)/N
    T=clean(N*s.kronecker_product(gamma0,s.eye(3))*dirac)
    B=clean(N*spin*swap*dirac)
    H=decode(receipt["stationary_H_constant"]);w=decode(receipt["source_prepared"])
    equal(T,decode(receipt["gauge_Hamiltonian_forces"][0]))
    equal(B,decode(receipt["original_current_readers"][0]));equal(B,-spin*Q*T)
    r=T*w;q=Q*r;p=Q*w
    frame=s.Matrix.hstack(w,r,q,p)
    equal(frame.H*frame,s.eye(4))
    h=clean(frame.H*H*frame);force=clean(frame.H*T*frame);current=clean(frame.H*B*frame)
    charge=clean(frame.H*Q*frame)
    equal(H*frame,frame*h);equal(T*frame,frame*force);equal(B*frame,frame*current)
    assert h*force!=force*h
    frequency=s.Symbol("omega",positive=True,real=True)
    epsilon,time=s.symbols("epsilon physical_time",real=True)
    # Diagonalize Q, not the epsilon-dependent target propagator.
    e=s.eye(4)
    J=s.Matrix.hstack(e[:,0]+e[:,3],e[:,1]+e[:,2],e[:,0]-e[:,3],e[:,1]-e[:,2])/s.sqrt(2)
    equal(J.H*J,s.eye(4))
    equal(J.H*charge*J,s.diag(1,1,-1,-1))
    sx=s.Matrix([[0,1],[1,0]]);sz=s.diag(1,-1)
    equal(J.H*h*J,s.diag(0,2*omega,0,-2*omega))
    equal(J.H*force*J,s.diag(sx,sx))
    rate=s.sqrt(frequency**2+epsilon**2)
    blocks=[]
    for sign in (1,-1):
        K=sign*frequency*s.eye(2)+epsilon*sx-sign*frequency*sz
        U=s.exp(-s.I*sign*frequency*time)*(s.cos(rate*time)*s.eye(2)
            -s.I*s.sin(rate*time)/rate*(epsilon*sx-sign*frequency*sz))
        equal(U.subs(time,0),s.eye(2))
        equal(U.diff(time),-s.I*K*U)
        equal(U.H*U,s.eye(2))
        blocks.append(U)
    finite=J*s.diag(*blocks)*J.H
    baseline=clean(finite.subs(epsilon,0))
    tangent=clean(finite.diff(epsilon).subs(epsilon,0))
    H4=s.Matrix([[0,0,0,0],[0,0,2*frequency,0],[0,2*frequency,0,0],[0,0,0,0]])
    equal(tangent.subs(time,0),s.zeros(4))
    equal(tangent.diff(time),-s.I*H4*tangent-s.I*force*baseline)
    # The derivative is full operator-valued; every actual source row is checked.
    delta_full=frame*tangent
    equal(delta_full.diff(time).subs(frequency,omega),
        -s.I*H*delta_full.subs(frequency,omega)-s.I*T*frame*baseline.subs(frequency,omega))
    expected_delta=(s.cos(2*frequency*time)-1)*e[:,2]/(2*frequency)
    expected_delta-=s.I*s.sin(2*frequency*time)*e[:,1]/(2*frequency)
    equal(tangent*e[:,0],expected_delta)
    # Compute the finite current first, then differentiate that exact expression.
    prepared=s.Matrix([1,0])
    finite_current=0
    for sign,U in zip((1,-1),blocks):
        finite_current+=(prepared.T*U.H*(-sign*spin*sx)*U*prepared)[0]/2
    finite_current=scalar(finite_current)
    expected_current=spin*epsilon*frequency/(frequency**2+epsilon**2)*(1-s.cos(2*rate*time))
    assert scalar(finite_current-expected_current)==0
    derivative=scalar(s.diff(finite_current,epsilon).subs(epsilon,0))
    expected_derivative=spin*(1-s.cos(2*frequency*time))/frequency
    assert scalar(derivative-expected_derivative)==0
    two_legs=scalar(((tangent*e[:,0]).H*current*e[:,0]+e[:,0].T*current*tangent*e[:,0])[0])
    assert scalar(derivative-two_legs)==0
    tau=s.Symbol("integration_time",real=True)
    kubo_integrand=2*spin*s.sin(2*frequency*(time-tau))
    primitive=spin*s.cos(2*frequency*(time-tau))/frequency
    assert scalar(s.diff(primitive,tau)-kubo_integrand)==0
    assert scalar(primitive.subs(tau,time)-primitive.subs(tau,0)-derivative)==0
    naive=-s.I*time*baseline*force
    order_control=clean((tangent-naive).diff(time,2).subs(time,0))
    equal(order_control,H4*force-force*H4)
    assert order_control!=s.zeros(4)
    wrong_current=scalar(((tangent*e[:,0]).H*force*e[:,0]+e[:,0].T*force*tangent*e[:,0])[0])
    assert wrong_current==0
    equal(charge*tangent,tangent*charge)
    z=s.Symbol("original_phase",nonzero=True)
    P=J*s.diag(z,z,1/z,1/z)*J.H
    equal(P*tangent,tangent*P)
    equal(P.subs(z,1/z)*current*P,current)

    # Supplement the exact identities with an operator-norm remainder check at
    # positive and negative epsilon/time; the universal estimate itself is Lean.
    mp.mp.dps=50
    finite_numeric=s.lambdify((frequency,epsilon,time),finite,"mpmath")
    baseline_numeric=s.lambdify((frequency,time),baseline,"mpmath")
    tangent_numeric=s.lambdify((frequency,time),tangent,"mpmath")
    wnum=mp.mpf(18)*mp.sqrt(15)/125
    ratios=[]
    for eps,t in ((mp.mpf('0.7'),mp.mpf('0.3')),(-mp.mpf('0.7'),mp.mpf('0.3')),
            (mp.mpf('0.2'),-mp.mpf('0.4')),(-mp.mpf('0.01'),-mp.mpf('0.8')),
            (mp.mpf('0.001'),mp.mpf('0.1'))):
        error=finite_numeric(wnum,eps,t)-baseline_numeric(wnum,t)-eps*tangent_numeric(wnum,t)
        singular=mp.sqrt(max(mp.eighe(error.H*error,eigvals_only=True)))
        ratio=singular/(eps**2*t**2)
        assert ratio<1
        ratios.append(str(ratio))
    result={"status":"PASS","source_channel":"original A01 temporal gauge force and B=-sqrt(2)Q T",
        "actual_invariant_subspace_dimension":4,"finite_epsilon_solution":"two Q-eigenblocks; each exp(-i H_epsilon t)",
        "parameter_regularness_not_assumed":True,"complete_actual_12_by_4_tangent_rows":True,
        "finite_current":str(expected_current),"true_finite_current_epsilon_zero_derivative":str(expected_derivative),
        "exact_Kubo_integral_matches":True,"naive_factored_derivative_fails_by":"[H,T] at second time derivative",
        "wrong_T_current_derivative":str(wrong_current),"operator_remainder_numeric_ratios_M_one":ratios,
        "phase_preparation_commutation_on_true_tangent":True,
        "scope":"Exact source-fiber finite epsilon/true derivative controls; universal L2 and operator norm differentiation are Lean theorems."}
    (audit/"independent-receipt.json").write_text(json.dumps(result,indent=2)+"\n")
    print("PASS exact noncommuting finite-epsilon derivative, original current/Kubo, phase, and operator remainder controls")


if __name__=="__main__":main()

#!/usr/bin/env python3
"""Lift the existing 289 background feedback, then generate its nonlinear remainder.

The complete Jacobi field already includes primal/dual background response.
Returning that same linear response again would count it twice.  The native
Euler residual beyond that Jacobi term is the source for the next correction.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from spectral_splice import NativeMatterReaction, clean, equal, encode


def matter_lift(source, fields):
    inside=[(degree,word) for degree in [6,2,4]
            for word in itertools.combinations(range(7),degree)]
    primal=s.zeros(252,1)
    dual=s.zeros(1,252)
    for index,entry in enumerate(source.active['fields']):
        if entry['group'] not in ('primal_H','dual_H'): continue
        imaginary,spin,color=entry['coordinate']
        coordinate=63*spin+inside.index((2,(color,5)))
        value=s.I**imaginary*fields[index]
        if entry['group']=='primal_H': primal[coordinate]+=value
        else: dual[coordinate]+=value
    return clean(primal),clean(dual)


def main():
    started=time.monotonic()
    native=NativeMatterReaction()
    source=native.source
    data=json.loads((HERE/'dynamic.json').read_text())
    assert data['root']==ROOT_ID and data['source_sha256']==source.vertices['source_sha256']
    occupied=json.loads((BASE/'occupied-response/receipt.json').read_text())
    assert occupied['source_sha256']==source.vertices['source_sha256']
    w=clean(decode(occupied['occupied_frame'])*decode(occupied['source_prepared']))
    psi=2*w
    chi=clean(2*s.sqrt(2)*w.H*source.S)
    p=list(s.symbols('p0:4'))
    at=lambda V,r:clean(V.subs(dict(zip(p,r))))
    zero=s.zeros(4,1)
    samples=[]
    for sample in data['samples']:
        for name,sign in [('response',1),('opposite_response',-1)]:
            r=sign*decode(sample['transfer'])
            field=-decode(sample[name]['field289'])
            x,z=matter_lift(source,field)
            primal_insertion=clean(sum((field[a]*at(V,zero) for a,V in zip(source.order,source.V)),s.zeros(252)))
            dual_insertion=clean(sum((field[a]*at(V,-r) for a,V in zip(source.order,source.V)),s.zeros(252)))
            equal(source.N*at(source.D,r)*x+primal_insertion*psi,s.zeros(252,1))
            equal(z*source.N*at(source.D,-r)+chi*dual_insertion,s.zeros(1,252))
            wrong=clean(z*source.N*at(source.D,-r)+chi*primal_insertion)
            samples.append({'sample':sample['name'],'order':name,'transfer':encode(r),
                'primal':encode(x),'dual':encode(z),'full252_primal_residual_zero':True,
                'full252_dual_residual_zero':True,
                'omitting_dual_coframe_derivatives_residual_nonzero_entries':len(wrong.todok())})
    assert any(row['omitting_dual_coframe_derivatives_residual_nonzero_entries'] for row in samples)
    print('PASS both ordered fields at both transfers recover all252 primal and dual background reactions',flush=True)

    # Physical real Fourier fields have real coordinate values and derivatives.
    # Pack the primal/dual real and imaginary coordinate pairs only afterwards.
    sample=next(row for row in data['samples'] if row['name']=='energy_transfer')
    r=decode(sample['transfer'])
    harmonic=-decode(sample['response']['field289'])
    field=clean(harmonic.applyfunc(s.re))
    derivative_fields=[clean((r[mu]*harmonic).applyfunc(s.re)) for mu in range(4)]
    x,z=matter_lift(source,field)
    derivatives=[matter_lift(source,derivative) for derivative in derivative_fields]
    epsilon,t=s.symbols('epsilon t',real=True)
    live=native.densitized(epsilon*field,s.zeros(3,1))
    psi_curve=psi+epsilon*x
    chi_curve=chi+epsilon*z
    primal=clean(live['K']*psi_curve+sum((live['contracted'][mu]*epsilon*derivatives[mu][0]
                                      for mu in range(4)),s.zeros(252,1)))
    divergence=s.zeros(252)
    for mu in range(4):
        de=s.zeros(4)
        for index in source.order:
            entry=source.active['fields'][index]
            if entry['group']=='coframe': de[tuple(entry['coordinate'])]=epsilon*derivative_fields[mu][index]
        changed=live['coframe']+t*de
        derivative_adjugate=clean(changed.adjugate(method='berkowitz').diff(t).subs(t,0))
        divergence+=sum((derivative_adjugate[mu,a]*s.I*native.Gamma[a] for a in range(4)),s.zeros(252))
    dual=clean(chi_curve*live['K']-sum((epsilon*derivatives[mu][1]*live['contracted'][mu]
                                    for mu in range(4)),s.zeros(1,252))-chi_curve*divergence)
    polynomial=[]
    for label,value in [('primal',primal),('dual',dual)]:
        degree=max((s.degree(entry,epsilon) for entry in value.todok().values()),default=0)
        coefficients=[clean(value.applyfunc(lambda entry:s.expand(entry).coeff(epsilon,k))) for k in range(degree+1)]
        equal(coefficients[0],s.zeros(*value.shape))
        equal(coefficients[1],s.zeros(*value.shape))
        assert coefficients[2].todok()
        assert any(coefficient.todok() for coefficient in coefficients[2:])
        polynomial.append({'side':label,'degree':int(degree),'constant_and_Jacobi_coefficient_zero':True,'quadratic_coefficient_nonzero':True,
            'nonlinear_coefficients':[{'order':k,'value':encode(coefficient)}
                for k,coefficient in enumerate(coefficients) if k>=2 and coefficient.todok()]})
        print('PASS native',label,'Euler polynomial, zero constant/linear, nonlinear orders',
              [k for k,coefficient in enumerate(coefficients) if k>=2 and coefficient.todok()],flush=True)
    paths=[HERE/'dynamic.json',HERE/'spectral_splice.py',BASE/'occupied-response/receipt.json',
           BASE/'full-phase/receipt.json',BASE/'active-gauge/receipt.json',BASE/'matter-vertices/receipt.json']
    output={'root':ROOT_ID,'source_sha256':source.vertices['source_sha256'],
        'scope':'FULL252_EMBEDDED_JACOBI_REACTION_AND_NATIVE_NONLINEAR_MATTER_REMAINDER',
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'full252_linear_consumers':samples,
        'physical_real_source':{'field_at_phase_zero':encode(field),
            'coordinate_derivatives':[encode(v) for v in derivative_fields],
            'primal_background':encode(psi),'dual_background':encode(chi),
            'primal_first_correction':encode(x),'dual_first_correction':encode(z),
            'source_bilinear_amplitude':'4*sqrt(2)'},
        'native_remainder':polynomial,
        'equations':{'primal':'K(e,A,Omega,phi) psi + sum_mu E_mu(e) partial_mu psi',
            'dual':'chi K(e,A,Omega,phi) - sum_mu (partial_mu chi) E_mu(e) - chi sum_mu partial_mu E_mu(e)',
            'next_forcing':'negative of the generated epsilon^2 and higher Euler coefficients; no repeated Jacobi reaction'},
        'consumer_contract':'the next constrained correction must consume these full matter Euler rows together with the bosonic nonlinear remainder in the same occurrence',
        'scope_note':'actual source harmonic value/derivatives and full original matter action are consumed; this does not yet solve the nonlinear constrained field equation or its quantum spectrum',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'spectral_splice_linear.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS same-occurrence linear feedback consumed once; actual next nonlinear matter forcing generated',flush=True)


if __name__=='__main__':
    main()

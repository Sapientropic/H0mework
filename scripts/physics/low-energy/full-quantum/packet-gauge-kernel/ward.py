#!/usr/bin/env python3
"""Off-shell Noether contact of the same primitive connection family.

The differentiated Ward source is generated from the background Euler vector
and the literal linear field action, independently of H1 times a chosen field.
"""
import itertools
import json
from pathlib import Path
import time
import sympy as s
import source

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
p=s.symbols('p0:4',real=True)
clean,encode=source.clean,source.encode


def decode(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v) for i,j,v in record['entries']})


def operator(entries,rows=289,cols=289,values=p):
    result=s.MutableSparseMatrix(rows,cols,{})
    for i,j,powers,value in entries:
        result[i,j]+=s.sympify(value)*s.prod(x**n for x,n in zip(values,powers))
    return clean(result)


def main():
    start=time.monotonic()
    original=json.loads((BASE/'active-gauge/receipt.json').read_text())
    syms=json.loads((BASE/'active-gauge/symmetries.json').read_text())
    data=json.loads((HERE/'source.json').read_text())
    E=decode(data['E1']);rho=list(map(decode,data['scalar_rho']))
    gen=list(map(decode,data['fundamental']));inc=decode(data['scalar_J_inclusion'])
    idx={(f['group'],tuple(f['coordinate'])):i for i,f in enumerate(original['fields'])}
    gram=s.Matrix(12,12,lambda i,j:s.re(-s.trace(gen[i]*gen[j])))
    gi=gram.inv()
    adjoint=[]
    for a in range(12):
        cols=[]
        for b in range(12):
            comm=gen[a]*gen[b]-gen[b]*gen[a]
            cols.append(gi*s.Matrix([s.re(-s.trace(g*comm)) for g in gen]))
        adjoint.append(s.Matrix.hstack(*cols))
    H0=operator(original['Fourier_Jacobi_entries'])
    H1=operator(data['H1']);H2=operator(data['H2'])
    Tg=operator(original['source_primitive_gauge_tangent'],cols=12)
    Tg1=s.zeros(289,12)
    for g in range(12):
        for c in range(12):Tg1[idx['gauge_A',(1,c)],g]=adjoint[g][c,1]
    native=source.load(BASE/'active-gauge/compute.py','kernel_ward_native')

    def field_action_gauge(g):
        result=s.MutableSparseMatrix(289,289,{})
        for group,count in [('gauge_A',4),('gauge_B',6)]:
            for mu in range(count):
                for (a,b),coefficient in s.SparseMatrix(adjoint[g]).todok().items():
                    result[idx[group,(mu,a)],idx[group,(mu,b)]]=coefficient
        internal=s.kronecker_product(s.eye(4),gen[g][:3,:3]+gen[g][5,5]*s.eye(3))
        for group,matrix in [('primal_H',internal),('dual_H',-internal.T)]:
            real=native.active.realify(matrix)
            for (a,b),coefficient in s.SparseMatrix(real).todok().items():
                result[idx[group,(a//12,(a%12)//3,a%3)],idx[group,(b//12,(b%12)//3,b%3)]]=coefficient
        # E1 has no scalar component. The exact action on the larger scalar
        # carrier can therefore be paired with E1 before this restriction.
        assert E[:9,:]==s.zeros(9,1)
        return s.SparseMatrix(result)

    gauge_actions=[field_action_gauge(g) for g in range(12)]
    Cg=clean(s.SparseMatrix.hstack(*(action.T*E for action in gauge_actions)))
    assert clean(H1*Tg+H0*Tg1+Cg)==s.zeros(289,12)
    assert clean(H2*Tg+H1*Tg1)==s.zeros(289,12)
    assert clean(H2*Tg1)==s.zeros(289,12)
    assert Cg.todok()
    print('PASS all12 original off-shell Ward polynomial coefficients, contact generated from E1',flush=True)

    K=operator(syms['source_symmetry_tangents_112'],cols=9)
    for step in reversed(original['algebraic_Schur_steps']):
        W=operator(step['write_back_auxiliary_from_retained'])
        K=clean(K+W*K)
    assert clean(H0*K)==s.zeros(289,9)
    color=s.zeros(12,3);color[1,0]=s.Rational(1,2);color[0,1]=s.Rational(1,2)
    color[6,2]=s.Rational(1,2);color[7,2]=-s.Rational(1,2)
    assert clean(K[:,:3]-Tg*color)==s.zeros(289,3)
    K1=clean((Tg1*color).row_join(s.zeros(289,6)))
    C=s.MutableSparseMatrix(289,9,{})
    C[:,:3]=Cg*color
    for k,(a,b) in enumerate(native.PAIRS):
        action=s.MutableSparseMatrix(289,289,{})
        lor=s.zeros(4);lor[a,b]=native.ETA[a,a];lor[b,a]=-native.ETA[b,b]
        for mu in range(4):
            for (i,j),value in s.SparseMatrix(lor).todok().items():
                action[idx['coframe',(i,mu)],idx['coframe',(j,mu)]]=value
        spin=s.kronecker_product(native.GAMMA[a]*native.GAMMA[b]/2,s.eye(3))
        for group,matrix in [('primal_H',spin),('dual_H',-spin.T)]:
            real=native.active.realify(matrix)
            for (i,j),value in s.SparseMatrix(real).todok().items():
                action[idx[group,(i//12,(i%12)//3,i%3)],idx[group,(j//12,(j%12)//3,j%3)]]=value
        # Other Lorentz-field derivatives pair with identically zero E1 rows.
        C[:,k+3]=action.T*E
    C=clean(C)
    assert clean(H1*K+H0*K1+C)==s.zeros(289,9)
    assert clean(H2*K+H1*K1)==s.zeros(289,9)
    assert clean(H2*K1)==s.zeros(289,9)
    assert C.todok()
    print('PASS original3SU2+6Lorentz full289 off-shell Ward including E1 contact',flush=True)
    naive=clean(H1*K+H0*K1)
    assert naive==-C and naive.todok()
    result={'scope':'STRIKE_OFF_SHELL_SOURCE_WARD_FAMILY_CONTACT',
        'source_sha256':original['source_sha256'],
        'formal_symbols':list(map(str,p)),'K0':encode(K),'K1':encode(K1),'C1':encode(C),
        'gauge12_T0':encode(Tg),'gauge12_T1':encode(Tg1),'gauge12_C1':encode(Cg),
        'definitions':'C1_g=(D fieldGaugeAction_g)^T E1; K_epsilon=K0+epsilon*K1',
        'identities':['H0*K0=0','H1*K0+H0*K1=-C1','H2*K0+H1*K1=0','H2*K1=0'],
        'all12_fixed_v_torque_independent_of_epsilon':True,
        'off_shell_Ward':'H_epsilon*K_epsilon=-epsilon*C1 on the9 true source symmetries',
        'contact_nonzero_entries':len(C.todok()),
        'negative_control_on_shell_Ward_assumption_fails':True,
        'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'ward.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS primitive Ward/contact construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()

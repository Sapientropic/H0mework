#!/usr/bin/env python3
"""Actual H0 label support and the original H raising counterleg."""
from pathlib import Path
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_live_differential_hamiltonian import SourceLiveDifferentialHamiltonian, clean
from source_joint_form_hamiltonian import read_bound
from source_gauss_quantum_current import apply_superposition, weighted_sum
from source_lorentz_contact import GAMMA


def occupation_grade(word):
    return sum(int(int(i)%63 < 7) for i in word)


def matrix_grade(matrix, weight):
    assert matrix.shape == (504,504)
    for (i,j),value in matrix.todok().items():
        difference=int(int(i)%63 < 7)-int(int(j)%63 < 7)-weight
        assert s.cancel(difference*value)==0


def state_grade(state, particles, grade):
    assert all(value!=0 and len(word)==particles and occupation_grade(word)==grade
        for word,value in state.items())


def run(raw):
    off=read_bound('source_live_differential_hamiltonian')['off_source']
    points=(raw.source_configuration,tuple(map(s.sympify,off['configuration100'])))
    common=raw.full.native.joint.common
    for R in raw.full.R:matrix_grade(R,0)
    records=[]
    for z in points:
        base=clean(raw.full.offset+raw.full.embedding*s.Matrix(z));phi=base[6:76,:]
        Yraw=clean(sum(((phi[a]+s.I*phi[35+a])*common.yukawa_basis[a] for a in range(35)),s.zeros(252)))
        Yprimal=clean(s.kronecker_product(raw.source_time[0]*GAMMA[0],s.eye(63))*Yraw)
        Y=clean(s.diag(Yprimal,-Yprimal.conjugate()))
        matrix_grade(Y,1);assert Y.todok()
        d=raw.coefficients(z)
        matrix_grade(clean(d.zero.one_body-Y),0)
        for M in d.current:matrix_grade(M,0)
        for _,A,B in d.zero.pairs:matrix_grade(A,0);matrix_grade(B,0)
        for word in ((),(0,315),(63,126,252)):
            g=s.Matrix([s.I*s.Rational(j%5-2,47) for j in range(100)])
            u=s.Matrix([s.Rational(j%3-1,43) for j in range(100)]);H=u*u.T-s.eye(100)
            value={word:s.S.One}
            result=weighted_sum([(1,d.apply(value,{word:g},{word:H})),(-1,apply_superposition(Y,value))])
            assert result
            state_grade(result,len(word),occupation_grade(word))
            records.append({'number':len(word),'grade':occupation_grade(word),'output_words':len(result)})
        i,j=next(iter(Y.todok()))
        raised=apply_superposition(Y,{(j,):s.S.One});assert raised
        state_grade(raised,1,occupation_grade((j,))+1)
        assert occupation_grade((i,))!=occupation_grade((j,))
    print('PASS original H0 complete coefficient labels, both-point N=0,2,3 actions; original Y nonzero +1 control',flush=True)
    return records


def main(raw=None):
    began=time.monotonic();raw=SourceLiveDifferentialHamiltonian() if raw is None else raw
    records=run(raw)
    deps=('source_diagonal_core_history','source_quantum_grade_structure','source_live_differential_hamiltonian')
    for name in ('source_diagonal_core_history','source_live_differential_hamiltonian'):read_bound(name)
    grade=json.loads((HERE/'source_quantum_grade_structure.json').read_text())
    assert grade['root']==ROOT_ID
    for path,digest in grade['input_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths=[Path(__file__)]+[HERE/(name+'.json') for name in deps]
    paths += [HERE/(name+'.lean') for name in ('GaussFockLabel','GaussCoreLabel','GaussDiagonalGrade','GaussDiagonalHistory','NativeHistoryGrade')]
    paths += [HERE/name for name in ('source_quantum_grade_structure.py','source_live_differential_hamiltonian.py')]
    report={'root':ROOT_ID,'scope':'ACTUAL_H0_NUMBER_G_COMMUTATION_AND_GRADED_RETARDED_SOURCE',
        'source_sha256':raw.full.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'whole_native12_currents_checked':len(raw.full.R),'actual_state_actions':records,
        'original_H0_complete_coefficient_grade':0,'original_Y_retained_nonzero_grade':1,
        'kernel_contract':'The source native/spin/matter representations generate complete label support; actual compact-core projectors commute with the full diagonalAction and its computed adjoints. The original graded history consumes this exact diagonal, domain, commutation and pairing to return its full-time derivative and retarded source.',
        'controller':'Original source/root/current and whole ledger unchanged; subordinate producer.',
        'seconds':round(time.monotonic()-began,3)}
    (HERE/'source_diagonal_grade.json').write_text(json.dumps(report,separators=(',',':'))+'\n')
    print('PASS actual H0 graded retarded history',report['seconds'],'seconds',flush=True)


if __name__=='__main__':main()

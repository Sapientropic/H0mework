#!/usr/bin/env python3
"""Original boson Schur kernel, auxiliary elimination order, and analytic heavy-matter expansion."""
import hashlib
import importlib.util
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];ROOT=HERE.parents[4]
spec=importlib.util.spec_from_file_location('boson_source_current',HERE.parent/'full-current/compute.py')
source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
clean,normalized,assertzero,encode,decode=source.clean,source.normalized,source.assertzero,source.encode,source.decode

def rational_solve(A,B):
    domain=s.QQ_I.poly_ring(u,q);left=DomainMatrix.from_Matrix(A).convert_to(domain);right=DomainMatrix.from_Matrix(B).convert_to(domain)
    num,den=left.solve_den(right,method='rref');assert left*num==right*den
    return s.SparseMatrix((num.to_Matrix()/domain.to_sympy(den)).applyfunc(s.cancel))

def source_matrix(entries,n,values):
    result=s.MutableSparseMatrix(n,n,{})
    for i,j,power,v in entries:result[i,j]+=s.sympify(v)*s.prod(x**a for x,a in zip(values,power))
    return clean(result)

u,q=s.symbols('u q',real=True)
def main():
    started=time.monotonic()
    a=json.loads((BASE/'active-gauge/receipt.json').read_text());quot=json.loads((BASE/'active-gauge/quotient.json').read_text());prop=json.loads((BASE/'active-gauge/propagation.json').read_text())
    old=json.loads((HERE.parent/'full-current/receipt.json').read_text())
    for path,digest in a['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    N=s.sympify(a['source_lapse']);omega=s.sympify(a['source_frequency']);lam,k=s.symbols('lam k',real=True)
    fields=a['fields'];ret=quot['retained_original_fields'];scale=list(map(s.sympify,prop['constant_diagonal_field_scaling']))
    K=s.SparseMatrix(103,103,{(i,j):s.expand(s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:N*s.sqrt(2)*u,k:s.sqrt(2)*q})*scale[i]*scale[j]/N) for i,j,v in quot['quotient_operator_103_by_103']})
    matter=[i for i,orig in enumerate(ret) if fields[orig]['group'] in ['primal_H','dual_H']];boson=[i for i in range(103) if i not in matter]
    assert len(matter)==48 and len(boson)==55
    write=s.MutableSparseMatrix(48,55,{})
    for block in prop['blocks']:
        mi=[i for i in block['quotient_indices'] if i in matter];bi=[i for i in block['quotient_indices'] if i in boson]
        if not mi:continue
        M=K.extract(mi,mi);force=-K.extract(mi,bi)
        solved=rational_solve(M,force)
        assertzero((M*solved-force).applyfunc(s.cancel))
        for (i,j),v in solved.todok().items():write[matter.index(mi[i]),boson.index(bi[j])]=v
        print('generated matter elimination',len(mi),'to',len(bi),'source boson legs',flush=True)
    write=s.SparseMatrix(write)
    effective=s.SparseMatrix((K.extract(boson,boson)+K.extract(boson,matter)*write).applyfunc(s.cancel))
    assertzero((K.extract(matter,matter)*write+K.extract(matter,boson)).applyfunc(s.cancel))
    assertzero((effective.subs({u:-u,q:-q},simultaneous=True).T-effective).applyfunc(s.cancel))
    print('PASS exact55 boson kernel; 48 matter equations and original formal adjoint',flush=True)

    # Source origin chooses the invertible matter block; six zero channels are retained.
    M0=K.extract(matter,matter).subs({u:0,q:0});piv=list(M0.rref()[1]);heavy=[matter[i] for i in piv];light=[i for i in matter if i not in heavy]
    assert len(heavy)==42 and len(light)==6
    keep=boson+light;D=K.extract(heavy,heavy);D0=D.subs({u:0,q:0});G0=D0.inv(method='DM');assertzero(D0*G0-s.eye(42))
    delta=clean(D-D0)
    assert all(s.Poly(v,u,q).total_degree()<=1 for v in delta.todok().values())
    G1=clean(-G0*delta*G0);G2=clean(G0*delta*G0*delta*G0);Gjet=clean(G0+G1+G2)
    remainder=clean(D*Gjet-s.eye(42))
    assert all(sum(term)>=3 for v in remainder.todok().values() for term,_ in s.Poly(v,u,q).terms())
    fulljet=clean(K.extract(keep,keep)-K.extract(keep,heavy)*Gjet*K.extract(heavy,keep))
    coefficients={}
    for (i,j),value in fulljet.todok().items():
        for power,v in s.Poly(value,u,q).terms():
            if sum(power)<=2:coefficients.setdefault(power,{})[i,j]=v
    jets={power:s.SparseMatrix(len(keep),len(keep),entries) for power,entries in coefficients.items()}
    assert (0,0) in jets
    print('PASS source42 invertible origin sector, six retained light matter channels, local61 kernel through degree2',flush=True)

    # At the same certified complex-frequency point, elimination order is paid in original coordinates.
    E=s.sympify(old['energy']);kv=list(map(s.sympify,old['spatial_momentum']));values=[-s.I*E,*[s.I*x for x in kv]]
    H=source_matrix(a['Fourier_Jacobi_entries'],289,values)
    b=[i for i,f in enumerate(fields) if f['group'] in ['scalar_J','gauge_A','coframe']]
    m=[i for i,f in enumerate(fields) if f['group'] in ['primal_H','dual_H']]
    aux=sorted(set(range(289))-set(b)-set(m));assert len(aux)==168
    A=H.extract(aux,aux);current=A;remaining=aux[:];rhs=s.SparseMatrix.eye(168);back=[]
    for step in a['algebraic_Schur_steps']:
        elim=step['eliminated_fields'];ei=[remaining.index(i) for i in elim];ki=[i for i in range(len(remaining)) if i not in ei]
        inv=s.SparseMatrix(len(ei),len(ei),{(elim.index(i),elim.index(j)):s.sympify(v) for i,j,v in step['algebraic_block_inverse']})
        assertzero(current.extract(ei,ei)*inv-s.eye(len(ei)))
        back.append((elim,[remaining[i] for i in ki],normalized(inv*rhs[ei,:]),normalized(-inv*current.extract(ei,ki))))
        rhs=normalized(rhs[ki,:]-current.extract(ki,ei)*inv*rhs[ei,:])
        current=normalized(current.extract(ki,ki)-current.extract(ki,ei)*inv*current.extract(ei,ki));remaining=[remaining[i] for i in ki]
    assert not remaining
    Ainv=s.MutableSparseMatrix(168,168,{})
    for elim,kept,forcing,WB in reversed(back):
        result=normalized(forcing+WB*Ainv[[aux.index(i) for i in kept],:])
        for j,i in enumerate(elim):Ainv[aux.index(i),:]=result[j,:]
    Ainv=s.SparseMatrix(Ainv);assertzero(A*Ainv-s.eye(168));assertzero(Ainv*A-s.eye(168))
    originalM=H.extract(m,m);Minv=source.block_inverse(originalM)
    # The previous all158 Pi is exactly this first Schur correction at its original97 interface.
    remaining_ba=b+aux
    firstMatter=normalized(H.extract(remaining_ba,remaining_ba)-H.extract(remaining_ba,m)*Minv*H.extract(m,remaining_ba))
    oldbos=old['original289_boson_indices'];oldPi=decode(old['original97_induced_current'])
    assertzero(-H.extract(oldbos,m)*Minv*H.extract(m,oldbos)-oldPi)
    modifiedM=normalized(originalM-H.extract(m,aux)*Ainv*H.extract(aux,m))
    feedback=normalized(modifiedM-originalM);assert feedback.todok()
    modInv=source.block_inverse(modifiedM)
    # Woodbury here is a generated source inverse, verified on both sides.
    changedA=normalized(A-H.extract(aux,m)*Minv*H.extract(m,aux))
    changedAinv=normalized(Ainv+Ainv*H.extract(aux,m)*modInv*H.extract(m,aux)*Ainv)
    assertzero(changedA*changedAinv-s.eye(168));assertzero(changedAinv*changedA-s.eye(168))
    bA=normalized(H.extract(b,b)-H.extract(b,aux)*Ainv*H.extract(aux,b))
    bmA=normalized(H.extract(b,m)-H.extract(b,aux)*Ainv*H.extract(aux,m));mbA=normalized(H.extract(m,b)-H.extract(m,aux)*Ainv*H.extract(aux,b))
    auxFirst=normalized(bA-bmA*modInv*mbA)
    matterFirst=normalized(firstMatter[:len(b),:len(b)]-firstMatter[:len(b),len(b):]*changedAinv*firstMatter[len(b):,:len(b)])
    assertzero(auxFirst-matterFirst)
    reduced=source_matrix(a['primitive_121_Fourier_Jacobi_entries'],289,values)
    assertzero(reduced.extract(m,m)-modifiedM);assertzero(reduced.extract(b,b)-bA)
    assertzero(reduced.extract(b,m)-bmA);assertzero(reduced.extract(m,b)-mbA)
    selected=[i for i in ret if i in b];sb=[b.index(i) for i in selected]
    ub=s.simplify(values[0]/(N*s.sqrt(2)));qb=s.simplify(kv[2]/s.sqrt(2));bs=s.diag(*[scale[i] for i in boson])
    assertzero(bs*auxFirst.extract(sb,sb)*bs/N-effective.subs({u:ub,q:qb}))
    print('PASS original aux/matter Schur orders, nonzero Lorentz feedback, no double-counted Pi, actual55 source section',flush=True)
    result={'scope':'ORIGINAL55_BOSON_SCHUR_AND_LIGHT6_HEAVY42_LOW_MOMENTUM_KERNEL',
        'source_sha256':a['source_sha256'],'original_retained103':ret,'normalized_field_scaling':list(map(str,scale)),
        'coordinate_convention':'lambda=N sqrt(2) u; k=sqrt(2) q; normalized K=S^T K_original S/N',
        'boson55_source_indices':[ret[i] for i in boson],'matter48_source_indices':[ret[i] for i in matter],
        'matter48_writeback_from_boson55':encode(write),'effective_boson55':encode(effective),
        'heavy42_source_indices':[ret[i] for i in heavy],'light6_source_indices':[ret[i] for i in light],
        'local61_source_indices':[ret[i] for i in keep],'origin_heavy_inverse':encode(G0),
        'local61_coefficients_degree2':{str(power):encode(value) for power,value in sorted(jets.items())},
        'heavy_inverse_residual_starts_at_degree':3,'full_matter_origin_rank':42,
        'source_auxiliary_matter_elimination_orders_equal':True,'original_Lorentz_matter_feedback_nonzero':encode(feedback),
        'original_Pi_consumed_once':True,'generic_boson_kernel_formally_self_transpose_at_minus_p':True,
        'order_check_energy':str(E),'order_check_momentum':list(map(str,kv)),
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['scope','full_matter_origin_rank','source_auxiliary_matter_elimination_orders_equal','elapsed_seconds']},indent=2),flush=True)
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Actual adjugate-recursive rational columns and original289 direct consumers."""
import hashlib
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix as DM
import algebra as alg

HERE=Path(__file__).resolve().parent
FQ=HERE.parent
x,U=alg.x,alg.U
ray=s.Symbol('s',real=True)
QQ,R=alg.QQ,alg.R
old,clean,encode=alg.old,alg.clean,alg.encode


def main():
    started=time.monotonic()
    paths=[HERE/'maps.json',HERE/'source.json',
           FQ.parent/'active-gauge/receipt.json',
           FQ/'packet-gauge-joint-momentum-jet/jets.json.gz']
    maps,source,actual,reference=map(alg.read,paths)
    for name,digest in {**maps['source_sha256'],**maps['input_sha256']}.items():
        assert hashlib.sha256((old.source.ROOT/name).read_bytes()).hexdigest()==digest,name
    data={key:[alg.matrix(v) for v in records] for key,records in maps['physical_s_jets'].items()}
    A=[DM.from_Matrix(clean(data['normalized103'][j]*s.sqrt(2)**j)).convert_to(R) for j in range(3)]
    force=[alg.pack(alg.split(clean(data['force'][j]*s.sqrt(2)**j))) for j in range(3)]
    part=[alg.split(clean(data['part'][j]*s.sqrt(2)**j)) for j in range(3)]
    lift=[alg.split(clean(data['lift'][j]*s.sqrt(2)**j)) for j in range(3)]
    frame=alg.matrix(maps['Frame']);fi=alg.matrix(maps['Frame_inverse'])
    Frame=alg.constant_parts(alg.split(frame))
    X0=alg.split(clean(frame*alg.matrix(maps['x0_axis'])))
    pout=[s.sympify(v,locals={'s':ray,'x':x}) for v in source['physical_p_out']]
    Hw=old.ward.operator(actual['Fourier_Jacobi_entries'],values=pout)
    H=[alg.split(clean(Hw.diff(ray,j).subs(ray,0))) for j in range(3)]
    Vw=old.matrix(source['source_polynomial']['V'],{'s':ray,'x':x})
    V=[alg.split(clean(Vw.diff(ray,j).subs(ray,0))) for j in range(3)]
    I=[alg.split(clean(fi.T*data['NoetherSource_axis'][j])) for j in range(3)]
    Fhat=s.Poly(s.sympify(maps['Fhat'],locals={'U':U}),U,domain=s.QQ)
    def nonzero_field(parts):
        row=clean(alg.join(parts).extract([57],range(6)))
        for radical in alg.radicals:
            values=[s.expand(v/radical) for v in row]
            if all(s.re(v).is_Rational and s.im(v).is_Rational for v in values):
                poly=s.Poly(sum(v*U**j for j,v in enumerate(values)),U,domain=QQ)
                assert poly and poly.gcd(Fhat).degree()==0
                return {'field':57,'radical':str(radical),'numerator_after_radical':str(poly.as_expr()),'full_Fhat_gcd_degree':0}
        raise AssertionError('actual coframe57 did not have a native simple radical')
    reports=[]
    for point in [QQ(6,-6),QQ(7,-2)]:
        ma=[alg.evaluate(v,point) for v in A]
        fb=[alg.evaluate(v,point) for v in force]
        inverse={}
        for block in maps['original103_blocks']:
            indices=block['indices'];m=ma[0].extract(indices,indices)
            inv=m.inv()
            assert m.matmul(inv)==inv.matmul(m)==DM.eye(len(indices),QQ)
            for (i,j),value in inv.to_dok().items():inverse[indices[i],indices[j]]=value
        P=DM.from_dok(inverse,(103,103),QQ)
        assert ma[0].matmul(P)==P.matmul(ma[0])==DM.eye(103,QQ)
        y=[P.matmul(fb[0])]
        y.append(P.matmul(fb[1]-ma[1].matmul(y[0])))
        y.append(P.matmul(fb[2]-ma[1].matmul(y[1]).scalarmul(QQ(2))-ma[2].matmul(y[0])))
        world=[]
        for order in range(3):
            value=[alg.evaluate(M,point) for M in part[order]]
            for j in range(order+1):
                left=[alg.evaluate(M,point) for M in lift[j]]
                value=alg.plus(value,alg.scale(alg.product(left,alg.unpack(y[order-j])),int(s.binomial(order,j))))
            world.append(alg.product(Frame,alg.physical(value,order)))
        hw=[[alg.evaluate(M,point) for M in row] for row in H]
        vw=[[alg.evaluate(M,point) for M in row] for row in V]
        src=[[alg.evaluate(M,point) for M in row] for row in I]
        incoming=[alg.evaluate(M,point) for M in X0]
        mouths=[]
        for order in range(3):
            residual=alg.plus(alg.product(vw[order],incoming),alg.scale(src[order],-1))
            for j in range(order+1):
                residual=alg.plus(residual,alg.scale(alg.product(hw[j],world[order-j]),int(s.binomial(order,j))))
            assert all(M.is_zero_matrix for M in residual),(point,order)
            if point==QQ(6,-6):
                expected=alg.constant_parts(alg.split(alg.matrix(reference['derivatives'][order]['X1_numerator_coefficients'])))
                assert all((a-b).is_zero_matrix for a,b in zip(world[order],expected)),order
            mouths.append({'physical_s_order':order,'all_original289_by6_rows':True,
                            'actual_g00_nonzero_witness':nonzero_field(world[order])})
        reports.append({'x':str(QQ.to_sympy(point)),'physical_lambda':str(alg.c*QQ.to_sympy(point)),
                'original103_double_inverse':True,'full112_scalar9_and168_in_source_lift':True,'orders':mouths,
                'frozen_JointMomentumJet_identical':point==QQ(6,-6)})
        print('PASS actual original289 all three physical derivative columns at',QQ.to_sympy(point),flush=True)
    # The inverse is the adjugate of the literal source matrix over its
    # generated determinant, not an input solution or inverse certificate.
    circuit={'P':'adj(A0(x))/det(A0(x))',
             'z0':'P*f0','z1':'P*(f1-A1*z0)','z2':'P*(f2-2*A1*z1-A2*z0)',
             'field_j':'Frame*(part_j+sum_r binomial(j,r)*lift_r*z_(j-r))/theta_denominator',
             'derivatives':'All A_j,f_j,part_j,lift_j are the physical s derivatives stored in maps.json, with incoming U held fixed.'}
    degree=sum(s.degree(s.sympify(f['polynomial'],locals={'x':x}),x)*f['multiplicity']
               for b in maps['original103_blocks'] for f in b['factors'])
    assert degree==126
    result={'scope':'STRIKE_ACTUAL_COMPACT_VARIABLE_FREQUENCY_SOURCE_RATIONAL_JETS',
       'input_sha256':{str(p.relative_to(old.source.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
       'rational_circuit':circuit,'determinant_factorization':maps['original103_blocks'],
       'determinant_frequency_degree':int(degree),
       'generated_frequency_denominator_bound':'det(A0)^(j+1)*(x^2-U), j=0,1,2; all other denominators frequency independent',
       'all_frequency_original289_identity':'The source polynomial identities H*lift=W*A and H*part+V*X0-I1=-W*f identify the original289 residual with W*(A*z-f); the explicit adjugate inverse and its differentiated recursion make every row zero.',
       'consumers':reports,'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'transfer.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS compact actual rational source jets',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()

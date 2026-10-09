#!/usr/bin/env python3
"""All48 original current readers and their selected-A1 family contact.

Unlike the old theta-class matrices, these include the full scalar current
Hessian on the active289 carrier, including coframe/scalar and coframe/gauge
terms when a reader does not fix the vacuum.
"""
import json
from pathlib import Path
import sys
import time
import sympy as s
import source
import ward

HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];FQ=HERE.parent


def main():
    start=time.monotonic()
    data=json.loads((HERE/'source.json').read_text())
    original=json.loads((BASE/'active-gauge/receipt.json').read_text())
    jet=source.load(BASE/'active-gauge/compute.py','gauge_reader_jets')
    tensor=source.load(FQ/'vertex-tensor/compute.py','gauge_reader_vertices')
    sys.modules['compute']=tensor
    covariance=source.load(FQ/'vertex-tensor/covariance.py','gauge_reader_cubics')
    _,_,N,_,context=tensor.source_tables(False)
    bare=covariance.source_hessians(context)
    coords=jet.Coordinates()
    for name,shape in [('scalar_J',(9,)),('gauge_A',(4,12)),('coframe',(4,4)),
        ('primal_H',(2,4,3)),('dual_H',(2,4,3)),('Lorentz',(4,6)),
        ('gravity_B',(6,6)),('multiplier',(6,6)),('gauge_B',(6,12))]:coords.group(name,shape)
    assert coords.fields==original['fields']
    q=coords.value;J=jet.Jet
    inclusion=ward.decode(data['scalar_J_inclusion']);v=ward.decode(data['scalar_v'])
    rho=list(map(ward.decode,data['scalar_rho']));abar=ward.decode(data['gauge_background'])
    e0=context['coframe'];e=jet.matrix(4,4,lambda i,j:e0[i,j]+q('coframe',i,j))
    einverse=jet.inverse_second_jet(e,e0.inv());volume=jet.determinant(e)
    density_metric=jet.matrix(4,4,lambda mu,nu:volume*sum(
        (jet.ETA[a,a]*einverse[mu][a]*einverse[nu][a] for a in range(4)),J()))
    eta=jet.multiply(jet.fixed(inclusion),jet.matrix(9,1,lambda i,j:q('scalar_J',i)))
    phi=jet.add(jet.fixed(v),eta)
    covariant=[]
    for mu in range(4):
        value=jet.multiply(jet.fixed(inclusion),jet.matrix(9,1,lambda i,j:q('scalar_J',i,derivative=mu)))
        for g in range(12):
            value=jet.add(value,jet.multiply(jet.fixed(rho[g]),jet.add(jet.scale(abar[mu,g],eta),
                jet.scale(q('gauge_A',mu,g),phi))))
        covariant.append(value)
    changed=jet.multiply(jet.fixed(rho[1]),phi)
    assert all(not entry[0].grade(0) for entry in changed)
    records=[]
    for mu in range(4):
        for g in range(12):
            reader=jet.multiply(jet.fixed(rho[g]),phi)
            scalar=sum((density_metric[nu][mu]*sum((x[0]*y[0] for x,y in zip(covariant[nu],reader)),J())
                for nu in range(4)),J())
            contact=density_metric[1][mu]*sum((x[0]*y[0] for x,y in zip(changed,reader)),J())
            hs=jet.fourier_hessian(coords,scalar)
            hc=jet.fourier_hessian(coords,contact)
            hb={(i,j,(0,0,0,0)):jet.number(value) for (i,j),value in bare[mu,g].todok().items()}
            full=hb.copy()
            for key,value in hs.items():full[key]=full.get(key,jet.ZERO)+value
            full={key:value for key,value in full.items() if value}
            if (mu,g)==(1,1):
                assert jet.encoded_operator(full)==data['H1']
                assert jet.encoded_operator(hc)==[[i,j,p,str(2*s.sympify(value))] for i,j,p,value in data['H2']]
            assert all(not any(power) for _,_,power in hc)
            records.append({'reader':[mu,g],'Q0':jet.encoded_operator(full),
                'scalar_Q0_completion':jet.encoded_operator(hs),'Q1_contact':jet.encoded_operator(hc),
                'primitive_identity':'Q_b(epsilon)=Q_b(0)+epsilon*Q_b_prime exactly on the field Hessian; non-scalar Q_b_prime is zero'})
    result={'scope':'STRIKE_ALL48_FULL_ACTIVE_CURRENT_READER_JETS',
        'source_sha256':original['source_sha256'],
        'external_family':data['external_family'],
        'scalar_reader':'Vol(e) sum_mu g^(mu,nu)(e) <D_mu phi,rho_b phi>',
        'scalar_reader_parameter_derivative':'Vol(e) g^(1,nu)(e) <rho_S01 phi,rho_b phi>',
        'non_scalar_contact_zero_reason':'Dirac current has no primitive A dependence; the BF double-A variation is linear in primitive B, so its field Hessian is zero.',
        'readers':records,
        'full_scalar_Q0_monomials':sum(len(row['scalar_Q0_completion']) for row in records),
        'full_contact_monomials':sum(len(row['Q1_contact']) for row in records),
        'nonzero_contact_readers':sum(bool(row['Q1_contact']) for row in records),
        'selected_reader_matches_full_H1_and_2H2':True,
        'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'readers.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS all48 full original reader jets, scalar terms',result['full_scalar_Q0_monomials'],
          'contact terms',result['full_contact_monomials'],'nonzero readers',result['nonzero_contact_readers'],
          'seconds',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()

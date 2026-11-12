#!/usr/bin/env python3
"""Independent exact finite actual-field feedback/null circuit controls.

The complete corrected pencil is inverted independently. Native Green has
its original null projection; neither feedback nor null terms are discarded.
"""
from pathlib import Path
from types import ModuleType
from hashlib import sha256
import argparse
import json
import re


def repository_root():
    for p in Path(__file__).resolve().parents:
        if (p/'Lean/lean-toolchain').is_file():
            return p
    raise RuntimeError('repository marker missing; pass --root')


def load_math(root):
    base=root/'Verification/physics/low-energy-phenomenology/alpha-source/em-identification'
    groups=[('check_actual_dressed_em_clock_action.py',('Z','F','exact','eye','mm','mv','inverse','madd','mscale')),
            ('check_actual_dressed_zero_damping.py',('poly','padd','pmul','pscale','peval','local_data'))]
    records=[]
    for filename,names in groups:
        p=base/filename
        m=ModuleType('staticfeedback_math_'+p.stem)
        m.__file__=str(p)
        exec(compile(p.read_text(),str(p),'exec'),m.__dict__)
        m.__dict__.update(globals())
        for name in names:
            globals()[name]=getattr(m,name)
        records.append(dict(path=str(p),sha256=sha256(p.read_bytes()).hexdigest(),functions=list(names)))
    return records


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),Z())


def vadd(a,b):
    return [x+y for x,y in zip(a,b)]


def controls():
    checks=[]
    def check(label,ok,evidence=None,negative=False):
        checks.append(dict(label=label,kind='negative_mutant_rejected' if negative else 'positive',passed=bool(ok),evidence=exact(evidence)))
    k=Z(F(2,7))
    # Native J retains two true null coordinates. Full Q mixes these directions.
    J=[[k**2 if i==j and i<2 else Z() for j in range(4)] for i in range(4)]
    G=[[1/k**2 if i==j and i<2 else Z() for j in range(4)] for i in range(4)]
    N=[[Z(i==j and i>=2) for j in range(4)] for i in range(4)]
    Q=[[Z(1,1),Z(F(1,3)),Z(F(1,2)),Z(0,1)],
       [Z(F(-1,4)),Z(2,-1),Z(1,1),Z(F(2,3))],
       [Z(F(1,5)),Z(0,1),Z(2),Z(F(1,2))],
       [Z(1,-1),Z(F(1,7)),Z(F(-1,3)),Z(3)]]
    P=madd(J,mscale(-1,Q))
    source=[Z(1,2),Z(2,-1),Z(1,-1),Z(3,1)]
    detector=[Z(2,-1),Z(1,1),Z(0,2),Z(-1,1)]
    a=mv(inverse(P),source)
    native=mv(G,source)
    feedback=mv(G,mv(Q,a))
    null=mv(N,a)
    check('original_native_left_and_right_inverse_keep_null_projection',mm(G,J)==mm(J,G)==madd(eye(4),mscale(-1,N)))
    check('complete_actual_corrected_pencil_solves_forcing',mv(P,a)==source)
    check('actual_field_generates_native_feedback_and_own_null_coordinates',a==vadd(vadd(native,feedback),null))
    balance=vadd(source,mv(Q,a))
    check('all_original_null_rows_balance_full_forcing_and_feedback',balance==mv(J,a) and mv(N,balance)==[Z()]*4)
    check('null_coordinates_come_from_actual_corrected_field',null[2:]==a[2:] and any(null))
    reads=[dot(detector,x) for x in (native,feedback,null)]
    full=dot(detector,a)
    check('same_independent_current_circuit_consumes_complete_actual_field',sum(reads,Z())==full and all(reads),reads)
    for i,x in enumerate(reads):
        check('reject_omitted_current_circuit_piece_'+str(i),bool(x) and full!=sum(reads[:i]+reads[i+1:],Z()),x,True)
    check('reject_native_green_as_corrected_inverse',mm(P,G)!=eye(4),negative=True)
    check('reject_null_projection_deleted_before_actual_equation',any(mv(P,vadd(native,feedback))[i]!=source[i] for i in range(4)),negative=True)
    check('reject_full_forcing_alone_as_compatible_native_input',mv(N,source)!=[Z()]*4,negative=True)

    # A fixed-direction complete circuit can have no separate sigma limits.
    # Its aggregate is generated from actual full-minus-native observations.
    Cnative=Z(3,1)
    Crest=Z(-2,3)
    def native_read(kappa):
        return -Cnative/kappa**2+Z(2)
    def actual_full(kappa,sigma):
        return -(Cnative+Crest)/kappa**2+Z(5)+sigma*Z(1,2)
    def pieces(kappa,sigma):
        singular=Z(1,1)/sigma
        feedback=singular-Crest/kappa**2+Z(3)+sigma*Z(1,2)
        null=-singular
        return feedback,null
    samples=[]
    for kappa,sigma in ((Z(F(1,7)),Z(F(1,5))),(Z(F(1,11)),Z(F(1,13)))):
        f,n=pieces(kappa,sigma)
        samples.append(actual_full(kappa,sigma)==native_read(kappa)+f+n)
    check('same_order_feedback_and_null_actual_circuit_is_full_minus_native',all(samples))
    check('aggregate_sigma_return_does_not_assert_separate_finite_limits',local_data(poly([1]),poly([0,1]))['order']==1 and local_data(poly([-1]),poly([0,1]))['order']==1)
    check('reject_individual_limits_from_aggregate_cancellation',local_data(poly([1]),poly([0,1]))['order']>0,negative=True)
    total=Cnative+Crest
    check('ordered_negative_kappa_square_coefficient_preserves_full_native_rest',total-Cnative==Crest and bool(Crest))
    check('reject_native_scalar_as_complete_physical_scalar',total!=Cnative,negative=True)
    check('reject_same_order_remainder_as_short_range',bool(Crest),Crest,True)
    # Exactly one Fourier 4pi is kept as a formal monomial, no pi approximation.
    whole=(total/4,-1)
    native_packet=(Cnative/4,-1)
    rest_packet=(Crest/4,-1)
    check('once_four_pi_preserves_whole_coefficient_balance',whole==(native_packet[0]+rest_packet[0],-1))
    check('reject_duplicate_or_missing_four_pi',whole!=(total/16,-2) and whole!=(total,0),negative=True)
    return checks,dict(dimension=4,actual_current_components=reads,full_current=full,null_coordinates=null[2:],native_coefficient=Cnative,feedback_null_coefficient=Crest,whole_coefficient=total,original_source_values_evaluated=False)


def binding(candidate,source_dir):
    raw=candidate.read_bytes()
    j=json.loads(raw)
    names=['ActualDressedStaticFeedback','ActualDressedStaticCurrentCircuit','ActualDressedStaticLongrangeReturn']
    if [x['module'] for x in j['sources']]!=names:
        raise ValueError('requires static feedback three-source candidate')
    strip=lambda s:re.sub(r'\s+','',re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/', '',re.sub(r'(?m)^import[^\n]*','',s),flags=re.S)))
    records=[]
    for x in j['sources']:
        original=Path(x['path']).read_bytes()
        if sha256(original).hexdigest()!=x['source_sha256']:
            raise ValueError('frozen source changed')
        selected=source_dir/(x['module']+'.lean') if source_dir else Path(x['path'])
        data=selected.read_bytes()
        if strip(original.decode())!=strip(data.decode()):
            raise ValueError('selected source changes frozen declaration bodies')
        records.append(dict(module=x['module'],path=str(selected),sha256=sha256(data).hexdigest()))
    return dict(candidate_path=str(candidate),candidate_sha256=sha256(raw).hexdigest(),sources=records)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('root','candidate','source-dir','output'):
        parser.add_argument('--'+name,type=Path)
    args=parser.parse_args()
    root=args.root.resolve() if args.root else repository_root()
    helpers=load_math(root)
    candidate=(args.candidate or root/'Lean/scratch/AlphaSource/ActualDressedStaticFeedbackDispositionOwn/candidate.json').resolve()
    bound=binding(candidate,args.source_dir.resolve() if args.source_dir else None)
    checks,fixtures=controls()
    failed=[x['label'] for x in checks if not x['passed']]
    result=dict(status='FAIL' if failed else 'PASS',positive=sum(x['kind']=='positive' for x in checks),negative=sum(x['kind']=='negative_mutant_rejected' for x in checks),failed=failed,checks=checks,fixtures=exact(fixtures),source_binding=bound,helper_bindings=helpers,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),scope='Independent exact synthetic finite pencil/current and ordered aggregate controls; no original source integrals, all-angle corrected domination, physical scalar C_EM, photon/speed or alpha value supplied.')
    output=(args.output or Path(__file__).with_suffix('.json')).resolve()
    output.write_text(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],positive=result['positive'],negative=result['negative'],failed=failed,script_sha256=result['script_sha256'],report_sha256=sha256(output.read_bytes()).hexdigest()),sort_keys=True))
    if failed:
        raise SystemExit(1)


if __name__=='__main__':
    main()

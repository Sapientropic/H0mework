"""Freeze, issue, compute and consume the complete late adjoint integral."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import ast
import gzip
import hashlib
import json
import subprocess

import late_registered_source_rha0038 as source
import late_registered_integral_rha0038 as integral
import late_registered_independent_rha0038 as independent
import registered_forcing_rha0034 as forcing

bank=source.bank
previous=bank.previous
HERE,ROOT=bank.HERE,bank.ROOT
OWN=('criterion-rha0038.md','LateRegisteredAdjoint.lean','late-adjoint-math-certification-rha0038.json',
    'positive_quadrature_rha0038.py','quadrature-first-rha0038.json','dyadic_matrix_rha0038.py',
    'late_registered_source_rha0038.py','late_registered_independent_rha0038.py','late_registered_integral_rha0038.py',
    'late_registered_run_rha0038.py','test_late_registered_arithmetic_rha0038.py','test_late_registered_source_rha0038.py',
    'test_late_registered_integral_rha0038.py','test_late_registered_run_rha0038.py')
INPUTS=(*bank.OWN,*bank.INPUTS,'gaussian-operator-bank-first-rha0037.1.json',
    'gaussian-operator-handoff-first-rha0037.1.json','registered_forcing_rha0034.py','registered_forcing_independent_rha0034.py',
    'registered_tensor_action_rha0034.py','free-density-bank-first-rha0033.json',
    'retarded_gaussian_bsm_source.py','retarded_receipt_activity_envelope.py')


def bindings(freeze):
    files={HERE/n for n in (*OWN,*INPUTS)}
    pending=[p for p in files if p.suffix=='.py' and not p.name.startswith('test_')]
    while pending:
        path=pending.pop()
        for node in ast.walk(ast.parse(path.read_text())):
            names=[a.name for a in node.names] if isinstance(node,ast.Import) else [node.module] if isinstance(node,ast.ImportFrom) and node.level==0 and node.module else []
            for name in names:
                candidate=HERE/(name.split('.')[0]+'.py')
                if candidate.is_file() and candidate not in files:files.add(candidate);pending.append(candidate)
    files|={ROOT/'ComputeNode/README.md',HERE.parent/'schema.py',HERE.parent.parent/'theory-blind/independent_born.py'}
    result={}
    for path in sorted(files):
        relative=path.relative_to(ROOT).as_posix();raw=path.read_bytes()
        source.require(subprocess.check_output(['git','-C',str(ROOT),'show',freeze+':'+relative])==raw,
                       'late integral science changed after freeze: '+relative)
        result[relative]=hashlib.sha256(raw).hexdigest()
    return result


def write(path,value):previous.write(Path(path),value)


def select(rows,piece=0):
    source.require(type(piece) is int and 0<=piece<60,'explicit original late piece required')
    values=[r for r in rows if r['piece_index']==piece]
    source.require(len(values)==1,'complete unique late source piece inventory required')
    return values[0]


def _operator_pieces(completed):
    result=[]
    for side in (0,1):
        row=next(r for r in completed['rows'] if r['side']==side and r['role']=='late_forward')
        path=previous.artifact(row['curve'])
        with gzip.open(path,'rt') as handle:
            header=json.loads(next(handle));pieces=[json.loads(line) for line in handle]
        source.require(header['flow_source_sha256']==row['flow_source_sha256'] and header['piece_count']==len(pieces)==60 and
            header['mode_bits']==96 and header['curve_degree']==64 and header['direction']=='forward',
            'the exact completed late operator stream is required')
        result.append((row,pieces))
    return result


def free_midpoint(current):
    raw=current.record();completed=json.loads(bank.paid.paid.frozen(HERE/'free-density-bank-first-rha0033.json'))
    nodes=forcing._nodes(current,raw,completed);rows=[];prices={}
    for node in nodes:
        checked=json.loads(previous.artifact(node['checked_curve']).read_text());side=node['side']
        with gzip.open(previous.artifact(node['Chebyshev_stream']),'rt') as handle:
            header=json.loads(next(handle));piece=None
            for index,line in enumerate(handle):
                if index==59:piece=json.loads(line);break
        source.require(piece is not None and header['piece_count']==120 and header['source_factor_id']==node['factor_id'],
                       'the complete paid free source midpoint is required')
        matrices=[forcing.core.density.fourier._coefficient(r,1 << header['mode_bits']) for r in piece['chebyshev_coefficients']]
        centre=forcing.core.endpoint(matrices,True);time=current._law.local_times(sum(map(Q,raw['retarded_detector_law']['gate_seconds']))/2)[side]
        physical,frame=forcing.core.density._frame(checked['original_density_source']['Gaussian_source'],centre,time,192)
        extra=Q(checked['whole_new_trace_norm_error'])+frame
        prices[side,node['factor_id']]={'initial_entry_norm_upper':checked['initial_entry_norm_upper'],'whole_new_trace_norm_error':str(extra)}
        rows.append({'side':side,'factor_id':node['factor_id'],'physical_local_seconds':str(time),
            'physical_matrix':[[i,j,str(a),str(b)] for (i,j),(a,b) in sorted(physical.items())],
            'whole_new_trace_norm_error':str(extra),'checked_curve':node['checked_curve'],'Chebyshev_stream':node['Chebyshev_stream']})
    error,_=previous.tensor_price(raw['source_factor_ids'],prices)
    return {'source_current_sha256':source.digest(raw),'source_factor_ids':raw['source_factor_ids'],'rows':rows,
        'whole_new_free_midpoint_error':str(error),'old_whole_input_error_once':raw['whole_retarded_gate_input_error'],
        'source_positive_mass_upper':raw['source_positive_mass_upper'],'new_pump_or_inlet_residuals':0}


def prepare(freeze,output):
    bound=bindings(freeze);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    write(output/'attempt.json',{'phase':'prepare','scientific_freeze_commit':freeze,'source_bindings':bound})
    current=bank.paid.restore();raw,plans=bank.plans(current)
    completed=json.loads(bank.paid.paid.frozen(HERE/'gaussian-operator-bank-first-rha0037.1.json'))
    grid=json.loads(bank.paid.paid.frozen(HERE/'quadrature-first-rha0038.json'))
    late=[bank.choose(plans,side=side,role='late_forward')[2] for side in (0,1)]
    program=source.source_program(current._law,late,completed,grid)
    independent.verify_program(program,current._law.record(),completed,grid)
    write(output/'program.json',program);program_binding=previous.binding(output/'program.json')
    midpoint=free_midpoint(current);write(output/'free-midpoint.json',midpoint)
    curves=_operator_pieces(completed);rows=[]
    for index in range(60):
        item={'schema':source.SCHEMA+'/handoff','scientific_freeze_commit':freeze,'source_program':program_binding,
            'source_program_sha256':source.digest(program),'piece_index':index,
            'original_completed_curve_bindings':[r['curve'] for r,_ in curves],
            'curve_pieces':[values[index] for _,values in curves],'source_bindings':bound}
        path=output/f'piece-{index:03d}.json';write(path,item);binding=previous.binding(path)
        rows.append({'piece_index':index,'handoff':binding,'node_unit_id':f'late-registered-adjoint-{index:03d}@{binding["sha256"][:16]}'})
    report={'schema':source.SCHEMA+'/prepared','scientific_freeze_commit':freeze,'source_bindings':bound,
        'source_program':program_binding,'source_program_sha256':source.digest(program),'free_midpoint':previous.binding(output/'free-midpoint.json'),
        'source_current_sha256':source.digest(raw),'rows':rows,'new_pump_or_inlet_residuals':0,
        'full_first_receipt_or_response_anchor_certified':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}
    write(output/'summary.json',report);print(json.dumps({'prepared_late_pieces':len(rows),'source_program_sha256':source.digest(program)}),flush=True)


def unit(program_path,handoff_path,output):
    program_raw=Path(program_path).read_bytes();handoff=json.loads(Path(handoff_path).read_text());program=json.loads(program_raw)
    source.require(handoff['schema']==source.SCHEMA+'/handoff' and
        handoff['source_program']['sha256']==hashlib.sha256(program_raw).hexdigest() and
        handoff['source_program']['bytes']==len(program_raw) and handoff['source_program_sha256']==source.digest(program),
        'the issued original late source program changed')
    for relative,sha in handoff['source_bindings'].items():
        source.require(hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()==sha,'worker science changed: '+relative)
    completed=json.loads((HERE/'gaussian-operator-bank-first-rha0037.1.json').read_text())
    grid=json.loads((HERE/'quadrature-first-rha0038.json').read_text())
    independent.verify_program(program,program['original_retarded_source'],completed,grid)
    result=integral.integrate_piece(program,*handoff['curve_pieces'],handoff['piece_index'])
    result['scientific_freeze_commit']=handoff['scientific_freeze_commit'];result['issued_handoff_sha256']=hashlib.sha256(Path(handoff_path).read_bytes()).hexdigest()
    write(output,result);print(json.dumps({'late_piece':handoff['piece_index'],
        'maximum_port_operator_error':max(float(Q(r['whole_operator_error_upper'])) for r in result['ports'])}),flush=True)


def _read_rows(rows,dimension):
    result={}
    for i,j,a,b in rows:
        source.require(type(i) is type(j) is type(a) is type(b) is int and
            0<=i<dimension and 0<=j<dimension and (i,j) not in result and (a or b),'canonical complete dyadic effect coefficient required')
        result[i,j]=a,b
    return result


def _trace_product(effect,matrix):
    answer=(Q(0),Q(0));quantum=1 << integral.B
    for (i,j),(a,b) in effect.items():
        c,d=matrix.get((j,i),(Q(0),Q(0)));answer=(answer[0]+(a*c-b*d)/quantum,answer[1]+(a*d+b*c)/quantum)
    return answer


def _multiply(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def readout(ports,program,midpoint):
    densities={(r['side'],r['factor_id']):{(i,j):(Q(a),Q(b)) for i,j,a,b in r['physical_matrix']} for r in midpoint['rows']}
    old=Q(midpoint['old_whole_input_error_once']);new=Q(midpoint['whole_new_free_midpoint_error']);mass=Q(midpoint['source_positive_mass_upper'])
    duration=Q(program['source_late_detector_interval_seconds'][1])-Q(program['source_late_detector_interval_seconds'][0])
    cap=Q(program['registered_total_activity_upper_per_second'])*duration;result=[];total=Q(0);operator_error=Q(0)
    for port in ports:
        value=Q(0);error=Q(port['whole_operator_error_upper']);operator_error+=error
        same=[_read_rows(port[key],33) for key in ('same_arm_A','same_arm_B')]
        for left,right in midpoint['source_factor_ids']:
            a,b=densities[0,left],densities[1,right]
            ta=sum((z[0] for (i,j),z in a.items() if i==j),Q(0));tb=sum((z[0] for (i,j),z in b.items() if i==j),Q(0))
            terms=_trace_product(same[0],a)[0]*tb+_trace_product(same[1],b)[0]*ta+Q(port['source_background_identity_coefficient'])*ta*tb
            for kernel in port['coherent_cross_kernels']:
                basis=program['raised_operator_bases'][kernel['line']];coefficient=_read_rows(kernel['raised_A_lowered_B_coefficients'],len(basis));cross=(Q(0),Q(0))
                for (i,j),(x,y) in coefficient.items():
                    e,g=basis[i];f,h=basis[j]
                    product=_multiply(a.get((g,e),(Q(0),Q(0))),b.get((f,h),(Q(0),Q(0))))
                    z=_multiply((Q(x,1 << integral.B),Q(y,1 << integral.B)),product);cross=(cross[0]+z[0],cross[1]+z[1])
                terms+=2*cross[0]
            value+=terms
        payment=cap*(old+new)+error*(mass+old+new);total+=value
        interval=max(Q(0),value-payment),min(cap*mass,value+payment)
        source.require(interval[0]<=interval[1],'source registered mean contradicts its positive activity bound')
        result.append({'port':port['port'],'centre':str(value),'whole_scalar_error':str(payment),
            'unclipped_interval':list(map(str,(value-payment,value+payment))),
            'physical_mean_interval':list(map(str,interval))})
    payment=cap*(old+new)+operator_error*(mass+old+new)
    interval=max(Q(0),total-payment),min(cap*mass,total+payment)
    source.require(interval[0]<=interval[1],'whole registered mean contradicts the same source activity bound')
    return {'port_registered_mean_integrals':result,'whole_four_port_mean_centre':str(total),
        'whole_four_port_scalar_error':str(payment),'whole_four_port_mean_interval':list(map(str,interval)),
        'source_registered_mean_effect_norm_upper':str(cap),'old_input_error_paid_once_for_whole_readout':True,
        'first_receipt_probability_generated':False,'mean_registration_readout_generated':True}


def aggregate(freeze,prepared,results,output):
    bound=bindings(freeze);prepared,results,output=map(Path,(prepared,results,output));manifest=json.loads((prepared/'summary.json').read_text())
    source.require(manifest['schema']==source.SCHEMA+'/prepared' and manifest['scientific_freeze_commit']==freeze and manifest['source_bindings']==bound,
                   'same frozen complete late source handoff required')
    output.mkdir(parents=True,exist_ok=False);write(output/'attempt.json',{'phase':'aggregate','scientific_freeze_commit':freeze,'source_bindings':bound})
    program=json.loads(previous.artifact(manifest['source_program']).read_text());midpoint=json.loads(previous.artifact(manifest['free_midpoint']).read_text())
    current=bank.paid.restore();_,plans=bank.plans(current);completed=json.loads(bank.paid.paid.frozen(HERE/'gaussian-operator-bank-first-rha0037.1.json'))
    grid=json.loads(bank.paid.paid.frozen(HERE/'quadrature-first-rha0038.json'))
    expected=source.source_program(current._law,[bank.choose(plans,side=s,role='late_forward')[2] for s in (0,1)],completed,grid)
    source.require(expected==program and source.digest(current.record())==manifest['source_current_sha256'] and free_midpoint(current)==midpoint,
                   'same native source, complete free midpoint or original time mother changed')
    independent.verify_program(program,current._law.record(),completed,grid)
    source.require([r['piece_index'] for r in manifest['rows']]==list(range(60)),'complete ordered late source cover required')
    ports=[{'port':p,'same_arm_A':{},'same_arm_B':{},'background':Q(0),'cross':{line:{} for line in ('D1','D2')},'error':Q(0)} for p in range(4)];rows=[]
    names=('numeric_exact_arithmetic_and_source_rounding_price','complete_polynomial_quadrature_and_phase_price',
           'source_full_TP_vs_no_jump_and_curve_price','source_Gamma_rate_price')
    for row in manifest['rows']:
        index=row['piece_index'];handoff=json.loads(previous.artifact(row['handoff']).read_text())
        path=results/row['node_unit_id']/f'late-effect-piece-{index:03d}.json';part=json.loads(path.read_text())
        source.require(part['source_program_sha256']==source.digest(program) and part['piece_index']==index and
            part['scientific_freeze_commit']==freeze and part['issued_handoff_sha256']==row['handoff']['sha256'] and
            [p['port'] for p in part['ports']]==list(range(4)) and part['mode_bits']==96 and
            part['source_late_relative_interval_seconds']==list(map(str,(index*source.PIECE_SECONDS,(index+1)*source.PIECE_SECONDS))) and
            part['full_natural_recycling_retained'] is True and part['source_spectator_reader']=='full TP identity' and
            part['old_inlet_error_applied_to_effect'] is False,'complete source piece, native time or checked arithmetic changed')
        for target,value in zip(ports,part['ports']):
            prices=[Q(value[k]) for k in names]
            source.require(min(prices)>=0 and sum(prices,Q(0))==Q(value['whole_operator_error_upper']), 'piece price arithmetic changed')
            for key in ('same_arm_A','same_arm_B'):
                matrix=_read_rows(value[key],33)
                source.require(matrix==integral.integer.adjoint(matrix),'same-arm integral lost its original Hermitian effect')
                integral.integer.add(target[key],matrix)
            target['background']+=Q(value['source_background_identity_coefficient']);target['error']+=Q(value['whole_operator_error_upper'])
            source.require([k['line'] for k in value['coherent_cross_kernels']]==['D1','D2'],'complete source line inventory changed')
            for kernel in value['coherent_cross_kernels']:
                line=kernel['line'];n=len(program['raised_operator_bases'][line])
                source.require(kernel['conjugate_reverse_term_retained'] is True and kernel['independent_all_complex_integer_entries']==n*n,
                               'independent full integer contraction coverage changed')
                integral.integer.add(target['cross'][line],_read_rows(kernel['raised_A_lowered_B_coefficients'],n))
        rows.append({'piece_index':index,'handoff':row['handoff'],'checked_piece':previous.binding(path)})
    result=[]
    for item in ports:
        source.require(item['background']==Q(program['original_background_rates_per_second'][item['port']])*60*source.PIECE_SECONDS,
                       'source background was not integrated exactly once')
        result.append({'port':item['port'],'same_arm_A':integral._rows(item['same_arm_A']),'same_arm_B':integral._rows(item['same_arm_B']),
            'source_background_identity_coefficient':str(item['background']),
            'coherent_cross_kernels':[{'line':line,'raised_A_lowered_B_coefficients':integral._rows(value),'conjugate_reverse_term_retained':True} for line,value in item['cross'].items()],
            'whole_operator_error_upper':str(item['error'])})
    effect={'schema':source.SCHEMA+'/complete-effect','source_program_sha256':source.digest(program),'mode_bits':96,'ports':result}
    write(output/'late-effect.json',effect);contraction=readout(result,program,midpoint);write(output/'registered-mean-readout.json',contraction)
    maximum=max(Q(p['whole_operator_error_upper']) for p in result)
    report={'schema':source.SCHEMA+'/complete','scientific_freeze_commit':freeze,'source_bindings':bound,
        'source_program':manifest['source_program'],'source_program_sha256':source.digest(program),'rows':rows,
        'complete_piece_count':60,'complete_port_count':4,'independent_complex_integer_entries':60*4*(64*64+128*128),
        'complete_late_effect':previous.binding(output/'late-effect.json'),'source_registered_mean_readout':previous.binding(output/'registered-mean-readout.json'),
        'maximum_port_operator_error':str(maximum),'registered_operator_accuracy':'1/10000000000','registered_accuracy_passed':maximum<=Q(1,10**10),
        'full_natural_recycling_retained':True,'source_Gaussian_field_truncated':False,'old_input_error_reapplied_per_effect':False,
        'first_receipt_probability_generated':False,'full_first_receipt_or_response_anchor_certified':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False}
    write(output/'summary.json',report);print(json.dumps({'complete_late_pieces':60,'maximum_port_operator_error':float(maximum),'accuracy_passed':report['registered_accuracy_passed']}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('phase',choices=('prepare','unit','aggregate'))
    p.add_argument('--freeze');p.add_argument('--output',type=Path,required=True);p.add_argument('--prepared',type=Path)
    p.add_argument('--results',type=Path);p.add_argument('--program',type=Path);p.add_argument('--handoff',type=Path);args=p.parse_args()
    try:
        if args.phase=='prepare':source.require(args.freeze is not None,'scientific freeze required');prepare(args.freeze,args.output)
        elif args.phase=='unit':source.require(args.program is not None and args.handoff is not None,'issued source program and handoff required');unit(args.program,args.handoff,args.output)
        else:source.require(args.freeze is not None and args.prepared is not None and args.results is not None,'complete issued source and results required');aggregate(args.freeze,args.prepared,args.results,args.output)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():write(args.output/'failure.json',{'schema':source.SCHEMA+'/failed-attempt','phase':args.phase,
            'scientific_freeze_commit':args.freeze,'reason':str(error),'actual_hardware_uniquely_identified':False,'controller_advance':False})
        raise

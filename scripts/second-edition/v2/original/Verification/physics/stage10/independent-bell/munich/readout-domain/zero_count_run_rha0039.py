"""Issue six same-source no-count coflows and consume the complete herald query."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import ast
import hashlib
import json
import subprocess

import zero_count_receipt_rha0039 as source
import zero_count_independent_rha0039 as independent
import zero_count_check_rha0039 as checker
import gaussian_operator_bank_rha0037_1 as previous

bank=previous.previous
HERE,ROOT=previous.HERE,previous.ROOT
OWN=('criterion-rha0039.md','FirstReceiptZeroCount.lean','first-receipt-zero-count-math-rha0039.json',
    'zero_count_receipt_rha0039.py','zero_count_independent_rha0039.py','zero_count_integer_rha0039.py',
    'zero_count_proposal_rha0039.py','zero_count_check_rha0039.py','zero_count_run_rha0039.py',
    'test_zero_count_receipt_rha0039.py','test_zero_count_coflow_rha0039.py','test_zero_count_run_rha0039.py')
INPUTS=(*previous.OWN,*previous.INPUTS,'late_registered_source_rha0038.py',
    'gaussian-operator-bank-first-rha0037.1.json','late-adjoint-bank-first-rha0038.1.json',
    'late-adjoint-mean-first-rha0038.1.json','FirstReceiptZeroCount.lean')


def bindings(freeze):
    paths={HERE/n for n in (*OWN,*INPUTS)};pending=[p for p in paths if p.suffix=='.py' and not p.name.startswith('test_')]
    while pending:
        path=pending.pop()
        for node in ast.walk(ast.parse(path.read_text())):
            names=[r.name for r in node.names] if isinstance(node,ast.Import) else [node.module] if isinstance(node,ast.ImportFrom) and node.level==0 and node.module else []
            for name in names:
                p=HERE/(name.split('.')[0]+'.py')
                if p.is_file() and p not in paths:paths.add(p);pending.append(p)
    paths|={ROOT/'ComputeNode/README.md',HERE.parent/'schema.py',HERE.parent.parent/'theory-blind/independent_born.py'}
    result={}
    for path in sorted(paths):
        relative=path.relative_to(ROOT).as_posix();raw=path.read_bytes()
        source.require(subprocess.check_output(['git','-C',str(ROOT),'show',freeze+':'+relative])==raw,
                       'zero-count source science changed after freeze: '+relative)
        result[relative]=hashlib.sha256(raw).hexdigest()
    return result


def inventory(parent):
    return [(query,side,source.LocalNoCountCoflow(parent,side,query=query)) for query in source.PORT_SETS for side in (0,1)]


def select(rows,query='all',side=0):
    source.require(query in source.PORT_SETS and type(side) is int and side in (0,1),'registered query and physical side required')
    found=[r for r in rows if r['query']==query and r['side']==side]
    source.require(len(found)==1,'complete original query-side cover required')
    return found[0]


def write(path,value):bank.write(Path(path),value)


def handoff(coflow,freeze,bound):
    return {'schema':source.SCHEMA+'/handoff','scientific_freeze_commit':freeze,'source_bindings':bound,
        'coflow_source':coflow.record(),'initial_effect_supplied_by_caller':False,'actual_hardware_member_asserted':False}


def prepare(freeze,output):
    bound=bindings(freeze);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    write(output/'attempt.json',{'phase':'prepare','scientific_freeze_commit':freeze,'source_bindings':bound})
    current=previous.paid.restore();raw=current.record();parent=source.ZeroCountReceiptSource(current._law);rows=[]
    write(output/'zero-count-source.json',parent.record())
    for query,side,coflow in inventory(parent):
        record=coflow.record()
        source.require(independent.local_recycling(current._law.record(),side,source.PORT_SETS[query])==record['complete_unobserved_local_recycling'],
                       'independent original local bath differs from the zero-count restriction')
        path=output/f'handoff-{query}-{side}.json';write(path,handoff(coflow,freeze,bound));binding=bank.binding(path)
        rows.append({'query':query,'side':side,'coflow_source_sha256':source.digest(record),'handoff':binding,
            'node_unit_id':f'zero-count-{query}-{side}@{binding["sha256"][:16]}'})
    report={'schema':source.SCHEMA+'/prepared','scientific_freeze_commit':freeze,'source_bindings':bound,'rows':rows,
        'complete_zero_count_source':bank.binding(output/'zero-count-source.json'),
        'original_current_sha256':source.digest(raw),'old_whole_input_error_once':raw['whole_retarded_gate_input_error'],
        'new_pump_or_inlet_residuals':0,'specific_Psi_label_probability_claimed':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}
    write(output/'summary.json',report);print(json.dumps({'complete_no_count_coflows':len(rows)}),flush=True)


def probability_from_effects(reports,current_record,law_record):
    terms=current_record['source_factor_ids'];inputs={}
    for side,rows in enumerate(current_record['checked_local_density_inventories']):
        for row in rows:inputs[side,row['factor_id']]=source.gaussian._matrix(row['complete_retarded_local_endpoint'])
    def trace(matrix):return sum((z for (i,j),z in matrix.items() if i==j),source.dipole.ComplexRadical())
    def contraction(e,r):return trace(source.dipole.matrix_product(e,r))
    central_mass=sum((trace(inputs[0,a])*trace(inputs[1,b]) for a,b in terms),source.dipole.ComplexRadical())
    source.require(not central_mass.imag,'original whole source trace must be real')
    mass,radical=source.gaussian.full.radical_midpoint(central_mass.real,192)
    old=Q(current_record['whole_retarded_gate_input_error']);upper=Q(current_record['source_positive_mass_upper'])
    duration=Q(law_record['gate_seconds'][1])-Q(law_record['gate_seconds'][0]);clock=law_record['complete_driven_field_source']['reference_clock']
    centre=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
    source.require(0<lo<=centre<=hi,'same original positive Gamma family required')
    rate_scale=max(centre-lo,hi-centre)/centre
    no_count={};new=radical;intervals={}
    for query,ports in source.PORT_SETS.items():
        rows=[select(reports,query,side)['report'] for side in (0,1)]
        effects=[source.gaussian._matrix(row['complete_physical_effect']) for row in rows]
        prices=[Q(row['whole_new_operator_error']) for row in rows]
        pair=prices[0]+prices[1]+prices[0]*prices[1]
        value=sum((contraction(effects[0],inputs[0,a])*contraction(effects[1],inputs[1,b]) for a,b in terms),source.dipole.ComplexRadical())
        source.require(not value.imag,'complete physical no-count contraction must remain real')
        v,rounding=source.gaussian.full.radical_midpoint(value.real,192)
        rate=sum((Q(law_record['BG_source']['BG_rates_per_second'][p]) for p in ports),Q(0))
        weight,scalar=source.gaussian._exponential(-rate*duration,0,192)
        scalar+=rate*duration*rate_scale
        price=abs(weight[0])*pair+scalar*(1+pair)
        local_new=price*(upper+old)+abs(weight[0])*rounding
        no_count[query]=weight[0]*v;new+=local_new
        no_count_interval=max(Q(0),no_count[query]-old-local_new),min(upper,no_count[query]+old+local_new)
        source.require(no_count_interval[0]<=no_count_interval[1],'source no-count readout contradicts its complete TNI support')
        intervals[query]={'centre':str(no_count[query]),'new_effect_and_arithmetic_price':str(local_new),
            'physical_no_count_interval':list(map(str,no_count_interval)),
            'two_source_effects':list(map(lambda row:row['coflow_source']['side'],rows))}
    event=mass-no_count['perp']-no_count['parallel']+no_count['all'];price=old+new
    interval=max(Q(0),event-price),min(upper,event+price)
    source.require(interval[0]<=interval[1],'source first-receipt readout contradicts its complete CP support')
    return {'schema':source.SCHEMA+'/complete-any-first-receipt-probability','original_current_sha256':source.digest(current_record),
        'source_detector_interval_seconds':law_record['gate_seconds'],'source_positive_mass_upper':str(upper),
        'source_whole_input_trace_centre':str(mass),'no_count_readouts':intervals,'any_first_receipt_mass_centre':str(event),
        'whole_new_effect_and_arithmetic_price':str(new),'old_whole_input_error_once':str(old),'whole_first_receipt_error':str(price),
        'physical_any_first_receipt_mass_interval':list(map(str,interval)),
        'source_event_is_complete_first_receipt':True,'specific_Psi_label_probability_claimed':False,
        'old_input_error_repeated_for_three_no_count_queries':False,'full_history_mother_reset':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False}


def check(freeze,prepared,results,output):
    bound=bindings(freeze);prepared,results,output=map(Path,(prepared,results,output));manifest=json.loads((prepared/'summary.json').read_text())
    source.require(manifest['schema']==source.SCHEMA+'/prepared' and manifest['scientific_freeze_commit']==freeze and manifest['source_bindings']==bound,
                   'the original complete frozen zero-count handoff is required')
    output.mkdir(parents=True,exist_ok=False);write(output/'attempt.json',{'phase':'check','scientific_freeze_commit':freeze,'source_bindings':bound})
    current=previous.paid.restore();raw=current.record();parent=source.ZeroCountReceiptSource(current._law);plans=inventory(parent)
    source.require(source.digest(raw)==manifest['original_current_sha256'] and
        json.loads(bank.artifact(manifest['complete_zero_count_source']).read_text())==parent.record() and
        [(r['query'],r['side']) for r in manifest['rows']]==[(q,s) for q,s,_ in plans],
        'same original input, all three queries and both physical arms are required')
    rows=[];reports=[]
    for row,(query,side,coflow) in zip(manifest['rows'],plans):
        source.require(json.loads(bank.artifact(row['handoff']).read_text())==handoff(coflow,freeze,bound) and
            independent.local_recycling(current._law.record(),side,source.PORT_SETS[query])==coflow.record()['complete_unobserved_local_recycling'],
            'the closed original coflow or independent raw natural restriction changed')
        curve=results/row['node_unit_id']/f'zero-count-{query}-{side}.jsonl.gz'
        report=checker.certify(coflow,curve,output/f'checked-{query}-{side}',progress=lambda p:print(json.dumps(p),flush=True))
        checked=output/f'checked-{query}-{side}/checked-coflow.json'
        rows.append({'query':query,'side':side,'coflow_source_sha256':source.digest(coflow.record()),'curve':bank.binding(curve),
            'checked_coflow':bank.binding(checked),'whole_new_operator_error':report['whole_new_operator_error'],
            'registered_accuracy_passed':report['registered_accuracy_passed']})
        reports.append({'query':query,'side':side,'report':report})
    probability=probability_from_effects(reports,raw,current._law.record());write(output/'first-receipt-probability.json',probability)
    report={'schema':source.SCHEMA+'/complete','scientific_freeze_commit':freeze,'source_bindings':bound,
        'complete_zero_count_source':manifest['complete_zero_count_source'],'rows':rows,'complete_query_side_count':len(rows),
        'all_registered_accuracy_gates_passed':all(r['registered_accuracy_passed'] for r in rows),
        'source_first_receipt_probability':bank.binding(output/'first-receipt-probability.json'),
        'complete_any_first_receipt_event_generated':True,'specific_Psi_label_probability_claimed':False,
        'Phi_B_source_response_determinant_certified':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}
    write(output/'summary.json',report);print(json.dumps({'complete_coflows':len(rows),'accuracy_passed':report['all_registered_accuracy_gates_passed'],
        'first_receipt_mass_interval':[float(Q(x)) for x in probability['physical_any_first_receipt_mass_interval']]}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('phase',choices=('prepare','check'));p.add_argument('--freeze',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepared',type=Path);p.add_argument('--results',type=Path);args=p.parse_args()
    try:
        if args.phase=='prepare':prepare(args.freeze,args.output)
        else:source.require(args.prepared is not None and args.results is not None,'original handoff and curve results required');check(args.freeze,args.prepared,args.results,args.output)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():write(args.output/'failure.json',{'schema':source.SCHEMA+'/failed-attempt','phase':args.phase,
            'scientific_freeze_commit':args.freeze,'reason':str(error),'actual_hardware_uniquely_identified':False,'controller_advance':False})
        raise

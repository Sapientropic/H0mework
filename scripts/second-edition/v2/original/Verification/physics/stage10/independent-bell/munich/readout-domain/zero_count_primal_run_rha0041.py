"""The complete source-owned forward bank for the original no-count queries."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import ast
import hashlib
import json
import subprocess

import zero_count_primal_source_rha0040 as source
import zero_count_primal_independent_rha0040 as independent
import zero_count_primal_check_rha0040 as checker
import first_receipt_flux_source_rha0040 as flux
import zero_count_run_rha0039 as previous
import zero_count_probability_price_rha0039_1 as activity_price

bank,HERE,ROOT=previous.bank,previous.HERE,previous.ROOT
SCHEMA='stage10-complete-source-primal-zero-count-bank/rha0041'
RHA40=('criterion-rha0040.md','FirstReceiptQuantumFlux.lean','first-receipt-quantum-flux-math-rha0040.json',
    'first_receipt_flux_source_rha0040.py','test_first_receipt_flux_rha0040.py',
    'zero_count_primal_source_rha0040.py','zero_count_primal_independent_rha0040.py',
    'zero_count_primal_integer_rha0040.py','zero_count_primal_proposal_rha0040.py',
    'zero_count_primal_check_rha0040.py','test_zero_count_primal_rha0040.py')
OWN=('criterion-rha0041.md','zero_count_primal_run_rha0041.py','test_zero_count_primal_run_rha0041.py')
INPUTS=(*RHA40,*activity_price.OWN,*activity_price.INPUTS,
    'first-receipt-probability-first-rha0039.1.json')


def bindings(freeze):
    paths={HERE/n for n in (*OWN,*INPUTS)}
    pending=[p for p in paths if p.suffix=='.py' and not p.name.startswith('test_')]
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
        source.base.require(subprocess.check_output(['git','-C',str(ROOT),'show',freeze+':'+relative])==raw,
                            'primal source science changed after freeze: '+relative)
        result[relative]=hashlib.sha256(raw).hexdigest()
    return result


def inventory(current,parent):
    raw=current.record()
    return [(query,side,index,source.LocalNoCountPrimalFlow(current,parent,side,index,query=query))
            for query in source.base.PORT_SETS for side,rows in enumerate(raw['checked_local_density_inventories'])
            for index in range(len(rows))]


def select(rows,query='all',side=0,index=0):
    source.base.require(query in source.base.PORT_SETS and type(side) is int and side in (0,1) and
        type(index) is int and index>=0,'registered query, physical side and source factor required')
    found=[r for r in rows if r['query']==query and r['side']==side and r['factor_index']==index]
    source.base.require(len(found)==1,'exactly one source factor from the complete bank required')
    return found[0]


def require_cover(rows,initial):
    source.base.require(all(type(r['query']) is str and type(r['side']) is int and type(r['factor_index']) is int for r in rows),
                        'source query and factor addresses retain their exact types')
    expected=[(q,s,i) for q in source.base.PORT_SETS for s,items in enumerate(initial['checked_local_density_inventories'])
              for i in range(len(items))]
    source.base.require([(r['query'],r['side'],r['factor_index']) for r in rows]==expected,
                        'all source factors, both arms and all queries must occur exactly once in source order')
    for row in rows:
        source.base.require(row['factor_id']==initial['checked_local_density_inventories'][row['side']][row['factor_index']]['factor_id'],
                            'source factor identity or incidence changed')


def handoff(flow,freeze,bound):
    return {'schema':source.SCHEMA+'/handoff','scientific_freeze_commit':freeze,'source_bindings':bound,
        'primal_source':flow.record(),'caller_initial_matrix_used':False,'actual_hardware_member_asserted':False}


def prepare(freeze,output):
    bound=bindings(freeze);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    previous.write(output/'attempt.json',{'phase':'prepare','scientific_freeze_commit':freeze,'source_bindings':bound})
    current=source.paid.restore();raw=current.record();parent=source.base.ZeroCountReceiptSource(current._law)
    previous.write(output/'zero-count-source.json',parent.record())
    previous.write(output/'first-flux-source.json',flux.FirstReceiptFluxSource(current._law).record())
    rows=[]
    for query,side,index,flow in inventory(current,parent):
        record=flow.record()
        source.base.require(independent.local_recycling(current._law.record(),side,source.base.PORT_SETS[query])==record['complete_unobserved_local_recycling'],
                            'independent original bath differs from the primal restriction')
        path=output/f'handoff-{query}-{side}-{index}.json';previous.write(path,handoff(flow,freeze,bound));b=bank.binding(path)
        rows.append({'query':query,'side':side,'factor_index':index,'factor_id':record['factor_id'],
            'primal_source_sha256':source.base.digest(record),'handoff':b,
            'node_unit_id':f'primal-{query}-{side}-{index}@{b["sha256"][:16]}'})
    require_cover(rows,raw)
    result={'schema':SCHEMA+'/prepared','scientific_freeze_commit':freeze,'source_bindings':bound,'rows':rows,
        'original_current_sha256':source.base.digest(raw),'complete_zero_count_source':bank.binding(output/'zero-count-source.json'),
        'complete_priority_flux_source':bank.binding(output/'first-flux-source.json'),
        'source_factor_ids':raw['source_factor_ids'],'old_whole_input_error_once':raw['whole_retarded_gate_input_error'],
        'new_pump_or_inlet_solves':0,'full_CEM_time_mother_issued':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}
    previous.write(output/'summary.json',result)
    print(json.dumps({'source_primal_flows':len(rows),'source_queries':len(source.base.PORT_SETS)}),flush=True)


def endpoint_readout(reports,initial,law):
    require_cover(reports,initial);terms=initial['source_factor_ids']
    inputs={(s,row['factor_id']):source.gaussian._matrix(row['complete_retarded_local_endpoint'])
            for s,items in enumerate(initial['checked_local_density_inventories']) for row in items}
    def trace(matrix):return sum((z for (i,j),z in matrix.items() if i==j),source.dipole.ComplexRadical())
    initial_mass=sum((trace(inputs[0,a])*trace(inputs[1,b]) for a,b in terms),source.dipole.ComplexRadical())
    source.base.require(not initial_mass.imag,'source initial trace must be real')
    mass,arithmetic=source.gaussian.full.radical_midpoint(initial_mass.real,192)
    duration=Q(law['gate_seconds'][1])-Q(law['gate_seconds'][0]);clock=law['complete_driven_field_source']['reference_clock']
    centre=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
    source.base.require(0<lo<=centre<=hi,'same positive mathematical Gamma family required')
    gamma=max(centre-lo,hi-centre)/centre
    old=Q(initial['whole_retarded_gate_input_error']);upper=Q(initial['source_positive_mass_upper']);values={};new=arithmetic;readouts={}
    for query,ports in source.base.PORT_SETS.items():
        local={};errors={};norms={}
        for row in reports:
            if row['query']!=query:continue
            r=row['report'];key=row['side'],row['factor_id'];raw=r['original_primal_source']
            source.base.require(raw['factor_id']==row['factor_id'] and raw['side']==row['side'] and raw['query']==query and
                raw['source_initial_physical_matrix']==initial['checked_local_density_inventories'][row['side']][row['factor_index']]['complete_retarded_local_endpoint'],
                'primal endpoint must retain its original inlet factor')
            local[key]=source.gaussian._matrix(r['complete_physical_endpoint'])
            errors[key]=Q(r['whole_new_endpoint_trace_norm_error']);norms[key]=Q(r['initial_entry_norm_upper'])
        value=sum((trace(local[0,a])*trace(local[1,b]) for a,b in terms),source.dipole.ComplexRadical())
        source.base.require(not value.imag,'source physical no-count trace must remain real')
        v,rounding=source.gaussian.full.radical_midpoint(value.real,192)
        pair=sum((errors[0,a]*norms[1,b]+errors[1,b]*norms[0,a]+errors[0,a]*errors[1,b] for a,b in terms),Q(0))
        rate=sum((Q(law['BG_source']['BG_rates_per_second'][p]) for p in ports),Q(0))
        weight,scalar=source.gaussian._exponential(-rate*duration,0,192);scalar+=rate*duration*gamma
        price=abs(weight[0])*pair+scalar*(upper+old+pair)+abs(weight[0])*rounding
        values[query]=weight[0]*v;new+=price
        interval=max(Q(0),values[query]-old-price),min(upper,values[query]+old+price)
        source.base.require(interval[0]<=interval[1],'source no-count endpoint contradicts its TNI support')
        readouts[query]={'centre':str(values[query]),'new_primal_and_arithmetic_price':str(price),
            'physical_no_count_interval':list(map(str,interval)),'source_factor_incidence_preserved':True}
    event=mass-values['perp']-values['parallel']+values['all'];error=old+new
    interval=max(Q(0),event-error),min(upper,event+error)
    source.base.require(interval[0]<=interval[1],'source primal first-receipt endpoint contradicts its CP support')
    # The output is the existing complete first-receipt query; only its
    # construction changes from adjoint effects to source-issued primal states.
    return {'schema':previous.source.SCHEMA+'/complete-any-first-receipt-probability',
        'source_readout_construction':'complete source-owned primal TNI bank',
        'original_current_sha256':source.base.digest(initial),'source_detector_interval_seconds':law['gate_seconds'],
        'source_positive_mass_upper':str(upper),'source_whole_input_trace_centre':str(mass),'no_count_readouts':readouts,
        'any_first_receipt_mass_centre':str(event),'whole_new_effect_and_arithmetic_price':str(new),
        'old_whole_input_error_once':str(old),'whole_first_receipt_error':str(error),
        'physical_any_first_receipt_mass_interval':list(map(str,interval)),
        'source_event_is_complete_first_receipt':True,'old_input_error_repeated_for_three_no_count_queries':False,
        'signed_factor_positivity_assumed':False,'specific_Psi_label_probability_claimed':False,
        'CEM_time_mother_issued':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}


def compare_adjoint(primal,adjoint):
    source.base.require(primal['original_current_sha256']==adjoint['original_current_sha256'] and
        primal['source_detector_interval_seconds']==adjoint['source_detector_interval_seconds'],
        'primal and adjoint consumers must use the same initial source and query')
    difference=abs(Q(primal['any_first_receipt_mass_centre'])-Q(adjoint['any_first_receipt_mass_centre']))
    price=Q(primal['whole_new_effect_and_arithmetic_price'])+Q(adjoint['whole_new_effect_and_arithmetic_price'])
    source.base.require(difference<=price,'independent complete primal-adjoint source readouts disagree')
    return {'complete_initial_current_and_gate_equal':True,'centre_difference':str(difference),
        'new_error_sum':str(price),'old_input_error_needed_for_numerical_duality_check':False}


def check(freeze,prepared,results,output):
    bound=bindings(freeze);prepared,results,output=map(Path,(prepared,results,output));manifest=json.loads((prepared/'summary.json').read_text())
    source.base.require(manifest['schema']==SCHEMA+'/prepared' and manifest['scientific_freeze_commit']==freeze and manifest['source_bindings']==bound,
                        'the complete frozen source-owned primal handoff is required')
    output.mkdir(parents=True,exist_ok=False);previous.write(output/'attempt.json',{'phase':'check','scientific_freeze_commit':freeze,'source_bindings':bound})
    current=source.paid.restore();raw=current.record();parent=source.base.ZeroCountReceiptSource(current._law)
    require_cover(manifest['rows'],raw);plans=inventory(current,parent)
    source.base.require(source.base.digest(raw)==manifest['original_current_sha256'] and
        json.loads(bank.artifact(manifest['complete_zero_count_source']).read_text())==parent.record() and
        json.loads(bank.artifact(manifest['complete_priority_flux_source']).read_text())==flux.FirstReceiptFluxSource(current._law).record(),
        'original current, no-count law or source priority changed')
    rows=[];reports=[]
    for row,(query,side,index,flow) in zip(manifest['rows'],plans):
        source.base.require(json.loads(bank.artifact(row['handoff']).read_text())==handoff(flow,freeze,bound) and
            independent.local_recycling(current._law.record(),side,source.base.PORT_SETS[query])==flow.record()['complete_unobserved_local_recycling'],
            'original factor handoff or independent bath restriction changed')
        curve=results/row['node_unit_id']/f'primal-{query}-{side}-{index}.jsonl.gz'
        report=checker.certify(flow,curve,output/f'checked-{query}-{side}-{index}',progress=lambda p:print(json.dumps(p),flush=True))
        record=flow.record();checked=output/f'checked-{query}-{side}-{index}/checked-primal.json'
        rows.append({'query':query,'side':side,'factor_index':index,'factor_id':record['factor_id'],
            'primal_source_sha256':source.base.digest(record),'curve':bank.binding(curve),'checked_primal':bank.binding(checked),
            'whole_new_uniform_trace_norm_error':report['whole_new_uniform_trace_norm_error'],
            'whole_new_endpoint_trace_norm_error':report['whole_new_endpoint_trace_norm_error'],
            'registered_accuracy_passed':report['registered_accuracy_passed']})
        reports.append({**row,'report':report})
    first=endpoint_readout(reports,raw,current._law.record())
    adjoint=json.loads(source.paid.paid.frozen(HERE/'first-receipt-probability-first-rha0039.json'))
    first['independent_accepted_adjoint_readout']=compare_adjoint(first,adjoint)
    previous.write(output/'primal-first-receipt.json',first)
    normalizer=json.loads(source.paid.paid.frozen(HERE/'retarded-normalizer-first-rha0028.json'))
    source.base.require(normalizer['source_bindings']=={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in normalizer['source_bindings']},
                        'the paid same-source activity certificate changed')
    activity=json.loads(bank.artifact(normalizer['report']).read_text())['complete_source_activity_cap'];ar=activity['source_record']
    source.base.require(ar['source_activity']==activity_price.activity._facts(current._law.record(),ar['scalar_bits']) and
        activity['source_bindings']==activity_price.activity._bindings(),'original complete activity derivation changed')
    priced=activity_price.contract(first,activity,current._law.record());previous.write(output/'primal-first-receipt-priced.json',priced)
    result={'schema':SCHEMA+'/complete','scientific_freeze_commit':freeze,'source_bindings':bound,
        'rows':rows,'complete_source_factor_query_count':len(rows),'all_registered_accuracy_gates_passed':all(r['registered_accuracy_passed'] for r in rows),
        'complete_zero_count_source':manifest['complete_zero_count_source'],'complete_priority_flux_source':manifest['complete_priority_flux_source'],
        'source_primal_first_receipt':bank.binding(output/'primal-first-receipt.json'),
        'source_primal_first_receipt_priced':bank.binding(output/'primal-first-receipt-priced.json'),
        'independent_accepted_adjoint_readout':first['independent_accepted_adjoint_readout'],
        'full_CEM_time_mother_issued':False,'specific_Psi_label_probability_claimed':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False}
    previous.write(output/'summary.json',result)
    print(json.dumps({'complete_primal_flows':len(rows),'accuracy_passed':result['all_registered_accuracy_gates_passed'],
        'first_receipt_mass_interval':[float(Q(x)) for x in priced['physical_any_first_receipt_mass_interval']]}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('phase',choices=('prepare','check'));p.add_argument('--freeze',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepared',type=Path);p.add_argument('--results',type=Path);args=p.parse_args()
    try:
        if args.phase=='prepare':prepare(args.freeze,args.output)
        else:source.base.require(args.prepared is not None and args.results is not None,'original source handoffs and proposed curves required');check(args.freeze,args.prepared,args.results,args.output)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():previous.write(args.output/'failure.json',{'schema':SCHEMA+'/failed-attempt','phase':args.phase,
            'scientific_freeze_commit':args.freeze,'reason':str(error),'actual_hardware_uniquely_identified':False,'controller_advance':False})
        raise

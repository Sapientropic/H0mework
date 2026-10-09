"""Original first-receipt quantum flux, including the source's pattern priority.

The first port of the opposite polarization closes the receipt. Its two
possible partners are ordered by the original FPGA rule. At most seven no-count
coimages suffice to retain every labelled flux without a Mark-state bank.
"""
from fractions import Fraction as Q
import json

import zero_count_receipt_rha0039 as base

SCHEMA='stage10-original-priority-first-receipt-quantum-flux/rha0040'
_ISSUED={}


def _name(ports):
    ports=tuple(sorted(ports))
    for name,original in base.PORT_SETS.items():
        if ports==original:return name
    return 'no-'+ '-'.join(map(str,ports))


def compile_flux(original):
    base.require(type(original) is base.law.RetardedGaussianBSMSource,
                 'closed original retarded BSM source required')
    raw=original.record();marks=base._marks(original);queries={};flux=[]
    for port in range(4):
        own=next(set(ports) for name,ports in base.PORT_SETS.items() if name!='all' and port in ports)
        order=[p for p in original._gate.pattern_priority if port in base.bsm.PATTERNS[p][1]]
        base.require(len(order)==2,'the original priority must supply both opposite partners')
        earlier=next(p for p in base.bsm.PATTERNS[order[0]][1] if p!=port)
        restrictions=(tuple(sorted(own)),tuple(sorted(own|{earlier})),base.PORT_SETS['all'])
        for ports in restrictions:queries[_name(ports)]=ports
        for rank,pattern in enumerate(order):
            positive,negative=restrictions[rank:rank+2]
            for mark in marks:
                before=mark.receipt is None
                target=base.bsm.BSMSource.target(original._gate,mark,port)
                actual=int(before and target.receipt==pattern)
                plus=int(before and not any(mark.counts[p] for p in positive))
                minus=int(before and not any(mark.counts[p] for p in negative))
                base.require(actual==plus-minus,'source pattern priority and no-count flux disagree')
            flux.append({'port':port,'pattern':pattern,'herald':base.bsm.PATTERNS[pattern][0],
                'priority_rank_for_this_port':rank,'positive_query':_name(positive),'negative_query':_name(negative),
                'original_pending_Mark_projectors_checked':len(marks)})
    inventory=[]
    for name,ports in sorted(queries.items()):
        for mark in marks:
            inside=mark.receipt is None and not any(mark.counts[p] for p in ports)
            for port in range(4):
                target=base.bsm.BSMSource.target(original._gate,mark,port)
                after=target.receipt is None and not any(target.counts[p] for p in ports)
                base.require(after==(inside and port not in ports),'original no-count face is not closed')
        transfer=tuple(original._transfer[p] for p in ports)
        _,gram,complement=base.joint.passive_transfer(transfer)
        coupled=any(gram[i][j] for i in range(3) for j in range(3,6))
        inventory.append({'query':name,'forbidden_ports':list(ports),
            'selected_source_transfer_Gram':base.law.optical._matrix(gram),
            'selected_source_transfer_complement':base.law.optical._matrix(complement),
            'cross_arm_Gram_nonzero':bool(coupled),'requires_coupled_no_count_flow':bool(coupled),
            'background_no_count_rate_per_second':str(sum((Q(raw['BG_source']['BG_rates_per_second'][p]) for p in ports),Q(0))),
            'original_Mark_port_transitions_checked':4*len(marks)})
    base.require(5<=len(inventory)<=7 and len(flux)==8,'all original priority-resolved fluxes required')
    return {'schema':SCHEMA,'original_retarded_source':raw,'complete_no_count_queries':inventory,
        'complete_priority_resolved_port_fluxes':flux,
        'pending_quantum_coimage':'sigma_perp + sigma_parallel - sigma_all',
        'any_port_flux':'J_port(sigma_own_polarization - sigma_all)',
        'labelled_port_flux':'J_port(sigma_positive_query - sigma_negative_query)',
        'J_port':'original coherent detected action plus original BG_port times identity',
        'input_time_reference':'original physical detector time; both local clocks retained',
        'source_pattern_priority':list(original._gate.pattern_priority),
        'source_Mark_receipt_latch_retained':True,'physical_time_atom_state_claimed':False,
        'zero_count_curves_certified_here':False,'CEM_time_mother_issued_here':False,
        'whole_hardware_domain_local_factorization_claimed':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False}


class FirstReceiptFluxSource:
    def __init__(self,original):
        self._original=original;self._value=compile_flux(original);self._seal=base.digest(self._value)
        _ISSUED[id(self)]=(original,self._seal)

    def record(self):
        base.require(type(self) is FirstReceiptFluxSource and set(vars(self))=={'_original','_value','_seal'} and
            _ISSUED.get(id(self))==(self._original,self._seal) and base.digest(self._value)==self._seal and
            self._original.record()==self._value['original_retarded_source'],'original flux source or priority changed')
        return json.loads(base.channel._canonical(self._value))

    def project_pending(self,state):
        raw=self.record();blocks=base.bsm.BSMSource.blocks(self._original._gate,state)
        base.require(all(mark.receipt is None for mark in blocks),'only original pending Mark states required')
        result={}
        for query in raw['complete_no_count_queries']:
            matrix={}
            for mark,block in blocks.items():
                if not any(mark.counts[p] for p in query['forbidden_ports']):base.law._add(matrix,block)
            result[query['query']]=matrix
        return result

    def contract(self,detector_time,coimages):
        """Apply the compiled operator to supplied matrices; this issues no time measure."""
        raw=self.record();time=Q(detector_time);a,b=map(Q,raw['original_retarded_source']['gate_seconds'])
        base.require(a<=time<=b and type(coimages) is dict and
            set(coimages)=={r['query'] for r in raw['complete_no_count_queries']},
            'original clock and all source-issued coimages required for labelled quantum flux')
        coimages={q:base.joint._matrix(m) for q,m in coimages.items()};answer=[{} for _ in base.bsm.PATTERNS]
        times=self._original.local_times(time);beta=tuple(map(Q,raw['original_retarded_source']['BG_source']['BG_rates_per_second']))
        for term in raw['complete_priority_resolved_port_fluxes']:
            matrix=dict(coimages[term['positive_query']]);base.law._add(matrix,coimages[term['negative_query']],-1)
            value=self._original._detected(matrix,times,term['port']);base.law._add(value,matrix,beta[term['port']])
            base.law._add(answer[term['pattern']],value)
        return answer

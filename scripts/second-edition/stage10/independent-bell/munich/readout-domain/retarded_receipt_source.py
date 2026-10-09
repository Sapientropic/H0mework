"""Retained full33 photon field and the original first-receipt BG port law.

The field is an operator-valued zero/one/two-photon wavefunction.  Its
off-diagonal time kernel is retained, including loss and future arrivals.
Background histories act on the original detector marks, independently of
the matter/field state.  A no-BG-through-end readout is a subinstrument of
this complete mother, with an explicitly priced positive complement.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import bsm_retry_source as bsm
import common_optical_readout as optical
import prepared_retarded_source as prepared
import retarded_photon_source as scalar


SCHEMA = 'stage10-retarded-field-full-first-receipt-source/v1'
ZERO = dipole.ComplexRadical()
_ISSUED = set()


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings(field=False):
    modules = (dipole, full, channel, local, joint, bsm, optical, scalar)
    if field:
        modules += (prepared,)
    paths = [Path(__file__), *(Path(m.__file__) for m in modules)]
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _matrix(record,dimension=joint.DIMENSION):
    _require(type(record) is list,'complete raw linear operator record required')
    result={}
    for item in record:
        _require(type(item) is list and len(item)==3,'raw source matrix coordinate required')
        i,j,value=item
        _require(type(i) is int and type(j) is int and 0<=i<dimension and 0<=j<dimension and (i,j) not in result,
                 'original unique linear operator coordinates required')
        result[i,j]=channel._complex_record(value)
    checked=joint._matrix(result) if dimension==joint.DIMENSION else local._matrix(result)
    _require(channel._input_record(checked)==record,'canonical raw linear operator record required')
    return checked


def _subsets(values):
    return (subset for size in range(len(values)+1) for subset in combinations(values,size))


def _mask(mark):
    return sum(int(bool(c)) << p for p,c in enumerate(mark.counts))


def _mark(mask):
    return bsm.Mark(tuple(int(bool(mask & (1 << p))) for p in range(4)))


def _sum_scalar(terms):
    return sum((c for c,e in terms),Q(0)), sum((e for c,e in terms),Q(0))


def _probability(value,error,bits):
    value,error=scalar._interval(value,error)
    quantum=1 << bits
    a=(value-error)*quantum;z=(value+error)*quantum
    lo=a.numerator//a.denominator;hi=-((-z.numerator)//z.denominator)
    return Q(lo+hi,2*quantum),Q(hi-lo,2*quantum)


def _exp_integral(rate,left,right,bits):
    if not rate:
        return right-left,Q(0)
    a,da=scalar._exp_negative(rate*left,bits)
    b,db=scalar._exp_negative(rate*right,bits)
    return (a-b)/rate,(da+db)/rate


def _emission_BG_integral(gamma,first_rate,second_rate,duration,bits):
    """Integral gamma*exp(-(gamma+a)t-b(T-t)), with decaying endpoints."""
    b,db=scalar._exp_negative(second_rate*duration,bits)
    difference=gamma+first_rate-second_rate
    if not difference:
        return gamma*duration*b,gamma*duration*db
    a,da=scalar._exp_negative((gamma+first_rate)*duration,bits)
    return gamma*(b-a)/difference,gamma*(db+da)/abs(difference)


class PortBackgroundLaw:
    def __init__(self,common):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('retarded receipt source execution closure changed')
        _guard()
        _require(type(common) is optical.CommonOpticalReadout,'closed common four-port optical source required')
        pack=optical.CommonOpticalReadout.record(common)
        gate,_=optical.CommonOpticalReadout.bsm_gate(common)
        unit=gate.seconds_per_unit
        rates=tuple(Q(r)/unit for r in pack['background_rates'])
        pending=[]
        for mask in range(16):
            try:
                _mark(mask)
                pending.append(mask)
            except ValueError:
                continue
        checks=[]
        for counts in product(range(3),repeat=4):
            for receipt in (None,0,1,2,3):
                try:
                    mark=bsm.Mark(counts,receipt)
                except ValueError:
                    continue
                for port in range(4):
                    target=bsm.BSMSource.target(gate,mark,port)
                    _require(_mask(target)==(_mask(mark)|(1<<port)),'BG presence projection is not monotone')
                    if receipt is None:
                        projected=bsm.BSMSource.target(gate,_mark(_mask(mark)),port)
                        _require(target.receipt==projected.receipt,'presence lump loses original first pattern priority')
                    else:
                        _require(target.receipt==receipt,'original receipt was erased')
                    checks.append([list(counts),receipt,port,target.receipt])
        flux={}
        insertions={}
        for mask in pending:
            row=[]
            for port in range(4):
                target=bsm.BSMSource.target(gate,_mark(mask),port)
                row.append({'port':port,'presence':_mask(target),'receipt':target.receipt})
            insertions[mask]=row
            for h in range(4):
                flux[mask,h]=sum((rates[p] for p in range(4) if row[p]['receipt']==h),Q(0))
        self._frame={'schema':SCHEMA+'/BG-port-law','common_optical_source':pack,'raw_BSM_gate':gate.record(),
            'seconds_per_source_unit':str(unit),'raw_rates_per_source_unit':pack['background_rates'],
            'BG_rates_per_second':list(map(str,rates)),'pending_presence_masks':pending,
            'presence_source_checks':checks,'presence_insertions':[[s,insertions[s]] for s in pending],
            'BG_receipt_flux_rates':[[s,h,str(flux[s,h])] for s in pending for h in range(4)],
            'lump_scope':'BSM first-receipt query only; the full BG/arrival word and native rolling queue are retained',
            'source_bindings':_bindings(),'controller_advance':False}
        self._seal=_digest(self._frame)
        _ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('retarded receipt source execution closure changed')
        _guard()
        _require(type(self) is PortBackgroundLaw and set(vars(self))=={'_frame','_seal'} and self._seal in _ISSUED and
                 _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),'BG source/callback/unit changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is PortBackgroundLaw and type(record) is dict,'closed BG source record required')
        result=cls(optical.CommonOpticalReadout.from_record(record['common_optical_source']))
        _require(PortBackgroundLaw.record(result)==record,'original port BG law changed')
        return result

    def transition_terms(self,start,end):
        record=PortBackgroundLaw.record(self)
        masks=record['pending_presence_masks']
        _require(type(start) is int and type(end) is int and start in masks and end in masks,'original transient presence masks required')
        if start & end != start:
            return []
        rates=tuple(map(Q,record['BG_rates_per_second']))
        added=[p for p in range(4) if end & (1<<p) and not start & (1<<p)]
        base=sum((rates[p] for p in range(4) if not end & (1<<p)),Q(0))
        return [(Q((-1)**len(subset)),base+sum((rates[p] for p in subset),Q(0))) for subset in _subsets(added)]

    def transition(self,start,end,duration,*,bits=160):
        duration=full.nonnegative(duration)
        terms=[]
        for coefficient,rate in PortBackgroundLaw.transition_terms(self,start,end):
            centre,error=scalar._exp_negative(rate*duration,bits)
            terms.append((coefficient*centre,abs(coefficient)*error))
        return _probability(*_sum_scalar(terms),bits)

    def insertion(self,mask,port):
        record=PortBackgroundLaw.record(self)
        _require(type(port) is int and port in range(4),'original physical port required')
        row=next((row for s,row in record['presence_insertions'] if s==mask),None)
        _require(row is not None,'original transient mark required')
        return _copy(row[port])

    def receipt_terms(self,pattern,*,start=0):
        record=PortBackgroundLaw.record(self)
        _require(type(pattern) is int and 0<=pattern<4,'original first receipt pattern required')
        result={}
        for mask,h,rate in record['BG_receipt_flux_rates']:
            if h!=pattern or not Q(rate):
                continue
            for coefficient,exponent in PortBackgroundLaw.transition_terms(self,start,mask):
                result[exponent]=result.get(exponent,Q(0))+Q(rate)*coefficient
        return [(coefficient,rate) for rate,coefficient in sorted(result.items()) if coefficient]

    def _cumulative_terms(self,pattern,start):
        result={}
        for coefficient,rate in PortBackgroundLaw.receipt_terms(self,pattern,start=start):
            _require(rate>0,'a surviving zero-rate mode cannot feed a positive absorbing BG flux')
            result[Q(0)]=result.get(Q(0),Q(0))+coefficient/rate
            result[rate]=result.get(rate,Q(0))-coefficient/rate
        return [(c,r) for r,c in sorted(result.items()) if c]

    def _one_signal_integral(self,port,gamma,duration,bits):
        """Entire original BG law, integrated over one source-born photon clock."""
        record=PortBackgroundLaw.record(self);masks=record['pending_presence_masks']
        if not any(map(Q,record['BG_rates_per_second'])):
            _require(PortBackgroundLaw.insertion(self,0,port)['receipt'] is None,
                     'the original detector cannot receipt from a single signal port')
            return [(Q(0),Q(0))]*4+[scalar._cdf(gamma,0,duration,bits)]
        success_terms=[[(c,a,Q(0)) for c,a in PortBackgroundLaw._cumulative_terms(self,h,0)] for h in range(4)]
        failure_terms=[]
        for s in masks:
            before=PortBackgroundLaw.transition_terms(self,0,s)
            insertion=PortBackgroundLaw.insertion(self,s,port)
            if insertion['receipt'] is not None:
                success_terms[insertion['receipt']].extend((c,a,Q(0)) for c,a in before)
                continue
            target=insertion['presence']
            for h in range(4):
                after=PortBackgroundLaw._cumulative_terms(self,h,target)
                success_terms[h].extend((c*d,a,b) for c,a in before for d,b in after)
            for end in masks:
                after=PortBackgroundLaw.transition_terms(self,target,end)
                failure_terms.extend((c*d,a,b) for c,a in before for d,b in after)
        values=[]
        for terms in [*success_terms,failure_terms]:
            entries=[]
            for coefficient,a,b in terms:
                value,error=_emission_BG_integral(gamma,a,b,duration,bits)
                entries.append((coefficient*value,abs(coefficient)*error))
            values.append(_probability(*_sum_scalar(entries),bits))
        return values

    def interval(self,left,right,*,duration,bits=160):
        record=PortBackgroundLaw.record(self)
        left,right,duration=map(full.nonnegative,(left,right,duration))
        _require(0<=left<=right<=duration,'BG query must retain its original gate origin')
        successes=[]
        for h in range(4):
            entries=[]
            for coefficient,rate in PortBackgroundLaw.receipt_terms(self,h):
                value,error=_exp_integral(rate,left,right,bits)
                entries.append((coefficient*value,abs(coefficient)*error))
            value,error=_probability(*_sum_scalar(entries),bits)
            successes.append({'pattern':h,'centre':str(value),'error':str(error)})
        failure=_probability(*_sum_scalar([PortBackgroundLaw.transition(self,0,s,duration,bits=bits) for s in record['pending_presence_masks']]),bits)
        return {'schema':SCHEMA+'/BG-first-receipt','source_record':record,'restriction_after_gate_origin':[str(left),str(right)],
            'gate_width_seconds':str(duration),'four_first_receipt_masses':successes,
            'gate_end_failure_mass':{'centre':str(failure[0]),'error':str(failure[1])},'scalar_bits':bits,
            'earlier_in_gate_BG_mark_retained':True,'BG_native_queue_reset':False}

    def path(self,signal_word,time,*,receipt_port=None,bits=160):
        """BG propagation along an actual ordered physical signal-arrival word."""
        record=PortBackgroundLaw.record(self)
        time=full.nonnegative(time)
        _require(type(signal_word) is list and all(type(x) is list and len(x)==2 for x in signal_word),
                 'ordered source signal port/time coordinates required')
        word=[(full.nonnegative(t),p) for t,p in signal_word]
        _require(all(type(p) is int and p in range(4) and t<=time for t,p in word) and
                 all(a[0]<=b[0] for a,b in zip(word,word[1:])),'causal ordered signal arrivals required')
        current={0:(Q(1),Q(0))};elapsed=Q(0)
        for endpoint,port in [*word,(time,None)]:
            following={}
            for s,(value,error) in current.items():
                for t in record['pending_presence_masks']:
                    weight=PortBackgroundLaw.transition(self,s,t,endpoint-elapsed,bits=bits)
                    term=scalar._product((value,error),weight)
                    if port is None:
                        target=t
                    else:
                        action=PortBackgroundLaw.insertion(self,t,port)
                        if action['receipt'] is not None:
                            continue
                        target=action['presence']
                    a,b=following.get(target,(Q(0),Q(0)))
                    following[target]=(a+term[0],b+term[1])
            current,elapsed=following,endpoint
        values=[]
        for h in range(4):
            terms=[]
            for s,(value,error) in current.items():
                if receipt_port is None:
                    rate=next(Q(r) for mask,k,r in record['BG_receipt_flux_rates'] if mask==s and k==h)
                else:
                    _require(type(receipt_port) is int and receipt_port in range(4),'physical completing signal port required')
                    rate=Q(PortBackgroundLaw.insertion(self,s,receipt_port)['receipt']==h)
                terms.append((value*rate,error*rate))
            values.append(_sum_scalar(terms))
        return {'pending_presence_weights':[[s,str(v),str(e)] for s,(v,e) in sorted(current.items())],
                'receipt_weights':[[h,str(v),str(e)] for h,(v,e) in enumerate(values)],
                'weights_are_BG_rate_density':receipt_port is None,'full_BG_word_is_not_reconstructed_from_presence':True}

    def full_word(self,word,*,duration,bits=160):
        record=PortBackgroundLaw.record(self);duration=full.nonnegative(duration)
        _require(type(word) is list,'full ordered BG word required')
        source=bsm.BSMSource.from_record(record['raw_BSM_gate']);mark=bsm.INITIAL
        rates=tuple(map(Q,record['BG_rates_per_second']))
        value,error=scalar._exp_negative(sum(rates,Q(0))*duration,bits)
        previous=Q(0);receipt=None;clock=None;trajectory=[]
        for entry in word:
            _require(type(entry) is list and len(entry)==2,'BG physical time/port required')
            time,port=full.nonnegative(entry[0]),entry[1]
            _require(previous<=time<=duration and type(port) is int and port in range(4),'causal original BG word required')
            value*=rates[port];error*=rates[port]
            mark=bsm.BSMSource.target(source,mark,port)
            if receipt is None and mark.receipt is not None:
                receipt,clock=mark.receipt,time
            trajectory.append({'time_after_gate_origin':str(time),'port':port,'counts':list(mark.counts),'receipt':mark.receipt})
            previous=time
        return {'source_record':record,'full_BG_word':_copy(word),'full_mark_trajectory':trajectory,
                'first_receipt':receipt,'first_receipt_time':None if clock is None else str(clock),
                'ordered_word_probability_density':str(value),'scalar_error':str(error),
                'dimension_of_BG_time_density':len(word),'no_native_queue_replaced_by_presence':True}


def _tensor(a,b):
    return {(joint.atom_pair_index(i,k),joint.atom_pair_index(j,l)):v*w for (i,j),v in a.items() for (k,l),w in b.items() if v*w}


def _add(a,b,weight=1):
    for key,value in b.items():
        local._add(a,key,value*weight)


class RetardedReceiptSource:
    def __init__(self,common,field):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('retarded receipt source execution closure changed')
        _guard()
        _require(type(common) is optical.CommonOpticalReadout and type(field) is prepared.FieldOffPhotonKernel,
                 'same closed common optics and complete field-off kernel required; target state is not input')
        pack=optical.CommonOpticalReadout.record(common)
        raw=prepared.FieldOffPhotonKernel.record(field)
        _require(pack['common_atomic_owner']==raw['common_atomic_programme'],'retarded field and port clocks need one atomic owner')
        _require(pack['collection_a']==raw['raw_collection'][0] and pack['collection_b']==raw['raw_collection'][1] and
                 pack['splitter']==raw['raw_splitter'] and pack['efficiencies']==raw['raw_efficiencies'],'retarded field and BG must use the same optical hardware')
        g0,g1=map(Q,raw['raw_gate_seconds'])
        _require(g0>=max(map(Q,raw['raw_emission_origin_seconds'])),'BG gate cannot precede the source-prepared atomic endpoints')
        transfer=tuple(tuple(channel._complex_record(v) for v in row) for row in pack['generated_four_by_six_transfer'])
        _,_,loss=joint.passive_transfer(transfer)
        completeness={}
        for group,info in field._groups.items():
            for q in dipole.Q_COMPONENTS:
                operator={(g,e):v for (component,g,e),v in info['operators'].items() if component==q}
                _add(completeness,dipole.matrix_product(dipole.matrix_adjoint(operator),operator))
        expected={(i,i):dipole.ComplexRadical(1) for i,s in enumerate(dipole.STATES) if s.family in ('D1','D2')}
        _require(completeness==expected,'complete original one-photon source must supply every excited column exactly once')
        self._field,self._bg=field,PortBackgroundLaw(common)
        self._frame={'schema':SCHEMA,'complete_field_source':raw,'BG_source':self._bg.record(),
            'loss_environment_gram':[[v.serialize() for v in row] for row in loss],
            'natural_one_photon_completeness':channel._input_record(completeness),
            'field_trace_measure':{'ordered_coordinate_sectors':[0,1,2],
                'two_photon_wavefunction_factor':dipole.sqrt_rational(Q(1,2)).serialize(),
                'chronological_k_photon_measurement_factor_squared':[[n,k,str(_falling(n,k))] for n in range(3) for k in range(n+1)],
                'detected_port_gram':[[int(p==q) for q in range(4)] for p in range(4)],
                'loss_gram':[[v.serialize() for v in row] for row in loss],
                'resolved_group_gram':[[list(g),list(h),int(g==h)] for g in field._groups for h in field._groups],
                'original_resolved_mode_operators':[{'group':list(g),'q':q,
                    'full33_operator':channel._input_record({(i,j):v for (component,i,j),v in info['operators'].items() if component==q})}
                    for g,info in field._groups.items() for q in dipole.Q_COMPONENTS]},
            'field_photon_numbers':[0,1,2],'all_full33_input_columns_retained':True,
            'gate_seconds':[str(g0),str(g1)],'source_bindings':_bindings(True),'controller_advance':False}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('retarded receipt source execution closure changed')
        _guard()
        _require(type(self) is RetardedReceiptSource and set(vars(self))=={'_field','_bg','_frame','_seal'} and self._seal in _ISSUED and
                 _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(True) and
                 prepared.FieldOffPhotonKernel.record(self._field)==self._frame['complete_field_source'] and
                 PortBackgroundLaw.record(self._bg)==self._frame['BG_source'],'retarded full field/BG source changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is RetardedReceiptSource and type(record) is dict,'complete retarded receipt source required')
        bg=PortBackgroundLaw.from_record(record['BG_source'])
        common=optical.CommonOpticalReadout.from_record(bg.record()['common_optical_source'])
        field=prepared.FieldOffPhotonKernel.from_record(record['complete_field_source'])
        result=cls(common,field)
        _require(result.record()==record,'retarded receipt source identity changed')
        return result

    def _emission(self,side,group,mode,time,observation,bits):
        raw=RetardedReceiptSource.record(self)['complete_field_source']
        origin=Q(raw['raw_emission_origin_seconds'][side]);flight=Q(raw['raw_flight_seconds'][side])
        if not origin<=time-flight<=observation:
            return {},Q(0)
        if mode[0]=='port':
            port=mode[1]
            pack=self._frame['BG_source']['common_optical_source']
            transfer=tuple(tuple(channel._complex_record(v) for v in row) for row in pack['generated_four_by_six_transfer'])
            coefficients={q:transfer[port][3*side+dipole.Q_COMPONENTS.index(q)] for q in dipole.Q_COMPONENTS}
        else:
            coefficients={q:dipole.ComplexRadical(int(mode[1]==3*side+dipole.Q_COMPONENTS.index(q))) for q in dipole.Q_COMPONENTS}
        matrix,error={},Q(0)
        for q,coefficient in coefficients.items():
            if not coefficient:
                continue
            report=prepared.FieldOffPhotonKernel.emission_operator(self._field,side,group,q,time,observation,bits=bits)
            operator=_matrix(report['full33_one_photon_operator'],full.DIMENSION)
            _add(matrix,operator,coefficient)
            error+=Q(report['operator_norm_error_upper'])*bsm._entry_norm({(0,0):coefficient},bits=bits)
        return matrix,error

    def field_amplitude(self,word,observation,*,bits=160):
        """Executable full matter/field wavefunction in its photon-time basis."""
        record=RetardedReceiptSource.record(self);observation=full.nonnegative(observation)
        _require(type(word) is list and len(word)<=2,'zero, one or two retained photon coordinates required')
        _require(observation>=max(map(Q,record['complete_field_source']['raw_emission_origin_seconds'])),'observation precedes an atomic endpoint')
        vacuum=[];vac_errors=[]
        for side in (0,1):
            report=prepared.FieldOffPhotonKernel.no_emission_operator(self._field,side,observation,bits=bits)
            vacuum.append(_matrix(report['full33_vacuum_operator'],full.DIMENSION))
            vac_errors.append(Q(report['operator_norm_error_upper']))
        emissions=[]
        for entry in word:
            _require(type(entry) is dict and set(entry)=={'group','mode','arrival_seconds'},'original photon environment/time coordinate required')
            group=tuple(entry['group']);mode=tuple(entry['mode']);time=full.nonnegative(entry['arrival_seconds'])
            _require(group in self._field._groups and len(mode)==2 and mode[0] in ('port','loss') and type(mode[1]) is int and
                     0<=mode[1]<(4 if mode[0]=='port' else 6),'source radiation group and physical/loss environment required')
            emissions.append(tuple(RetardedReceiptSource._emission(self,side,group,mode,time,observation,bits) for side in (0,1)))
        if not word:
            operator=_tensor(*vacuum);error=sum(vac_errors,Q(0))+vac_errors[0]*vac_errors[1]
        elif len(word)==1:
            (a,ea),(b,eb)=emissions[0];operator={}
            _add(operator,_tensor(a,vacuum[1]));_add(operator,_tensor(vacuum[0],b))
            error=ea*(1+vac_errors[1])+eb*(1+vac_errors[0])+vac_errors[1]*bsm._entry_norm(a,bits=bits)+vac_errors[0]*bsm._entry_norm(b,bits=bits)
        else:
            (a,ea),(b,eb)=emissions[0];(c,ec),(d,ed)=emissions[1]
            operator={};normalizer=dipole.sqrt_rational(Q(1,2))
            _add(operator,_tensor(a,d),normalizer);_add(operator,_tensor(c,b),normalizer)
            error=ea*bsm._entry_norm(d,bits=bits)+ed*bsm._entry_norm(a,bits=bits)+ea*ed+\
                  ec*bsm._entry_norm(b,bits=bits)+eb*bsm._entry_norm(c,bits=bits)+ec*eb
        return {'source_record':record,'physical_observation_seconds':str(observation),'photon_word':_copy(word),
            'full_pair_operator':channel._input_record(operator),'operator_error_upper':str(error),
            'field_basis':'symmetric ordered-coordinate Fock basis; loss coordinates carry source Gram I-T*T',
            'two_Bose_assignments_retained':len(word)==2,'future_arrivals_not_discarded':True,'scalar_bits':bits}

    def field_density_column(self,row,column,bra_word,ket_word,observation,*,bits=160):
        _require(type(row) is int and type(column) is int and 0<=row<joint.DIMENSION and 0<=column<joint.DIMENSION,'original full33 pair matrix-unit column required')
        bra=RetardedReceiptSource.field_amplitude(self,bra_word,observation,bits=bits)
        ket=RetardedReceiptSource.field_amplitude(self,ket_word,observation,bits=bits)
        a,b=_matrix(bra['full_pair_operator']),_matrix(ket['full_pair_operator'])
        matrix=dipole.matrix_product(dipole.matrix_product(a,{(row,column):dipole.ComplexRadical(1)}),dipole.matrix_adjoint(b))
        ea,eb=Q(bra['operator_error_upper']),Q(ket['operator_error_upper'])
        error=ea*bsm._entry_norm(b,bits=bits)+eb*bsm._entry_norm(a,bits=bits)+ea*eb
        return {'source_record':RetardedReceiptSource.record(self),'matrix_unit':[row,column],
            'physical_observation_seconds':str(observation),'bra_photon_word':_copy(bra_word),'ket_photon_word':_copy(ket_word),
            'complete_matter_field_kernel':channel._input_record(matrix),'trace_norm_kernel_error':str(error),
            'off_diagonal_photon_time_and_number_retained':True,'scalar_bits':bits}

    def field_trace_metric(self,bra_word,ket_word):
        """Metric of the ordered symmetric-coordinate field trace measure."""
        record=RetardedReceiptSource.record(self)
        _require(type(bra_word) is list and type(ket_word) is list and len(bra_word)<=2 and len(ket_word)<=2,
                 'original zero/one/two field coordinates required')
        if len(bra_word)!=len(ket_word):
            return ZERO
        value=dipole.ComplexRadical(1)
        loss=tuple(tuple(channel._complex_record(v) for v in row) for row in record['loss_environment_gram'])
        for a,b in zip(bra_word,ket_word):
            for e in (a,b):
                _require(type(e) is dict and set(e)=={'group','mode','arrival_seconds'} and tuple(e['group']) in self._field._groups,
                         'source resolved field coordinate required')
                mode=e['mode']
                _require(type(mode) is list and len(mode)==2 and mode[0] in ('port','loss') and type(mode[1]) is int and
                         0<=mode[1]<(4 if mode[0]=='port' else 6),'source field environment coordinate required')
                full.nonnegative(e['arrival_seconds'])
            if a['group']!=b['group'] or Q(a['arrival_seconds'])!=Q(b['arrival_seconds']) or a['mode'][0]!=b['mode'][0]:
                return ZERO
            p,q=a['mode'][1],b['mode'][1]
            value*=dipole.ComplexRadical(int(p==q)) if a['mode'][0]=='port' else loss[q][p]
        return value

    def receipt_field_column(self,row,column,bra_word,ket_word,observation,*,completing_signal=None,bits=160):
        """First-receipt coimage kernel, including its unmeasured future field."""
        record=RetardedReceiptSource.record(self);g0,g1=map(Q,record['gate_seconds']);time=full.exact(observation)
        _require(g0<=time<=g1,'receipt outside the original physical gate')
        def observed(word):
            return sorted((Q(e['arrival_seconds'])-g0,e['mode'][1],tuple(e['group'])) for e in word if e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<time)
        _require(observed(bra_word)==observed(ket_word),'measured past photon coordinates must match on both field legs')
        past=len(observed(bra_word))
        if completing_signal is not None:
            def completing(word):
                return [e for e in word if e['mode']==['port',completing_signal] and Q(e['arrival_seconds'])==time]
            _require(len(completing(bra_word))==len(completing(ket_word))==1,
                     'completing signal must be the same source-born photon coordinate on both field legs')
            _require(completing(bra_word)[0]['group']==completing(ket_word)[0]['group'],
                     'the consumed resolved photon group must match before its environment is traced')
            past+=1
        else:
            _require(not any(e['mode'][0]=='port' and Q(e['arrival_seconds'])==time for e in [*bra_word,*ket_word]),
                     'a simultaneous signal coordinate needs its original signal completion event')
        path=PortBackgroundLaw.path(self._bg,[[str(t),p] for t,p,g in observed(bra_word)],time-g0,
                                     receipt_port=completing_signal,bits=bits)
        kernel=RetardedReceiptSource.field_density_column(self,row,column,bra_word,ket_word,time,bits=bits)
        raw=_matrix(kernel['complete_matter_field_kernel']);factor=_measurement_factor(len(bra_word),len(ket_word),past)
        raw={key:factor*v for key,v in raw.items()}
        norm=bsm._entry_norm(raw,bits=bits);price=Q(kernel['trace_norm_kernel_error'])*bsm._entry_norm({(0,0):factor},bits=bits)
        matrices=[];local_price=Q(0)
        for h,value,error in path['receipt_weights']:
            value,error=Q(value),Q(error)
            matrices.append(channel._input_record({key:value*v for key,v in raw.items() if value*v}))
            local_price+=(abs(value)+error)*price+error*norm
        return {'schema':SCHEMA+'/receipt-field-kernel','source_record':record,'matrix_unit':[row,column],
            'physical_receipt_seconds':str(time),'bra_photon_word':_copy(bra_word),'ket_photon_word':_copy(ket_word),
            'four_pattern_matter_field_kernels':matrices,'whole_four_pattern_error':str(local_price),
            'source_BG_path':path,'first_receipt_is_BG_rate_density':completing_signal is None,
            'observed_resolved_group_environment_traced':True,'consumed_signal_photons':past,
            'remaining_bra_field':[e for e in bra_word if not (e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<=time)],
            'remaining_ket_field':[e for e in ket_word if not (e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<=time)],
            'in_flight_lost_and_off_diagonal_future_field_retained':True,'scalar_bits':bits}

    def failure_field_column(self,row,column,bra_word,ket_word,*,bits=160):
        record=RetardedReceiptSource.record(self);g0,g1=map(Q,record['gate_seconds'])
        def observed(word):
            return sorted((Q(e['arrival_seconds'])-g0,e['mode'][1],tuple(e['group'])) for e in word if e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<=g1)
        _require(observed(bra_word)==observed(ket_word),'gate-observed photon words must match on both field legs')
        path=PortBackgroundLaw.path(self._bg,[[str(t),p] for t,p,g in observed(bra_word)],g1-g0,bits=bits)
        weight=_sum_scalar([(Q(v),Q(e)) for _,v,e in path['pending_presence_weights']])
        kernel=RetardedReceiptSource.field_density_column(self,row,column,bra_word,ket_word,g1,bits=bits)
        factor=_measurement_factor(len(bra_word),len(ket_word),len(observed(bra_word)))
        matrix={key:factor*v for key,v in _matrix(kernel['complete_matter_field_kernel']).items()}
        price=Q(kernel['trace_norm_kernel_error'])*bsm._entry_norm({(0,0):factor},bits=bits)
        return {'schema':SCHEMA+'/gate-end-failure-field-kernel','source_record':record,'matrix_unit':[row,column],
            'gate_end_seconds':str(g1),'bra_photon_word':_copy(bra_word),'ket_photon_word':_copy(ket_word),
            'complete_failure_matter_field_kernel':channel._input_record({key:weight[0]*v for key,v in matrix.items() if weight[0]*v}),
            'trace_norm_kernel_error':str((abs(weight[0])+weight[1])*price+weight[1]*bsm._entry_norm(matrix,bits=bits)),
            'source_BG_path':path,'retained_field_not_replaced_by_atom_shadow':True,'scalar_bits':bits}

    def _atomic_marginal(self,matrix,observation,bits):
        record=RetardedReceiptSource.record(self);time=full.nonnegative(observation)
        matrix=dict(matrix);error=Q(0)
        for side in (0,1):
            origin=Q(record['complete_field_source']['raw_emission_origin_seconds'][side])
            _require(time>=origin,'field marginal precedes a source endpoint')
            vacuum=prepared.FieldOffPhotonKernel.no_emission_operator(self._field,side,time,bits=bits)
            operator=_matrix(vacuum['full33_vacuum_operator'],full.DIMENSION)
            radius=Q(vacuum['operator_norm_error_upper'])
            norm=bsm._entry_norm(matrix,bits=bits)
            result=joint._operator_right(joint._operator_left(matrix,side,operator),side,dipole.matrix_adjoint(operator))
            local_error=(2+radius)*radius*norm
            for group,info in self._field._groups.items():
                survival=scalar._exp_negative(info['gamma']*(time-origin),bits)
                mass=scalar._difference((Q(1),Q(0)),survival)
                for q in dipole.Q_COMPONENTS:
                    jump={(a,b):v for (component,a,b),v in info['operators'].items() if component==q}
                    image=joint._operator_right(joint._operator_left(matrix,side,jump),side,dipole.matrix_adjoint(jump))
                    _add(result,image,mass[0]);local_error+=mass[1]*bsm._entry_norm(image,bits=bits)
            matrix=result;error+=local_error
        return {'source_record':record,'physical_observation_seconds':str(time),
            'complete_atomic_field_trace_column':channel._input_record(matrix),'trace_norm_error':str(error),
            'all_zero_one_two_and_loss_field_sectors_traced':True,'scalar_bits':bits}

    def atomic_marginal_column(self,row,column,observation,*,bits=160):
        """Trace the source field, including every loss/in-flight sector."""
        _require(type(row) is int and type(column) is int and 0<=row<joint.DIMENSION and 0<=column<joint.DIMENSION,
                 'original complex-linear full33 matrix-unit column required')
        report=RetardedReceiptSource._atomic_marginal(self,{(row,column):dipole.ComplexRadical(1)},observation,bits)
        report['matrix_unit']=[row,column]
        return report

    def ground_BG_column(self,index,left=None,right=None,*,bits=160):
        """Exact BG receipt/failure action on a generated no-photon basis column."""
        record=RetardedReceiptSource.record(self)
        _require(type(index) is int and 0<=index<joint.DIMENSION and
                 all(dipole.STATES[i].family in ('ground','ion') for i in divmod(index,full.DIMENSION)),
                 'original ground/ion vacuum column required; excited photons cannot be deleted')
        a,z=map(Q,record['gate_seconds']);left=a if left is None else full.exact(left);right=z if right is None else full.exact(right)
        report=PortBackgroundLaw.interval(self._bg,left-a,right-a,duration=z-a,bits=bits)
        atom={(index,index):dipole.ComplexRadical(1)}
        success=[channel._input_record({key:Q(row['centre'])*v for key,v in atom.items() if Q(row['centre'])*v})
                 for row in report['four_first_receipt_masses']]
        failure=Q(report['gate_end_failure_mass']['centre'])
        error=sum((Q(row['error']) for row in report['four_first_receipt_masses']),Q(report['gate_end_failure_mass']['error']))
        return {'schema':SCHEMA+'/ground-BG-whole-instrument-column','source_record':record,'matrix_unit':[index,index],
            'restriction_seconds':[str(left),str(right)],'four_pattern_poststates':success,
            'gate_end_failure_poststate':channel._input_record({key:failure*v for key,v in atom.items() if failure*v}),
            'global_trace_norm_error':str(error),'source_BG_first_receipt_report':report,
            'retained_field_sector':{'photon_number':0},'initial_source_column_trace':str(1),
            'native_rolling_queue_reconstructed_or_reset':False,'scalar_bits':bits}

    def one_photon_BG_column(self,index,*,bits=160):
        """Whole original signal+BG instrument on a one-excitation basis column."""
        record=RetardedReceiptSource.record(self);g0,g1=map(Q,record['gate_seconds']);duration=g1-g0
        raw=record['complete_field_source']
        _require(tuple(map(Q,raw['raw_emission_origin_seconds']))==(g0,g0) and not any(map(Q,raw['raw_flight_seconds'])),
                 'this exact finite exponential readout requires zero flights and the original gate-aligned source endpoints')
        _require(type(index) is int and 0<=index<joint.DIMENSION,'original full-pair basis column required')
        indices=divmod(index,full.DIMENSION)
        excited=[side for side,i in enumerate(indices) if dipole.STATES[i].family in ('D1','D2')]
        _require(len(excited)==1 and dipole.STATES[indices[1-excited[0]]].family in ('ground','ion'),
                 'one source photon and one original ground/ion leg required; two photons require their Bose field')
        side=excited[0];initial={(index,index):dipole.ComplexRadical(1)}
        atom=joint._source(full.Segment.from_record(raw['source_atoms'][side]))
        unit=Q(raw['common_atomic_programme']['atomic_base']['seconds_per_unit'])
        gamma=atom.outgoing[indices[side]]/unit
        survival=scalar._exp_negative(gamma*duration,bits);emission=scalar._difference((Q(1),Q(0)),survival)
        bg=PortBackgroundLaw.interval(self._bg,0,duration,duration=duration,bits=bits)
        bg_weights=[(Q(r['centre']),Q(r['error'])) for r in bg['four_first_receipt_masses']]
        bg_weights.append((Q(bg['gate_end_failure_mass']['centre']),Q(bg['gate_end_failure_mass']['error'])))
        matrices=[{} for _ in range(5)];error=Q(0)
        for output,(weight,radius) in zip(matrices,bg_weights):
            value,price=scalar._product(survival,(weight,radius))
            _add(output,initial,value);error+=price
        signal_weights={p:PortBackgroundLaw._one_signal_integral(self._bg,p,gamma,duration,bits) for p in range(4)}
        for group,info in self._field._groups.items():
            original={};ports=[]
            for q in dipole.Q_COMPONENTS:
                jump={(a,b):v for (component,a,b),v in info['operators'].items() if component==q}
                image=joint._operator_right(joint._operator_left(initial,side,jump),side,dipole.matrix_adjoint(jump))
                _add(original,image)
            if not original:
                continue
            for port in range(4):
                jump=self._field._operations[group,side,port]
                image=joint._operator_right(joint._operator_left(initial,side,jump),side,dipole.matrix_adjoint(jump))
                ports.append(image)
                norm=bsm._entry_norm(image,bits=bits)
                for output,(weight,radius) in zip(matrices,signal_weights[port]):
                    _add(output,image,weight);error+=radius*norm
            lost=dict(original)
            for image in ports:
                _add(lost,image,-1)
            norm=bsm._entry_norm(lost,bits=bits)
            for output,weight in zip(matrices,bg_weights):
                value,price=scalar._product(emission,weight)
                _add(output,lost,value);error+=price*norm
        return {'schema':SCHEMA+'/one-photon-BG-whole-instrument-column','source_record':record,'matrix_unit':[index,index],
            'four_pattern_poststates':[channel._input_record(m) for m in matrices[:4]],
            'gate_end_failure_poststate':channel._input_record(matrices[4]),'global_trace_norm_error':str(error),
            'source_BG_first_receipt_report':bg,'source_signal_mark_clock_weights':[[p,[[str(v),str(e)] for v,e in signal_weights[p]]] for p in range(4)],
            'source_emission_decay_per_second':str(gamma),'integrated_matter_reference_seconds':str(g1),
            'first_receipt_time_and_remaining_field':{'source_record':record,'kernel':'receipt_field_column'},
            'ground_phase_for_BG_mixed_input_assumed':False,'loss_source_Gram_consumed':True,
            'positive_physical_input_from_this_column_readout':False,'old_input_error':'0','scalar_bits':bits}

    def verify_one_photon_BG_column(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/one-photon-BG-whole-instrument-column' and
                 report['source_record']==RetardedReceiptSource.record(self),'same one-photon/full-BG source column required')
        i,j=report['matrix_unit'];_require(i==j,'one original basis column required')
        _require(RetardedReceiptSource.one_photon_BG_column(self,i,bits=report['scalar_bits'])==report,
                 'one-photon CP flux, failure, quantum coimage or full BG price changed')
        return True

    def signal_reference_law(self):
        record=RetardedReceiptSource.record(self);raw=record['complete_field_source']
        unit=Q(raw['common_atomic_programme']['atomic_base']['seconds_per_unit'])
        atoms=tuple(joint._source(full.Segment.from_record(r)) for r in raw['source_atoms'])
        checks=[]
        for group,info in self._field._groups.items():
            for side,atom in enumerate(atoms):
                for (q,target,origin),value in info['operators'].items():
                    if value:
                        energy=atom.hamiltonian.get((target,target),ZERO).real.as_rational()/unit
                        _require(energy==info['ground_energy'],'original ground output range has no common source energy')
            checks.append({'group':list(group),'ground_energy_per_second':str(info['ground_energy'])})
        return {'source_record':record,'source_ground_ranges':checks,
            'pair_range_identity':'both Bose assignments for (g,h) have the same total ground energy Eg+Eh',
            'signal_poststate_commutes_with_common_ground_Hamiltonian':True,
            'receipt_state_can_be_read_at_gate_end_without_a_fake_clock':True,
            'BG_mixed_state_uses_this_identity':False}

    def _coupled(self,matrix,left,right,bits):
        record=RetardedReceiptSource.record(self);g0,g1=map(Q,record['gate_seconds'])
        left=g0 if left is None else full.exact(left);right=g1 if right is None else full.exact(right)
        _require(g0<=left<=right<=g1,'whole receipt query retains original gate origin')
        reference=RetardedReceiptSource.signal_reference_law(self)
        signal=prepared.FieldOffPhotonKernel._instrument(self._field,matrix,left,right,g0,g1,bits,0)
        whole=prepared.FieldOffPhotonKernel._instrument(self._field,matrix,g0,g1,g0,g1,bits,0)
        total=RetardedReceiptSource._atomic_marginal(self,matrix,g1,bits)
        entry_norm=bsm._entry_norm(matrix,bits=bits)
        matrix=_matrix(total['complete_atomic_field_trace_column'])
        for poststate in whole['four_pattern_poststates']:
            _add(matrix,_matrix(poststate),-1)
        rates=tuple(map(Q,record['BG_source']['BG_rates_per_second']))
        survival=_probability(*scalar._exp_negative(sum(rates,Q(0))*(g1-g0),bits),bits)
        p0,p0_error=survival;remainder=min(Q(1),1-p0+p0_error)
        centres=[_matrix(r) for r in signal['four_pattern_poststates']]
        magnitude=sum((bsm._entry_norm(c,bits=bits) for c in centres),bsm._entry_norm(matrix,bits=bits))
        local_error=Q(signal['global_trace_norm_error'])+Q(whole['global_trace_norm_error'])+Q(total['trace_norm_error'])
        numerical=(p0+p0_error)*local_error+p0_error*magnitude
        coupling=2*remainder*entry_norm
        return {'schema':SCHEMA+'/whole-receipt-failure-enclosure','source_record':record,
            'restriction_seconds':[str(left),str(right)],'scalar_bits':bits,
            'four_pattern_poststates':[channel._input_record({key:p0*v for key,v in c.items() if p0*v}) for c in centres],
            'gate_end_failure_poststate':channel._input_record({key:p0*v for key,v in matrix.items() if p0*v}),
            'no_BG_through_gate_end_probability':str(p0),'no_BG_probability_error':str(p0_error),
            'any_BG_path_probability_upper':str(remainder),'source_coupling_trace_norm_upper':str(coupling),
            'input_centre_trace_norm_upper':str(entry_norm),
            'new_local_source_error':str(numerical),'global_trace_norm_error':str(numerical+coupling),
            'complete_field_reference_law':reference,
            'omitted_positive_CP_subinstrument':'all original field+BG histories with at least one in-gate BG event',
            'complete_mother_readers':['field_amplitude','field_density_column','receipt_field_column','failure_field_column'],
            'enclosed_readout':'four time-integrated matter poststates at gate end and the gate-end atomic failure restriction',
            'complete_retained_field_mother':{'source_record':record,'receipt_density_reader':'receipt_field_column',
                'failure_density_reader':'failure_field_column','ordered_field_trace_metric':'field_trace_metric'},
            'no_BG_through_end_is_only_a_subinstrument':True,'no_BG_until_receipt_weight_replaced_by_gate_end':False,
            'BG_mixed_ground_identity_assumed':False,'whole_native_history_or_arrival_queue_discarded':False,
            'integrated_matter_reference_seconds':str(g1),
            'receipt_time_field_law_retained_in_full_mother':True,
            'actual_hardware_uniquely_identified':False,'controller_advance':False}

    def coupled_column(self,row,column,left=None,right=None,*,bits=160):
        """Uniform complex-linear readout; no physical input state is asserted."""
        _require(type(row) is int and type(column) is int and 0<=row<joint.DIMENSION and 0<=column<joint.DIMENSION,
                 'original full-pair matrix-unit column required')
        report=RetardedReceiptSource._coupled(self,{(row,column):dipole.ComplexRadical(1)},left,right,bits)
        report['matrix_unit']=[row,column]
        report['positive_physical_input_from_this_column_readout']=False
        return report

    @classmethod
    def from_prepared(cls,source):
        _require(cls is RetardedReceiptSource and type(source) is prepared.PreparedRetardedSource,
                 'closed source-born prepared endpoint required; a target state is not input')
        raw=prepared.PreparedRetardedSource.record(source)
        if raw['common_optical_owner_record'] is not None:
            common=optical.CommonOpticalReadout.from_record(raw['common_optical_owner_record'])
        else:
            field=raw['field_kernel']
            decode=lambda rows:tuple(tuple(channel._complex_record(v) for v in row) for row in rows)
            common=optical.CommonOpticalReadout(
                prepared.atomic.MunichAtomicProgramme.from_record(raw['common_atomic_programme']),
                collection_a=decode(field['raw_collection'][0]),collection_b=decode(field['raw_collection'][1]),
                splitter=decode(field['raw_splitter']),efficiencies=tuple(field['raw_efficiencies']),
                background_rates=tuple(raw['raw_shared_four_port_background_rates']))
        result=cls(common,prepared.FieldOffPhotonKernel.from_record(raw['field_kernel']))
        _require(result.record()['BG_source']['raw_rates_per_source_unit']==raw['raw_shared_four_port_background_rates'],
                 'the source-born native endpoint and first receipt have different BG clocks')
        return result

    def coupled_prepared(self,source,left=None,right=None,*,bits=160):
        """The complete CP mother consumes only its certified prepared coimage."""
        _require(type(source) is prepared.PreparedRetardedSource,'closed source-born prepared endpoint required')
        parent=prepared.PreparedRetardedSource.record(source);record=RetardedReceiptSource.record(self)
        _require(parent['field_kernel']==record['complete_field_source'] and
                 parent['raw_shared_four_port_background_rates']==record['BG_source']['raw_rates_per_source_unit'] and
                 (parent['common_optical_owner_record'] is None or parent['common_optical_owner_record']==record['BG_source']['common_optical_source']),
                 'same prepared field/native/optical mother required')
        matrix=_matrix(parent['source_generated_full_pair_endpoint'])
        report=RetardedReceiptSource._coupled(self,matrix,left,right,bits)
        old=Q(parent['upstream_trace_norm_error']);mass_upper=Q(parent['source_ready_positive_mass_upper'])
        remainder=Q(report['any_BG_path_probability_upper'])
        report.update({'schema':SCHEMA+'/source-born-whole-receipt-failure-enclosure',
            'source_preparation_record':parent,'upstream_trace_norm_error':str(old),
            'source_positive_input_mass_upper':str(mass_upper),
            'source_positive_BG_remainder_mass_upper':str(mass_upper*remainder),
            'global_trace_norm_error':str(old+Q(report['new_local_source_error'])+Q(report['source_coupling_trace_norm_upper'])),
            'old_error_consumed_once_by_whole_CP_instrument':True,
            'source_positive_input_is_not_the_numerical_centre':True,
            'parameter_domain':_copy(parent['parameter_domain']),'source_support_word':_copy(parent['source_support_word']),
            'complete_native_time_state_mother':_copy(parent['native_time_state_mother']),
            'native_ready_relative_time_recipe':_copy(parent['native_ready_relative_time_recipe']),
            'complete_receipt_time_field_recipe':{'full_source_record':record,
                'source_generated_endpoint':parent['source_generated_full_pair_endpoint'],
                'input_old_error':str(old),'receipt_kernel_readout':'receipt_field_column',
                'failure_kernel_readout':'failure_field_column','field_trace_metric':'field_trace_metric'},
            'positive_physical_input_from_source_parent':True})
        return report

    def verify_prepared(self,source,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/source-born-whole-receipt-failure-enclosure',
                 'source-born complete receipt/failure report required')
        a,z=report['restriction_seconds']
        _require(RetardedReceiptSource.coupled_prepared(self,source,a,z,bits=report['scalar_bits'])==report,
                 'prepared coimage, full mother, source time law or old/local/BG price changed')
        return True

    def verify_coupled_column(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/whole-receipt-failure-enclosure' and
                 report['source_record']==RetardedReceiptSource.record(self),'same full field/BG source column required')
        row,column=report['matrix_unit'];a,z=report['restriction_seconds']
        _require(RetardedReceiptSource.coupled_column(self,row,column,a,z,bits=report['scalar_bits'])==report,
                 'whole receipt/failure column, source, interval or coupling price changed')
        return True


def _falling(n,k):
    result=1
    for i in range(k):
        result*=n-i
    return result


def _measurement_factor(bra_count,ket_count,observed_count):
    _require(0<=observed_count<=min(bra_count,ket_count)<=2,'observed source photon count exceeds its field sector')
    return dipole.ComplexRadical(dipole.sqrt_rational(_falling(bra_count,observed_count)*_falling(ket_count,observed_count)))


def _signature():
    functions=(_require,_copy,_digest,_bindings,_matrix,_subsets,_mask,_mark,_sum_scalar,_probability,_exp_integral,_emission_BG_integral,_tensor,_add,_falling,_measurement_factor,_signature,_guard,
        bsm.Mark.__init__,bsm.Mark.__post_init__,bsm.BSMSource.target,optical.CommonOpticalReadout.record,
        optical.CommonOpticalReadout.bsm_gate,scalar._exp_negative,scalar._product,scalar._interval,joint.passive_transfer,
        dipole.matrix_product,dipole.matrix_adjoint,dipole.sqrt_rational,
        channel._read_input,channel._input_record,channel._complex_record,bsm._entry_norm,
        joint._operator_left,joint._operator_right,joint._matrix,local._matrix,local._add,
        full.nonnegative,full.exact,scalar._difference)
    classes=(PortBackgroundLaw,RetardedReceiptSource)
    methods=tuple((id(getattr(f,'__func__',f)),id(getattr(getattr(f,'__func__',f),'__code__',None)))
                  for c in classes for f in vars(c).values() if callable(f) or isinstance(f,(classmethod,staticmethod)))
    return (tuple((id(f),id(f.__code__)) for f in functions),methods,tuple(bsm.PATTERNS),tuple(bsm.PORTS),tuple(dipole.STATES),
            tuple(dipole.INDEX.items()),tuple(dipole.Q_COMPONENTS),full.DIMENSION,joint.DIMENSION,
            (bsm.INITIAL.counts,bsm.INITIAL.receipt),SCHEMA)


def _guard():
    if not (_signature is _SIGNATURE and _signature.__code__ is _SIGNATURE_CODE and _signature()==_EXPECTED):
        raise ValueError('retarded receipt source execution closure changed')


_GUARD,_GUARD_CODE=_guard,_guard.__code__
_SIGNATURE,_SIGNATURE_CODE=_signature,_signature.__code__
_EXPECTED=_signature()

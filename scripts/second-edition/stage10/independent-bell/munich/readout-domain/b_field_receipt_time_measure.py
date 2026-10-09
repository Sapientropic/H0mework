"""Both Bose assignments generate one first-receipt CP time measure.

The two arrival coordinates share the receipt matter clock.  The complete
field/BG mother remains attached.  No-background-through-gate two-signal
receipts form a positive subinstrument, independently of its complement.
"""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import hashlib
import json

import b_field_photon_source as photons
import source_mode_time_measure as temporal
import apd_window_history as apd
import radical_time_accumulator as integer_time

SCHEMA='stage10-B-field-two-signal-first-receipt-time-measure/v1'
C=photons.dipole.ComplexRadical
ZERO=C()
_ISSUED=set()
_REPORTS=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return photons._copy(value)


def _digest(value):
    return photons._digest(value)


def _bindings():
    paths=(Path(__file__),*(Path(m.__file__) for m in (photons,temporal,apd,integer_time)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _add(matrix,other,factor=1):
    photons._add(matrix,other,factor)


def _conjugate(value):
    return value[0],-value[1]


def _sum(a,b):
    return a[0]+b[0],a[1]+b[1]


def _difference(a,b):
    return a[0]-b[0],a[1]-b[1]


def _curve_modes(curve):
    _require(curve['sector']=='all' and len(curve['pieces'])==1 and
             curve['pieces'][0]['source_interval_seconds'][0]=='0',
             'complete one-piece source mode operator is required')
    ground=[];excited=[]
    for term in curve['pieces'][0]['complete_physical_operator_terms']:
        _require(term['constant_source_phase_angle_radians']=='0' and
                 len(term['normalized_polynomial_coefficients'])==1,
                 'this first-receipt integral consumes constant source modes')
        quantum=1<<term['mode_bits'];exponent=tuple(map(Q,term['lambda_per_second']))
        matrix={(i,j):C(Q(a,quantum),Q(b,quantum))
                for i,j,a,b in term['normalized_polynomial_coefficients'][0]}
        g={key:v for key,v in matrix.items() if all(photons.dipole.STATES[i].family=='ground' for i in key)}
        e={key:v for key,v in matrix.items() if all(photons.dipole.STATES[i].family in ('D1','D2') for i in key)}
        if g: ground.append((exponent,g))
        if e: excited.append((exponent,e))
    return ground,excited


@lru_cache(maxsize=8192)
def _prefactor(ge,ee,ground_age,excited_age,bits):
    _require(ground_age>=0 and excited_age>=0,'source photons cannot precede either physical evolution leg')
    return temporal._exp(ge,ground_age,bits).multiply(temporal._exp(ee,excited_age,bits)).rounded(bits)


@lru_cache(maxsize=8192)
def _ordered_triangle(first,second,x0,t0,stop,bits):
    """Existing moments pay the retained early-click rectangle and triangle."""
    if t0>=stop:
        return temporal.Enclosure((Q(0),Q(0)),Q(0))
    before=t0-x0;width=stop-t0
    rectangle=temporal.exponential_moment(first,0,0,before,bits=bits).multiply(
        temporal.exponential_moment(second,0,0,width,bits=bits))
    triangle=temporal._exp(first,before,bits).multiply(
        temporal.exponential_triangle(first,second,0,width,inner_start=0,bits=bits))
    return rectangle.add(triangle).rounded(bits)


def _leg_vectors(ground,excited,jump,column):
    combined={}
    for ge,gm in ground:
        for ee,em in excited:
            if column is not None and not any(j==column for i,j in em):
                continue
            operator=photons.dipole.matrix_product(photons.dipole.matrix_product(gm,jump),em)
            vector=operator if column is None else {(i,0):v for (i,j),v in operator.items() if j==column}
            if vector:
                key=(ge,ee);_add(combined.setdefault(key,{}),vector)
    return [(ge,ee,vector) for (ge,ee),vector in combined.items() if vector]


def _late_vectors(vectors,flight,bits):
    """The late ground clock is exactly its fixed physical flight."""
    combined={};price=Q(0)
    for ge,ee,vector in vectors:
        phase=temporal._exp(ge,flight,bits)
        _add(combined.setdefault(ee,{}),vector,C(*phase.centre))
        # The mode checker bounds positive real growth through the entire
        # source curve by exp(1/2)<2.  Excited ages never exceed that curve.
        growth=Q(1) if ee[0]<=0 else Q(2)
        price+=growth*phase.error*photons.bsm._entry_norm(vector,bits=bits)
    return [((Q(0),Q(0)),ee,vector) for ee,vector in combined.items() if vector],price


def _branch_terms(vectors,early_side,*,tensor_input=False):
    result=[]
    for ge,ee,early in vectors[early_side]:
        for gl,el,late in vectors[1-early_side]:
            operators=(early,late) if early_side==0 else (late,early)
            pair=operators if tensor_input else photons.receipt._tensor(*operators)
            if pair:
                result.append((_difference(ee,ge),_sum(ge,el),ge,ee,gl,el,pair))
    return result


def _branch_factor(term,early_side,x0,t0,raw,bits):
    _,_,ge,ee,gl,el,_=term
    late_side=1-early_side
    flight=Q(raw['flight_seconds'][early_side]);late_flight=Q(raw['flight_seconds'][late_side])
    early_origin=Q(raw['source_arrival_origins_seconds'][early_side])
    late_origin=Q(raw['source_arrival_origins_seconds'][late_side])
    early=_prefactor(ge,ee,t0-x0+flight,x0-early_origin,bits)
    late=_prefactor(gl,el,late_flight,t0-late_origin,bits)
    return early.multiply(late).rounded(bits)


def _image(first,second):
    return photons.dipole.matrix_product(first,photons.dipole.matrix_adjoint(second))


def _normal_errors(jump,jump_error,uniform,bits):
    norm=photons._operator_bound(jump,bits)
    centre=(1+uniform)**2*norm
    price=(1+uniform)**2*(norm+jump_error)-norm
    return centre,price


class BFieldReceiptTimeMeasure:
    def __init__(self,source,certificates):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('joint B-field time measure execution changed')
        _CHECK()
        _require(type(source) is photons.BFieldPhotonSource and type(certificates) in (tuple,list) and len(certificates)==2,
                 'closed same-source two-leg photon curves required; a target state or q table is not input')
        raw=photons.BFieldPhotonSource.record(source)
        measures=tuple(temporal.PhotonTimeMeasure(source,side,certificates[side]) for side in (0,1))
        curves=tuple(temporal.PhotonTimeMeasure.record(m)['source_curve'] for m in measures)
        gate=tuple(map(Q,raw['gate_seconds']))
        _require(all(Q(curve['duration_seconds'])>=gate[1]-Q(raw['emission_origin_seconds'][side])
                     for side,curve in enumerate(curves)),
                 'every original curve must cover the receipt matter clock through gate end')
        self._source,self._measures,self._curves=source,measures,curves
        self._modes=tuple(_curve_modes(curve) for curve in curves)
        self._value={'schema':SCHEMA,'complete_two_arm_field_mother':raw,
            'complete_source_certificates':_copy(certificates),'source_curves':_copy(curves),
            'source_bindings':_bindings(),'receipt_law':'two source Bose assignments on the same chronological arrival triangle',
            'subinstrument':'two detected signal photons with no BG anywhere in the original gate',
            'B0_stationarity_used':False,'quantum_input_state_supplied':False,'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED.add(self._seal)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('joint B-field time measure execution changed')
        _CHECK();photons._closed(self)
        _require(type(self) is BFieldReceiptTimeMeasure and set(vars(self))=={'_source','_measures','_curves','_modes','_value','_seal'} and
            self._seal in _ISSUED and _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            photons.BFieldPhotonSource.record(self._source)==self._value['complete_two_arm_field_mother'] and
            _copy(self._curves)==self._value['source_curves'] and
            tuple(_curve_modes(curve) for curve in self._curves)==self._modes and
            all(temporal.PhotonTimeMeasure.record(m)['source_curve']==curve for m,curve in zip(self._measures,self._curves)),
            'joint first-receipt source, two clocks, complete curves or whole field mother changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls,record):
        _require(cls is BFieldReceiptTimeMeasure and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed source-issued joint time measure required')
        source=photons.BFieldPhotonSource.from_record(record['complete_two_arm_field_mother'])
        result=cls(source,record['complete_source_certificates'])
        _require(BFieldReceiptTimeMeasure.record(result)==record,'original joint source/time measure identity changed')
        return result

    def interval_column(self,row,column,start,stop,*,patterns=None,bits=192):
        _require(type(row) is int and type(column) is int and 0<=row<photons.joint.DIMENSION and 0<=column<photons.joint.DIMENSION,
                 'complete original pair matrix-unit column and scalar precision required')
        return BFieldReceiptTimeMeasure._interval(self,start,stop,patterns=patterns,bits=bits,
            coordinates=(divmod(row,33),divmod(column,33)),source_matrix_unit=[row,column])

    def interval_prepared(self,source,start,stop,*,patterns=None,bits=192):
        import prepared_b_field_receipt as prepared
        _require(type(source) is prepared.PreparedBFieldReceipt,'closed source-issued reference tensor coimage required')
        inlet=prepared.PreparedBFieldReceipt.source_tensors(source)
        _require(inlet['source_record']['reference_joint_instrument']['centre_joint_source']==BFieldReceiptTimeMeasure.record(self),
                 'prepared tensors and original photon time instrument must have the same source')
        return BFieldReceiptTimeMeasure._interval(self,start,stop,patterns=patterns,bits=bits,
            coordinates=((None,None),(None,None)),source_matrix_unit=None,inlet=inlet)

    def _interval(self,start,stop,*,patterns,bits,coordinates,source_matrix_unit,inlet=None):
        record=BFieldReceiptTimeMeasure.record(self);raw=record['complete_two_arm_field_mother']
        _require(type(bits) is int and 64<=bits<=512,'complete original pair matrix-unit column and scalar precision required')
        g0,g1=map(Q,raw['gate_seconds']);left,right=map(photons.full.nonnegative,(start,stop))
        _require(g0<=left<=right<=g1,'first-receipt restriction must retain its whole original gate')
        patterns=tuple(range(4)) if patterns is None else tuple(patterns)
        _require(patterns and len(set(patterns))==len(patterns) and all(type(p) is int and 0<=p<4 for p in patterns),
                 'explicit original source pattern addresses required')
        arrivals=tuple(map(Q,raw['source_arrival_origins_seconds']))
        results=[{} for _ in range(4)]
        tensor_input=inlet is not None
        source_norm=Q(1) if inlet is None else inlet['source_centre_trace_norm_upper']
        old=Q(0) if inlet is None else inlet['whole_upstream_trace_norm_error']
        uniform=[Q(curve['pieces'][0]['physical_uniform_operator_error_upper_with_exact_block_phases']) for curve in self._curves]
        zero=(left==right or right<=max(g0,*arrivals) or (not tensor_input and
              any(photons.dipole.STATES[i].family not in ('D1','D2') for pair in coordinates for i in pair)))
        groups=sorted({tuple(item['group']) for item in raw['physical_legs'][0]['original_physical_natural_jumps']})
        scalar_price=Q(0);source_price=Q(0);late_phase_price=Q(0);cross_records=[];compiled={};late_compiled={};jumps={}
        area=((right-g0)**2-(left-g0)**2)/2
        def get_jump(side,group,port):
            key=side,group,port
            if key not in jumps:
                jumps[key]=temporal.PhotonTimeMeasure._jump(self._measures[side],group,port,bits)
            return jumps[key]
        def vector(side,group,port,input_column):
            key=side,group,port,input_column
            if key not in compiled:
                compiled[key]=_leg_vectors(*self._modes[side],get_jump(side,group,port)[0],input_column)
            return compiled[key]
        def late_vector(side,group,port,input_column):
            key=side,group,port,input_column
            if key not in late_compiled:
                late_compiled[key]=_late_vectors(vector(*key),Q(raw['flight_seconds'][side]),bits)
            return late_compiled[key]
        if not zero:
            for pattern in patterns:
                ports=photons.bsm.PATTERNS[pattern][1]
                for p,q in (ports,ports[::-1]):
                    first=photons.receipt.PortBackgroundLaw.insertion(self._source._bg,0,p)
                    final=photons.receipt.PortBackgroundLaw.insertion(self._source._bg,first['presence'],q)
                    _require(first['receipt'] is None and final['receipt']==pattern,
                             'the original port Mark does not generate this first pattern')
                    for g in groups:
                        for h in groups:
                            branch_by_column=[]
                            for input_pair in coordinates:
                                branches=[]
                                for early_side in (0,1):
                                    vectors=[None,None]
                                    vectors[early_side]=vector(early_side,g,p,input_pair[early_side])
                                    vectors[1-early_side]=late_vector(1-early_side,h,q,input_pair[1-early_side])[0]
                                    branches.append(_branch_terms(vectors,early_side,tensor_input=tensor_input))
                                branch_by_column.append(branches)
                            norms=[];errors=[];phase_errors=[]
                            for early_side in (0,1):
                                a,ea=_normal_errors(*get_jump(early_side,g,p),uniform[early_side],bits)
                                b,eb=_normal_errors(*get_jump(1-early_side,h,q),uniform[1-early_side],bits)
                                norms.append(a*b);errors.append(ea*b+eb*a+ea*eb)
                                phase_errors.append(a*max(late_vector(1-early_side,h,q,pair[1-early_side])[1]
                                                          for pair in coordinates))
                            amplitude_norm=sum(norms,Q(0));amplitude_error=sum(errors,Q(0))
                            source_price+=source_norm*area*amplitude_error*(2*amplitude_norm+amplitude_error)
                            phase_error=sum(phase_errors,Q(0))
                            late_phase_price+=source_norm*area*phase_error*(2*amplitude_norm+phase_error)
                            if not any(branch_by_column[0]) or not any(branch_by_column[1]):
                                continue
                            count=0
                            for bra_side in (0,1):
                                for ket_side in (0,1):
                                    x0=max(g0,arrivals[bra_side],arrivals[ket_side])
                                    t0=max(left,x0,arrivals[1-bra_side],arrivals[1-ket_side])
                                    if t0>=right:
                                        continue
                                    bra_terms=branch_by_column[0][bra_side];ket_terms=branch_by_column[1][ket_side]
                                    if tensor_input:
                                        inventories=[[],[]];addresses=[{},{}];term_ids=[]
                                        for term in (*bra_terms,*ket_terms):
                                            ids=[]
                                            for side,operator in enumerate(term[6]):
                                                identity=tuple(sorted(operator.items()))
                                                if identity not in addresses[side]:
                                                    addresses[side][identity]=len(inventories[side])
                                                    inventories[side].append(operator)
                                                ids.append(addresses[side][identity])
                                            term_ids.append(tuple(ids))
                                        accumulation=integer_time.RadicalTensorTimeAccumulator(*inventories,
                                            inlet['tensor_terms'],dimension=33,scalar_bits=bits,norm_bits=bits)
                                    else:
                                        accumulation=integer_time.RadicalTimeAccumulator(
                                            [term[6] for term in (*bra_terms,*ket_terms)],scalar_bits=bits,norm_bits=bits)
                                    bra_factors=[_branch_factor(term,bra_side,x0,t0,raw,bits) for term in bra_terms]
                                    ket_factors=[_branch_factor(term,ket_side,x0,t0,raw,bits) for term in ket_terms]
                                    for bi,(bra,ab) in enumerate(zip(bra_terms,bra_factors)):
                                        for ki,(ket,ak) in enumerate(zip(ket_terms,ket_factors)):
                                            z=_sum(bra[0],_conjugate(ket[0]));w=_sum(bra[1],_conjugate(ket[1]))
                                            integral=_ordered_triangle(z,w,x0,t0,right,bits)
                                            factor=ab.multiply(temporal.Enclosure(_conjugate(ak.centre),ak.error)).multiply(integral).rounded(bits)
                                            if tensor_input:
                                                integer_time.RadicalTensorTimeAccumulator.add_tensor(accumulation,
                                                    term_ids[bi],term_ids[len(bra_terms)+ki],factor)
                                            else:
                                                integer_time.RadicalTimeAccumulator.add_outer(accumulation,bi,len(bra_terms)+ki,factor)
                                            count+=1
                                    image,price=integer_time.RadicalTimeAccumulator.result(accumulation)
                                    scalar_price+=price;_add(results[pattern],image)
                            if count:
                                cross_records.append({'pattern':pattern,'ordered_ports':[p,q],'early_group':list(g),
                                    'late_group':list(h),'complete_Bose_matrix_terms':count,
                                    'amplitude_source_error_upper':str(amplitude_error),
                                    'late_ground_scalar_amplitude_error_upper':str(phase_error)})
        contraction=Q(1) if inlet is None else inlet['whole_input_signal_contraction_upper']
        _require(0<=contraction<=1,'source-issued whole two-signal contraction required')
        old_payment=Q(0) if zero else old*contraction
        base_error=source_price+scalar_price+late_phase_price+old_payment
        rate=sum(map(Q,raw['source_BG_law']['BG_rates_per_second']),Q(0))
        p0=temporal._exp((-rate,Q(0)),g1-g0,bits)
        norm=sum((photons.bsm._entry_norm(matrix,bits=bits) for matrix in results),Q(0))
        report={'schema':SCHEMA+('/interval-prepared-CP' if tensor_input else '/interval-CP-column'),
            'source_record':record,'source_matrix_unit':source_matrix_unit,
            'first_receipt_restriction_seconds':[str(left),str(right)],'original_gate_seconds':[str(g0),str(g1)],
            'patterns':list(patterns),'four_pattern_poststates':[photons.channel._input_record({key:value*p0.centre[0]
                for key,value in matrix.items() if value*p0.centre[0]}) for matrix in results],
            'no_BG_signal_centre_probability':str(p0.centre[0]),'no_BG_signal_probability_error':str(p0.error),
            'uniform_source_curve_integration_error':str(source_price),'scalar_triangle_integration_error':str(scalar_price),
            'late_ground_scalar_integration_error':str(late_phase_price),
            'late_ground_modes_merged_before_Bose_cross':True,
            'whole_upstream_trace_norm_error_paid_once':str(old_payment),
            'whole_upstream_trace_norm_error_before_signal_contraction':str(old),
            'whole_input_signal_contraction_upper':str(contraction),
            'source_centre_trace_norm_upper':str(source_norm),
            'source_BG_scaling_error':str(p0.error*norm),
            'whole_trace_norm_error_upper':str(base_error+p0.error*norm),
            'complete_group_and_Bose_price_records':cross_records,'first_click_before_restriction_left_retained':True,
            'quantum_poststate_at_actual_receipt_time':True,'two_marginal_product_used_as_joint':False,
            'source_generated_exact_zero_two_signal_column':zero,'scalar_bits':bits,
            'complete_field_BG_positive_complement_mother':raw,
            'uncomputed_BG_and_zero_one_loss_branches_conditioned_away':False,
            'probability_scope':'positive two-signal/no-BG-through-whole-gate subinstrument; the full receipt complement remains in the source',
            'continuous_time_memory_recipe':{'latent_coordinates_seconds':['first_signal_arrival','first_receipt'],
                'domain':'gate_origin <= first <= receipt, receipt in original restriction; assignment source flight bounds retained',
                'clock_recipe':'elapse incoming same-source memory to first; append once; elapse to receipt; append once',
                'a_scalar_receipt_clock_selected':False},'controller_advance':False}
        if tensor_input:
            report['prepared_source_record']=inlet['source_record']
            report['whole_native_time_and_PC_mother']=inlet['time_state_mother']
            report['signed_tensor_terms_assumed_positive']=False
            report['centre_zero_excited_support_used_as_exact_source_zero']=False
        _REPORTS.add(_digest(report));return report

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/interval-CP-column' and
                 report.get('source_record')==BFieldReceiptTimeMeasure.record(self),'same literal joint time measure required')
        row,column=report['source_matrix_unit'];a,b=report['first_receipt_restriction_seconds']
        _require(BFieldReceiptTimeMeasure.interval_column(self,row,column,a,b,patterns=report['patterns'],bits=report['scalar_bits'])==report,
                 'complete joint CP state, original triangle, shared price or source mother changed')
        return True

    def memory_at(self,report,source,incoming,first,receipt_time,*,clock_offset_seconds=0):
        _CHECK();record=BFieldReceiptTimeMeasure.record(self)
        _require(type(report) is dict and report.get('source_record')==record and _digest(report) in _REPORTS,
                 'an unchanged source-issued joint interval is required')
        _require(type(source) is apd.APDWindowHistorySource and type(incoming) is apd.ArrivalMemory,
                 'original continuous shared APD memory source and incoming queue required')
        raw=record['complete_two_arm_field_mother'];base=raw['common_optical_source']['common_atomic_owner']['atomic_base']
        unit=Q(base['seconds_per_unit']);apd_record=apd.APDWindowHistorySource.record(source)
        _require(source.seconds_per_unit==unit,'same physical source clock is required for the APD memory')
        transfer,bg=photons.optical.CommonOpticalReadout._parameters(self._source._common,photons.optical.ALL_PORTS)
        counter=photons.joint.JointCounterGenerator.from_record(apd_record['original_shared_source'])
        _require(counter.background_rate==bg and all(item['matrix']==photons.optical._matrix(transfer)
                 for item in counter.record()['collection']) and
                 all(atom.program.gammas==photons.full.Segment.from_record(leg['raw_segment']).gammas
                     for atom,leg in zip(counter.sources,raw['physical_legs'])),
                 'memory and photon arrivals must use the same raw bath and shared APD transfer')
        x,t,offset=map(photons.full.nonnegative,(first,receipt_time,clock_offset_seconds))
        a,b=map(Q,report['first_receipt_restriction_seconds']);g0=Q(raw['gate_seconds'][0])
        _require(g0<=x<=t and a<=t<=b and x>=min(map(Q,raw['source_arrival_origins_seconds'])) and
                 t>=max(map(Q,raw['source_arrival_origins_seconds'])),
                 'latent two-arrival coordinates lie outside the same source receipt domain')
        _require(incoming.clock<=(offset+x)/unit,'incoming memory cannot occur after the latent first arrival')
        memory=apd.APDWindowHistorySource.elapse(source,incoming,(offset+x)/unit-incoming.clock)
        memory=apd.APDWindowHistorySource.append_arrival(source,memory)
        memory=apd.APDWindowHistorySource.elapse(source,memory,(t-x)/unit)
        memory=apd.APDWindowHistorySource.append_arrival(source,memory)
        return {'source_time_measure_record':record,'source_interval_report_digest':_digest(report),
            'incoming_memory':incoming.record(),'source_memory':memory.record(),
            'latent_source_seconds':[str(x),str(t)],'source_clock_offset_seconds':str(offset),
            'actual_quantum_clock_selected_from_UID_or_Unix':False,'emitter_identity_observed':False,
            'queue_not_reset_at_receipt':True,'APD_quantum_jump_dynamics_paid_by_retarded_source':True,
            'instantaneous_counter_quantum_action_consumed_here':False}


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    functions=(_require,_copy,_digest,_bindings,_add,_conjugate,_sum,_difference,_curve_modes,
        _prefactor,_prefactor.__wrapped__,_ordered_triangle,_ordered_triangle.__wrapped__,_leg_vectors,_late_vectors,_branch_terms,
        _branch_factor,_image,_normal_errors,_function,_signature,_check,
        photons.BFieldPhotonSource.record,photons.BFieldPhotonSource.from_record,photons.BFieldPhotonLeg.exponential_curve,
        temporal.PhotonTimeMeasure.__init__,temporal.PhotonTimeMeasure.record,temporal.PhotonTimeMeasure._jump,
        temporal.exponential_moment,temporal.exponential_triangle,temporal._exp,temporal._source_execution,
        temporal._complex,temporal._norm,temporal._product,temporal._inverse,temporal._ceil,
        temporal._unit_moment,getattr(temporal._unit_moment,'__wrapped__',temporal._unit_moment),temporal.Enclosure,
        temporal.Enclosure.__post_init__,temporal.Enclosure.add,temporal.Enclosure.scale,
        temporal.Enclosure.multiply,temporal.Enclosure.rounded,
        photons.receipt.PortBackgroundLaw.insertion,photons.receipt._tensor,photons.dipole.matrix_product,
        photons.dipole.matrix_adjoint,photons.bsm._entry_norm,
        integer_time.RadicalTimeAccumulator.__init__,integer_time.RadicalTimeAccumulator._weight,
        integer_time.RadicalTimeAccumulator._image,integer_time.RadicalTimeAccumulator._add_image,
        integer_time.RadicalTimeAccumulator.add_outer,integer_time.RadicalTimeAccumulator.result,
        integer_time.RadicalMatrixTimeAccumulator.__init__,integer_time.RadicalMatrixTimeAccumulator.add_matrix,
        integer_time._matrix_family,integer_time._integer_product,integer_time._integer_adjoint,
        integer_time._integer_tensor_add,integer_time.RadicalTensorTimeAccumulator.__init__,
        integer_time.RadicalTensorTimeAccumulator._local,integer_time.RadicalTensorTimeAccumulator.add_tensor,
        apd.APDWindowHistorySource.record,apd.APDWindowHistorySource.elapse,apd.APDWindowHistorySource.append_arrival)
    methods=tuple(_function(member) for member in vars(BFieldReceiptTimeMeasure).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(photons.bsm.PATTERNS),SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or _signature.__code__ is not _SIGNATURE_CODE:
        raise ValueError('joint B-field time measure execution changed')
    if _signature()!=_EXPECTED:
        raise ValueError('joint B-field time measure execution changed')


_SIGNATURE,_SIGNATURE_CODE=_signature,_signature.__code__
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_signature()

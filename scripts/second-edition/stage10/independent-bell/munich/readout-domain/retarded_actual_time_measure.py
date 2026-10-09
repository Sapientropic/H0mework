"""The same receipt-time instrument supplies actual-time joint atoms.

The anchor channel is a numerical approximation to the time-dependent
source dilation.  Its uniform operator variation is paid against the whole
receipt measure, and the time total-variation error is transported once.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import retarded_receipt_time_measure as timed
import retarded_atomic_delay_source as delay
import retarded_atomic_delay_envelope as envelope

continuous=timed.continuous
field,full,channel,joint,bsm=(timed.field,timed.full,timed.channel,timed.joint,timed.bsm)
SCHEMA='stage10-source-actual-time-joint-receipt-measure/v1'
_ISSUED={}
_TIMED_CHECK,_DELAY_CHECK,_ENVELOPE_CHECK=timed._CHECK,delay._CHECK,envelope._CHECK


def _require(value,message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__),*(Path(m.__file__) for m in (timed,delay,envelope,continuous)))}


class RetardedActualTimeMeasure:
    def __init__(self,measure,*,bits=192):
        _CHECK();field._closed(measure)
        _require(type(measure) is timed.RetardedReceiptTimeMeasure,'closed source time-tagged receipt measure required')
        raw=measure.record()
        self._measure=measure
        self._delay=delay.RetardedAtomicDelaySource(measure._certificate._source._law)
        self._envelope=envelope.RetardedAtomicDelayEnvelope(self._delay,bits=bits)
        self._value={'schema':SCHEMA,'source_time_measure':raw,'same_source_atomic_delay':self._delay.record(),
            'same_source_uniform_delay_envelope':self._envelope.record(),
            'physical_rule':'mu_actual(B)=integral_B D_tau mu_ret(d tau)',
            'all_other_field_and_queue_mother_retained':True,
            'actual_hardware_member_asserted':False,'source_bindings':_bindings(),'controller_advance':False}
        self._seal=continuous._digest(self._value);_ISSUED[id(self)]=self._seal,measure,self._delay,self._envelope

    def record(self):
        _CHECK();field._closed(self)
        _require(type(self) is RetardedActualTimeMeasure and
            set(vars(self))=={'_measure','_delay','_envelope','_value','_seal'} and
            _ISSUED.get(id(self))==(self._seal,self._measure,self._delay,self._envelope) and
            continuous._digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            self._measure.record()==self._value['source_time_measure'] and
            self._delay.record()==self._value['same_source_atomic_delay'] and
            self._envelope.record()==self._value['same_source_uniform_delay_envelope'] and
            self._delay._law is self._measure._certificate._source._law,
            'original receipt-time mother or same-source physical delay changed')
        return continuous._copy(self._value)

    def generate_trial(self,lower,upper,reference,*,left_closed=False,right_closed=True,
                       slices=64,order=32,mode_bits=160,coefficient_bits=192,envelope_order=10,
                       delay_representation='polynomial',delay_krylov_dimension=48):
        raw=RetardedActualTimeMeasure.record(self)
        variation=self._envelope.restriction(lower,upper,reference)
        receipt=self._measure.interval(lower,upper,left_closed=left_closed,right_closed=right_closed,bits=coefficient_bits)
        curves=[{'pattern_index':row['pattern_index'],'untrusted_joint_delay':self._delay.generate_trial(
            row['complete_retarded_poststate'],reference,slices=slices,order=order,mode_bits=mode_bits,
            coefficient_bits=coefficient_bits,envelope_order=envelope_order,
            representation=delay_representation,krylov_dimension=delay_krylov_dimension)} for row in receipt['four_pattern_poststates']]
        return {'schema':SCHEMA+'/untrusted-actual-time-image','source_record':raw,
            'physical_receipt_interval_seconds':list(map(str,(full.nonnegative(lower),full.nonnegative(upper)))),
            'source_anchor_detector_seconds':str(full.nonnegative(reference)),
            'Stieltjes_left_closed':left_closed,'Stieltjes_right_closed':right_closed,
            'source_time_measure_restriction':receipt,'uniform_source_delay_price':variation,
            'four_pattern_anchor_delay_trials':curves,'receipt_scalar_bits':coefficient_bits,
            'writer_correctness_assumed':False}

    def _norm_upper(self,receipt,lower,upper,bits):
        curve=self._measure._report
        if curve['source_issued_input_used']:
            centre=timed.dipole.Radical()
            for row in receipt['four_pattern_poststates']:
                centre+=joint._trace(channel._read_input(row['complete_retarded_poststate'],joint.DIMENSION)).real
            value,error=full.radical_midpoint(centre,bits)
            price=Q(receipt['whole_four_pattern_trace_norm_error'])
            return max(Q(0),value+error+price),{'bound':'same positive source receipt mass plus whole measure error',
                'source_positive_input_used':True,'whole_measure_error_in_mass_upper':str(price)}
        original=continuous._read_state(curve['untrusted_trial']['complete_initial_marked_state'],self._measure._certificate._source)
        marks=tuple({m for m,_,_ in original})
        activity=continuous.activity.RetardedReceiptActivityEnvelope(self._delay._law,bits=bits)
        cap=activity.first_receipt_cap(start_marks=marks,input_time=Q(curve['source_detector_interval_seconds'][0]),
            interval=(lower,upper))
        norm_upper=(Q(curve['source_initial_trace_norm_upper'])*Q(cap['whole_first_receipt_input_contraction_upper'])+
            Q(curve['whole_upstream_trace_norm_error_once']))
        return norm_upper,{'bound':'whole source initial norm times event effect bound plus generic old error',
            'source_positive_input_used':False,'source_event_effect_bound':cap}

    def certify(self,trial,*,coefficient_bits=192,envelope_order=10):
        raw=RetardedActualTimeMeasure.record(self)
        _require(type(trial) is dict and set(trial)=={'schema','source_record','physical_receipt_interval_seconds',
            'source_anchor_detector_seconds','Stieltjes_left_closed','Stieltjes_right_closed',
            'source_time_measure_restriction','uniform_source_delay_price','four_pattern_anchor_delay_trials',
            'receipt_scalar_bits','writer_correctness_assumed'} and
            trial['schema']==SCHEMA+'/untrusted-actual-time-image' and trial['source_record']==raw and
            trial['writer_correctness_assumed'] is False,'actual-time image must bind its complete original source')
        lower,upper=map(Q,trial['physical_receipt_interval_seconds']);reference=Q(trial['source_anchor_detector_seconds'])
        receipt=self._measure.interval(lower,upper,left_closed=trial['Stieltjes_left_closed'],
            right_closed=trial['Stieltjes_right_closed'],bits=trial['receipt_scalar_bits'])
        variation=self._envelope.restriction(lower,upper,reference)
        _require(receipt==trial['source_time_measure_restriction'] and variation==trial['uniform_source_delay_price'],
                 'original Stieltjes cell, receipt-time measure or uniform delay price changed')
        proposals=trial['four_pattern_anchor_delay_trials']
        _require(type(proposals) is list and len(proposals)==4,'all four original pattern delay images required')
        patterns=[];reports=[];new_error=Q(0)
        for row,proposal in zip(receipt['four_pattern_poststates'],proposals):
            _require(type(proposal) is dict and set(proposal)=={'pattern_index','untrusted_joint_delay'} and
                proposal['pattern_index']==row['pattern_index'],'original pattern identity changed')
            curve=proposal['untrusted_joint_delay']
            _require(curve['complete_initial_joint_matrix']==row['complete_retarded_poststate'] and
                curve['physical_detector_seconds']==str(reference),'anchor delay must consume this same complete receipt poststate')
            checked=self._delay.certify(curve,input_error=0,coefficient_bits=coefficient_bits,envelope_order=envelope_order)
            new_error+=Q(checked['whole_trace_norm_error']);reports.append(checked)
            patterns.append({'pattern_index':row['pattern_index'],'pattern_name':row['pattern_name'],
                'complete_actual_time_poststate':checked['complete_physical_joint_endpoint']})
        mass,mass_record=RetardedActualTimeMeasure._norm_upper(self,receipt,lower,upper,coefficient_bits)
        uniform=Q(variation['whole_two_arm_delay_operator_difference_upper'])*mass
        old=Q(receipt['whole_four_pattern_trace_norm_error'])
        return {'schema':SCHEMA+'/checked-actual-time-image','source_record':raw,'untrusted_trial':continuous._copy(trial),
            'four_pattern_actual_time_poststates':patterns,'four_complete_anchor_delay_certificates':reports,
            'source_time_measure_error_transported_once':str(old),
            'source_receipt_time_norm_upper':str(field._price_upper(mass,coefficient_bits)),
            'source_receipt_time_norm_upper_derivation':mass_record,
            'uniform_time_dependent_delay_price':str(field._price_upper(uniform,coefficient_bits)),
            'new_anchor_numeric_delay_error':str(field._price_upper(new_error,coefficient_bits)),
            'whole_four_pattern_trace_norm_error':str(field._price_upper(old+uniform+new_error,coefficient_bits)),
            'time_dependent_physical_delay_paid':True,'all_pattern_error_is_one_direct_sum_bound':True,
            'unpriced_representative_clock_used':False,'actual_hardware_member_asserted':False,
            'coefficient_bits':coefficient_bits,'envelope_order':envelope_order}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/checked-actual-time-image',
                 'complete actual-time source image certificate required')
        expected=RetardedActualTimeMeasure.certify(self,report['untrusted_trial'],
            coefficient_bits=report['coefficient_bits'],envelope_order=report['envelope_order'])
        _require(expected==report,'actual-time joint poststate, field-time variation or paid error changed')
        return expected


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers=(_require,_bindings,_function,_signature,_check,
        timed.RetardedReceiptTimeMeasure.record,timed.RetardedReceiptTimeMeasure.interval,
        delay.RetardedAtomicDelaySource.record,delay.RetardedAtomicDelaySource.generate_trial,delay.RetardedAtomicDelaySource.certify,
        envelope.RetardedAtomicDelayEnvelope.record,envelope.RetardedAtomicDelayEnvelope.restriction,
        continuous._read_state,continuous.activity.RetardedReceiptActivityEnvelope.first_receipt_cap,
        joint._trace,channel._read_input,field._closed,field._price_upper,full.radical_midpoint)
    methods=tuple(_function(v) for v in vars(RetardedActualTimeMeasure).values() if callable(v))
    return tuple(map(_function,helpers)),methods,SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature()==_EXPECTED and
        timed._CHECK is _TIMED_CHECK and delay._CHECK is _DELAY_CHECK and envelope._CHECK is _ENVELOPE_CHECK,
        'actual-time receipt consumer execution changed')
    _TIMED_CHECK();_DELAY_CHECK();_ENVELOPE_CHECK()


_CHECK,_SIGNATURE=_check,_signature
_EXPECTED=_signature()

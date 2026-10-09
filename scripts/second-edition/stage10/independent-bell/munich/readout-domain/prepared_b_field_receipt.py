"""Source-issued reference local coimages feed the same retarded instrument.

Signed Hermitian factors retain the complete pair; positivity belongs to
the original native/CP source.  They are never treated as separate states.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import b_field_photon_source as photons
import b_field_receipt_time_measure as joint_time
import reference_local_phase_source as local
import reference_joint_receipt_time_measure as reference_joint
import prepared_retarded_source as tensor_kernel

SCHEMA='stage10-source-issued-prepared-B-field-receipt/v1'
_ISSUED=set()
_REPORTS=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return photons._copy(value)


def _digest(value):
    return photons._digest(value)


def _producer(source):
    if type(source) is local.ReferenceLocalPhaseSource:
        return local.ReferenceLocalPhaseSource,'reference exact local CP source'
    try:
        import fourier_reference_local_programme_source as programme
    except ModuleNotFoundError as error:
        if error.name!='fourier_reference_local_programme_source':
            raise
        raise ValueError('closed reference local or Fourier programme source required') from error
    _require(type(source) is programme.FourierReferenceLocalProgrammeSource,
             'closed reference local or Fourier programme source required')
    return programme.FourierReferenceLocalProgrammeSource,'reference complete Fourier local programme'


def _bindings(source):
    cls,_=_producer(source)
    paths=(Path(__file__),*(Path(module.__file__) for module in
        (photons,joint_time,local,reference_joint,tensor_kernel,local.aperture)),Path(__import__(cls.__module__).__file__))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _tensor_input(terms,bits):
    _require(type(terms) is list and terms,'complete source-generated tensor terms required')
    matrices=[];local_price=Q(0);detail=[]
    for item in terms:
        a,b=item['left'],item['right']
        ma=photons.channel._read_input(a['local_poststate'],33)
        mb=photons.channel._read_input(b['local_poststate'],33)
        _require(ma==photons.dipole.matrix_adjoint(ma) and mb==photons.dipole.matrix_adjoint(mb),
                 'source-generated tensor factors must remain Hermitian; positivity is not assumed')
        ea,eb=map(photons.full.nonnegative,(a['trace_norm_error'],b['trace_norm_error']))
        na,nb=(photons.bsm._entry_norm(matrix,bits=bits) for matrix in (ma,mb))
        cost=ea*nb+eb*na+ea*eb
        _require(item['local_norm_upper']==[str(na),str(nb)] and Q(item['tensor_error'])==cost,
                 'source tensor price must retain signed-factor cross errors')
        local_price+=cost;matrices.append((ma,mb))
        detail.append({'left_factor_id':a['factor_id'],'right_factor_id':b['factor_id'],
            'local_operator_norm_uppers':[str(na),str(nb)],'local_errors':[str(ea),str(eb)],'tensor_error':str(cost)})
    return tuple(matrices),local_price,detail


def _pullback(first,terms,second):
    """Same full tensor sandwich as the already checked source field kernel."""
    return tensor_kernel._tensor_sandwich(first[0],first[1],second[0],second[1],terms)


def _leg_operators(ground,excited,jump):
    """Keep complete local columns for the original mode contraction."""
    combined={}
    for ge,gm in ground:
        for ee,em in excited:
            operator=photons.dipole.matrix_product(photons.dipole.matrix_product(gm,jump),em)
            if operator:
                photons._add(combined.setdefault((ge,ee),{}),operator)
    return [(ge,ee,operator) for (ge,ee),operator in combined.items() if operator]


def _operator_branches(legs,early_side):
    branches=[]
    for ge,ee,early in legs[early_side]:
        for gl,el,late in legs[1-early_side]:
            operators=(early,late) if early_side==0 else (late,early)
            branches.append((joint_time._difference(ee,ge),joint_time._sum(ge,el),ge,ee,gl,el,operators))
    return branches


def _ready_mass_upper(parent):
    ready=parent['reference_first_poll_ready']
    matrix=photons.channel._read_input(ready['generated_first_ready_poststate'],photons.joint.DIMENSION)
    trace=photons.joint._trace(matrix)
    _require(not trace.imag,'Hermitian reference Ready mass required')
    centre,rounding=photons.full.radical_midpoint(trace.real,192)
    # Native Ready is a positive trace-nonincreasing branch.  Every local
    # phase is TP on that same branch, so this mass survives the programme.
    return min(Q(1),max(Q(0),centre+rounding+Q(ready['first_poll_joint_error'])))


def _objective_contraction(parent,physical,bits):
    domain=local.aperture.ApertureCollectionDomain.from_record(parent['working_aperture_source'])
    geometry=local.aperture.ApertureCollectionDomain.record(domain)
    field=physical['reference_centre_field_source']
    _require(geometry==physical['same_lambda_aperture_source'] and
             geometry['common_optical_source']==field['common_optical_source'],
             'the whole two-signal contraction must use the original field and objective source')
    maxima=tuple(local.aperture.cone_gram(Q(a))[0] for a in geometry['numerical_apertures'])
    product=maxima[0]*maxima[1]
    centre,rounding=photons.full.radical_midpoint(product,bits)
    upper=min(Q(1),max(Q(0),centre+rounding))
    return {'objective_collection_domain':geometry,
        'source_leg_collection_effect_bounds':[a.serialize() for a in maxima],
        'whole_two_signal_input_contraction_upper':str(upper),
        'exact_product':product.serialize(),'product_centre':str(centre),'product_rounding':str(rounding),
        'operator_law':'Gamma_2(T* T) <= Gamma_2(blockdiag(c_A I,c_B I)); one emitted photon per arm gives c_A*c_B I',
        'natural_emission_law':'K*+K=-R implies sum integral Ue* L* L Ue <= I on each complete leg',
        'all_resolved_groups_time_restrictions_and_Bose_cross_terms_covered':True,
        'numerical_input_positivity_assumed':False,'positive_BG_complement_scaled':False}


class PreparedBFieldReceipt:
    def __init__(self,source,report,measure,*,bits=192):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('prepared B-field source execution changed')
        _CHECK()
        _require(type(bits) is int and 64<=bits<=512,'registered source contraction precision required')
        cls,kind=_producer(source)
        photons._closed(source);photons._closed(measure)
        _require(type(measure) is reference_joint.ReferenceJointReceiptTimeMeasure,
                 'same closed reference joint photon-time instrument required')
        issued=cls.record(source);cls.verify(source,report)
        parent=(issued if cls is local.ReferenceLocalPhaseSource else issued['reference_local_parent'])
        instrument=reference_joint.ReferenceJointReceiptTimeMeasure.record(measure)
        physical=instrument['reference_field_source'];field=physical['reference_centre_field_source']
        _require(report['source_record']==issued and physical['reference_local_parent']==parent,
                 'prepared phases and photon field must have one original reference local parent')
        _require(report['working_atomic_owner']==parent['working_atomic_owner']==field['common_optical_source']['common_atomic_owner'] and
                 report['working_common_optical_source']==parent['working_common_optical_source']==field['common_optical_source'] and
                 report['working_aperture_source']==parent['working_aperture_source']==physical['same_lambda_aperture_source'] and
                 report['same_reference_clock']==parent['reference_clock']==physical['reference_clock'],
                 'prepared state, aperture, Gamma and full four-port optics must be the same source')
        origins=tuple(map(Q,report['source_local_emission_origins_seconds']))
        _require(list(map(str,origins))==field['emission_origin_seconds']==physical['source_local_emission_origins_seconds'],
                 'both local physical phase endpoints must be the original photon source origins')
        flights=tuple(map(Q,field['flight_seconds']));g0=Q(field['gate_seconds'][0])
        _require(all(origin+flight<=g0 for origin,flight in zip(origins,flights)),
                 'earlier driven photons can still enter this gate; their full driven field is required')
        terms,price,detail=_tensor_input(report['tensor_terms'],bits)
        old=Q(report['old_error_once']);error=Q(report['trace_norm_error'])
        _require(error==old+price,'complete reference Ready/local tensor error must telescope once')
        mass=_ready_mass_upper(parent)
        contraction=_objective_contraction(parent,physical,bits)
        self._source,self._measure,self._terms=source,measure,terms
        self._value={'schema':SCHEMA,'source_kind':kind,'forward_source_record':issued,
            'complete_forward_certificate':_copy(report),'reference_local_parent':parent,
            'reference_joint_instrument':instrument,'source_tensor_error_records':detail,
            'source_input_positive_mass_upper':str(mass),'source_centre_trace_norm_upper':str(mass+error),
            'whole_upstream_trace_norm_error':str(error),'original_native_error_in_tensor_sum_once':str(old),
            'source_objective_signal_contraction':contraction,
            'source_local_and_tensor_error':str(price),
            'source_local_emission_origins_seconds':list(map(str,origins)),
            'earlier_driven_photon_gate_disjointness':{'latest_arrivals_seconds':[str(a+b) for a,b in zip(origins,flights)],
                'fixed_gate_origin_seconds':str(g0),'native_APD_time_mother_discarded':False},
            'complete_preparation_then_excitation_plan':report['complete_preparation_then_excitation_plan'],
            'whole_reference_native_time_and_PC_mother':parent['whole_reference_native_time_and_PC_mother'],
            'native_pending_poststate':parent['native_pending_poststate'],
            'signed_factor_positivity_assumed':False,'free_density_or_Bell_target_supplied':False,
            'scalar_bits':bits,'source_bindings':_bindings(source),'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED.add(self._seal)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('prepared B-field source execution changed')
        _CHECK();photons._closed(self)
        cls,_=_producer(self._source)
        _require(type(self) is PreparedBFieldReceipt and set(vars(self))=={'_source','_measure','_terms','_value','_seal'} and
                 self._seal in _ISSUED and _digest(self._value)==self._seal and self._value['source_bindings']==_bindings(self._source) and
                 cls.record(self._source)==self._value['forward_source_record'] and
                 reference_joint.ReferenceJointReceiptTimeMeasure.record(self._measure)==self._value['reference_joint_instrument'],
                 'prepared source, time mother, instrument or whole error changed')
        terms,price,_=_tensor_input(self._value['complete_forward_certificate']['tensor_terms'],self._value['scalar_bits'])
        _require(terms==self._terms,'complete source-generated tensor factors changed')
        return _copy(self._value)

    def source_tensors(self):
        """The direct contraction inlet is issued from the verified mother."""
        record=PreparedBFieldReceipt.record(self)
        return {'source_record':record,'tensor_terms':tuple((dict(a),dict(b)) for a,b in self._terms),
            'source_centre_trace_norm_upper':Q(record['source_centre_trace_norm_upper']),
            'whole_upstream_trace_norm_error':Q(record['whole_upstream_trace_norm_error']),
            'positive_source_mass_upper':Q(record['source_input_positive_mass_upper']),
            'whole_input_signal_contraction_upper':Q(record['source_objective_signal_contraction']['whole_two_signal_input_contraction_upper']),
            'time_state_mother':record['whole_reference_native_time_and_PC_mother']}

    def interval(self,start,stop,*,patterns=None,bits=192):
        record=PreparedBFieldReceipt.record(self)
        centre=joint_time.BFieldReceiptTimeMeasure.interval_prepared(self._measure._measure,self,
            start,stop,patterns=patterns,bits=bits)
        physical=record['reference_joint_instrument']['reference_field_source']
        parameter=reference_joint._parameter_payment(physical,centre,bits)
        mass=Q(record['source_input_positive_mass_upper'])
        payment=mass*Q(parameter['whole_reference_clock_payment'])
        report={'schema':SCHEMA+'/interval-CP','source_record':record,
            'reference_centre_CP_certificate':centre,'reference_clock_price':parameter,
            'reference_clock_price_source_positive_mass_upper':str(mass),
            'whole_reference_clock_payment':str(payment),
            'four_pattern_poststates':centre['four_pattern_poststates'],
            'centre_curve_scalar_and_old_error':centre['whole_trace_norm_error_upper'],
            'whole_trace_norm_error_upper':str(Q(centre['whole_trace_norm_error_upper'])+payment),
            'first_receipt_restriction_seconds':centre['first_receipt_restriction_seconds'],
            'patterns':centre['patterns'],'scalar_bits':bits,
            'whole_reference_native_time_and_PC_mother':record['whole_reference_native_time_and_PC_mother'],
            'native_pending_poststate':record['native_pending_poststate'],
            'complete_reference_field_BG_positive_complement_mother':physical,
            'source_positive_Ready_normalized':False,
            'probability_scope':centre['probability_scope'],
            'complete_preparation_then_excitation_plan':record['complete_preparation_then_excitation_plan'],
            'full_record_or_actual_hardware_identity_asserted':False,'controller_advance':False}
        _REPORTS.add(_digest(report));return report

    def verify(self,report):
        record=PreparedBFieldReceipt.record(self)
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/interval-CP' and
                 report.get('source_record')==record,'same closed prepared receipt source required')
        if _digest(report) not in _REPORTS:
            a,b=report['first_receipt_restriction_seconds']
            _require(PreparedBFieldReceipt.interval(self,a,b,patterns=report['patterns'],bits=report['scalar_bits'])==report,
                     'whole prepared interval, source tensor, Gamma, scalar price or time mother changed')
        return True

    @classmethod
    def from_record(cls,record):
        _require(cls is PreparedBFieldReceipt and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed prepared B-field receipt source record required')
        source_record=record['forward_source_record']
        if source_record.get('schema')==local.SCHEMA:
            source=local.ReferenceLocalPhaseSource.from_record(source_record)
            parent=source
        else:
            import fourier_reference_local_programme_source as programme
            source=programme.FourierReferenceLocalProgrammeSource.from_record(source_record)
            parent=source._parent
        instrument=record['reference_joint_instrument']
        physical_record=instrument['reference_field_source']
        field_record=physical_record['reference_centre_field_source']
        physical=reference_joint.reference.ReferencePhotonTimeSource(parent,
            flight_seconds=field_record['flight_seconds'],gate_seconds=field_record['gate_seconds'])
        _require(reference_joint.reference.ReferencePhotonTimeSource.record(physical)==physical_record,
                 'original physical photon field, clocks or Gamma mother changed')
        measure=reference_joint.ReferenceJointReceiptTimeMeasure(physical,
            instrument['centre_joint_source']['complete_source_certificates'])
        result=cls(source,record['complete_forward_certificate'],measure,bits=record['scalar_bits'])
        _require(PreparedBFieldReceipt.record(result)==record,'complete prepared, time or source mother changed')
        return result


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers=(_require,_copy,_digest,_producer,_bindings,_tensor_input,_pullback,_leg_operators,_operator_branches,
        _ready_mass_upper,_objective_contraction,_function,_signature,_check,
        local.aperture.ApertureCollectionDomain.from_record,local.aperture.ApertureCollectionDomain.record,
        local.aperture.cone_gram,
        photons.BFieldPhotonSource.record,photons.dipole.matrix_adjoint,photons.channel._read_input,photons.joint._trace,
        photons.full.radical_midpoint,photons.bsm._entry_norm,
        local.ReferenceLocalPhaseSource.record,local.ReferenceLocalPhaseSource.verify,
        local.ReferenceLocalPhaseSource.from_record,
        reference_joint.ReferenceJointReceiptTimeMeasure.__init__,reference_joint.ReferenceJointReceiptTimeMeasure.record,
        reference_joint.reference.ReferencePhotonTimeSource.__init__,reference_joint.reference.ReferencePhotonTimeSource.record,
        reference_joint._parameter_payment,tensor_kernel._tensor_sandwich,joint_time.BFieldReceiptTimeMeasure.interval_prepared,
        photons.dipole.matrix_product,joint_time._difference,joint_time._sum)
    methods=tuple(_function(member) for member in vars(PreparedBFieldReceipt).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return tuple(map(_function,helpers)),methods,SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or _signature.__code__ is not _SIGNATURE_CODE:
        raise ValueError('prepared B-field source execution changed')
    if _signature()!=_EXPECTED:
        raise ValueError('prepared B-field source execution changed')


_SIGNATURE,_SIGNATURE_CODE=_signature,_signature.__code__
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_signature()

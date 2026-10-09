"""Reference physical Ready generates exact raw local tensor coimages.

The working unit is the checked reference Gamma centre.  Every true Gamma
in the strict numerical pi enclosure uses the same normalized spectrum and
raw controls; its time-dependent local action is covered before tensoring.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import munich_atomic_programme as atomic
import common_optical_readout as common
import aperture_collection_domain as aperture
import reference_atomic_clock_source as reference
import factorized_local_phase_source as factors
import exact_local_phase_source as exact
import bsm_retry_source as bsm


SCHEMA='stage10-reference-clock-exact-local-phase-source/v1'
_ISSUED=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    paths=(Path(__file__),*(Path(module.__file__) for module in
        (dipole,full,channel,local,joint,atomic,common,aperture,reference,factors,exact,bsm)))
    return {path.name:hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _working_package(record):
    original=record['common_normalized_atomic_owner'];old=original['atomic_base']
    gamma=Q(record['reference_clock']['Gamma_numerical_centre'])
    base=atomic.AtomicBase(old['spectrum'],dict(zip(full.WIDTHS,old['natural_widths'])),
        magnetic_fields=old['magnetic_fields'],magnetic_moments=old['magnetic_moments'],
        seconds_per_unit=1/gamma,radiation_regime=old['radiation_regime'])
    owner=atomic.MunichAtomicProgramme(base,original['beam_transfers'],paid_si_leaf=None)
    raw=atomic.MunichAtomicProgramme.record(owner)
    keys=('spectrum','natural_widths','magnetic_fields','magnetic_moments','radiation_regime')
    _require(all(raw['atomic_base'][key]==old[key] for key in keys) and raw['beam_transfers']==original['beam_transfers'],
             'working clock owner changed the original normalized atomic or beam lambda')
    domain=record['same_lambda_aperture_source'];optics=domain['common_optical_source']
    source=common.CommonOpticalReadout(owner,collection_a=common._read_matrix(optics['collection_a']),
        collection_b=common._read_matrix(optics['collection_b']),splitter=common._read_matrix(optics['splitter']),
        efficiencies=optics['efficiencies'],background_rates=optics['background_rates'])
    cone=aperture.ApertureCollectionDomain(source,numerical_apertures=tuple(map(Q,domain['numerical_apertures'])),
        axes_aligned=tuple(domain['axes_aligned']))
    check=aperture.ApertureCollectionDomain.record(cone)
    current=common.CommonOpticalReadout.record(source)
    _require(all(current[key]==optics[key] for key in
        ('collection_a','collection_b','splitter','efficiencies','background_rates','generated_four_by_six_transfer')),
        'working physical clock changed the shared optical lambda')
    return owner,current,check


def _raw_plans(owner,raw_plans):
    _require(type(raw_plans) in (tuple,list) and len(raw_plans)==2,'two complete raw local clock plan inventories required')
    unit=Q(atomic.MunichAtomicProgramme.record(owner)['atomic_base']['seconds_per_unit'])
    result=[]
    for side,plan in enumerate(raw_plans):
        _require(type(plan) in (tuple,list) and plan,'a nonempty raw local phase plan is required on each side')
        rows=[];previous=None;excited=False
        for index,item in enumerate(plan):
            _require(type(item) is dict and set(item)=={'kind','duration_seconds','drives','cuts_seconds'},
                'raw role, physical duration, drives and physical cuts required; phases or target matrices are not inputs')
            kind=item['kind'];duration=full.exact(item['duration_seconds'])
            _require(kind in ('preparation','excitation') and not excited,
                         'preparation precedes the unique final local excitation')
            drives=tuple(atomic.Drive.from_record(d) for d in item['drives'])
            phase=atomic.MunichAtomicProgramme.phase(owner,kind,side,duration,drives)
            if kind=='preparation':
                pump=next(d for d in drives if d.role=='pump2to1');address=pump.beam,pump.polarization
                _require(previous is None or all(a!=b for a,b in zip(previous,address)),
                         'source pump direction and polarization must alternate')
                previous=address
            else:
                _require(index==len(plan)-1,'local excitation must be the final source phase');excited=True
            cuts=tuple(map(full.exact,item['cuts_seconds']))
            _require(len(cuts)>=2 and cuts[0]==0 and cuts[-1]==duration and all(a<b for a,b in zip(cuts,cuts[1:])),
                         'physical cuts must cover the entire original raw local duration')
            rows.append({'raw_controls':{'kind':kind,'duration_seconds':str(duration),
                'drives':[atomic.Drive.record(d) for d in drives],'cuts_seconds':list(map(str,cuts))},
                'source_phase':atomic.AtomicPhase.record(phase),'cuts_source_units':[str(t/unit) for t in cuts]})
        result.append(rows)
    return result


def _cells(plan):
    return [(index,cell,atomic._read_phase(item['source_phase']),(Q(a),Q(b)),(Q(sa),Q(sb)))
        for index,item in enumerate(plan) for cell,((a,b),(sa,sb)) in enumerate(zip(
            zip(item['cuts_source_units'],item['cuts_source_units'][1:]),
            zip(item['raw_controls']['cuts_seconds'],item['raw_controls']['cuts_seconds'][1:])))]


def _phase_clock_price(phase,physical_interval,clock,input_norm,bits):
    program=atomic.AtomicPhase.programme(phase)
    owner=atomic.MunichAtomicProgramme.from_record(atomic.AtomicPhase.record(phase)['parent'])
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    static=exact.multitone._sum(program.static,atomic.AtomicBase.off_diagonal_zeeman(base,phase.record()['side']))
    static_norm=atomic._operator_upper(static,bits)
    outgoing=max(program.bath.outgoing)
    tones=[];amplitude_sum=frequency_sum=Q(0)
    for tone in program.tones:
        excitation=program._excitation(tone);norm=atomic._operator_upper(excitation,bits)
        amplitude_sum+=norm;frequency_sum+=abs(tone.angular_frequency)*norm
        tones.append({'raw_tone':tone.record(),'raising_operator_norm_upper':str(norm),
                      'frequency_times_operator_norm_upper':str(abs(tone.angular_frequency)*norm)})
    generator_bound=2*(static_norm+outgoing)+4*amplitude_sum
    derivative_bound=4*frequency_sum
    a,b=physical_interval;delta=Q(clock['Gamma_numerical_error'])
    gamma_hi=max(Q(clock['Gamma_numerical_centre']),Q(clock['angular_Gamma_enclosure_per_second'][1]))
    scale_price=delta*(b-a)*generator_bound*input_norm
    phase_price=delta*gamma_hi*(b*b-a*a)*derivative_bound*input_norm/2
    return {'source_clock':clock,'physical_phase_local_interval_seconds':list(map(str,(a,b))),
        'full_static_H_operator_norm_upper':str(static_norm),'original_outgoing_max':str(outgoing),
        'raw_tone_norms':tones,'Gnorm_induced_trace_norm_upper':str(generator_bound),
        'Gnorm_source_time_derivative_norm_upper':str(derivative_bound),
        'complete_input_trace_norm_upper':str(input_norm),
        'reference_Gamma_scale_payment':str(scale_price),'reference_tone_time_payment':str(phase_price),
        'total_trace_norm_payment':str(scale_price+phase_price),
        'source_law':'Gphysical_Gamma(t)=Gamma*Gnorm(Gamma*t) on each original local phase clock',
        'bound':'deltaGamma*[Delta_t*M+Gamma_hi*(b^2-a^2)*L/2]*norm(centre)',
        'old_error_multiplied_by_clock_price':False,'source_model_mean_price':'0'}


def _outward_error(value,bits):
    _require(value>=0 and type(bits) is int and 64<=bits<=512,'nonnegative source error and registered precision required')
    quantum=1<<bits;scaled=value*quantum
    result=Q(-(-scaled.numerator//scaled.denominator),quantum)
    return result,result-value


class ReferenceLocalPhaseSource:
    def __init__(self,source,ready_report,raw_two_side_clock_plans):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('reference local executed source closure changed')
        _GUARD()
        _require(type(source) is reference.ReferenceAtomicClockSource,
                 'closed reference physical source required; a Ready density or old Native report is not input')
        original=reference.ReferenceAtomicClockSource.record(source)
        reference.ReferenceAtomicClockSource.verify_first_poll_ready(source,ready_report)
        owner,common_source,cone=_working_package(original)
        matrix=channel._read_input(ready_report['generated_first_ready_poststate'],joint.DIMENSION)
        inventory,terms=factors._factor_inventory(factors._decompose(matrix))
        plans=_raw_plans(owner,raw_two_side_clock_plans)
        complete=all(len(plan)>=3 and plan[-1]['raw_controls']['kind']=='excitation' for plan in plans)
        self._frame={'schema':SCHEMA,'reference_native_source_record':original,'reference_first_poll_ready':_copy(ready_report),
            'reference_clock':original['reference_clock'],'working_atomic_owner':atomic.MunichAtomicProgramme.record(owner),
            'working_common_optical_source':common_source,'working_aperture_source':cone,
            'source_generated_local_plans':plans,'complete_initial_ready':channel._input_record(matrix),
            'complete_preparation_then_excitation_plan':complete,
            'source_scope':'complete supplied raw local CP schedule; the declared prefix is not relabelled as the full preparation/excitation programme',
            'upstream_trace_norm_error':ready_report['first_poll_joint_error'],
            'local_factor_inventory':inventory,'source_tensor_factor_ids':terms,
            'source_ready_physical_clock_seconds':ready_report['same_physical_geometry']['physical_seconds']['stop'],
            'whole_reference_native_time_and_PC_mother':_copy(ready_report),
            'native_pending_poststate':_copy(ready_report['first_poll_pending_poststate']),
            'native_loaded_flags_and_count_faces':_copy(ready_report['count_faces']),
            'Gamma_math_interval_is_an_unknown_hardware_coordinate':False,
            'normalized_atomic_lambda_changed':False,'old_unit_or_old_Ready_relabelled':False,
            'paid_SI_leaf_installed_on_new_unit':False,'hardware_prior_used':False,
            'actual_hardware_parameters_identified':False,'controller_advance':False,'source_bindings':_bindings()}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('reference local executed source closure changed')
        _GUARD()
        _require(type(self) is ReferenceLocalPhaseSource and set(vars(self))=={'_frame','_seal'} and self._seal in _ISSUED and
            _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),
            'reference native/local occurrence, controls, clock or callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is ReferenceLocalPhaseSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed reference local phase record required')
        raw=[[item['raw_controls'] for item in side] for side in record['source_generated_local_plans']]
        result=cls(reference.ReferenceAtomicClockSource.from_record(record['reference_native_source_record']),
                   record['reference_first_poll_ready'],raw)
        _require(result.record()==record,'reference working owner, plans, tensor factors or history changed')
        return result

    def with_clock_plans(self,raw_two_side_clock_plans):
        record=ReferenceLocalPhaseSource.record(self)
        owner=atomic.MunichAtomicProgramme.from_record(record['working_atomic_owner'])
        record['source_generated_local_plans']=_raw_plans(owner,raw_two_side_clock_plans)
        record['complete_preparation_then_excitation_plan']=all(
            len(plan)>=3 and plan[-1]['raw_controls']['kind']=='excitation' for plan in record['source_generated_local_plans'])
        result=object.__new__(ReferenceLocalPhaseSource);result._frame=record;result._seal=_digest(record);_ISSUED.add(result._seal)
        return result

    def generate_trials(self,*,order=24,mode_bits=160,coefficient_bits=192,exponential_bits=192,phase_order=32):
        record=ReferenceLocalPhaseSource.record(self);side_curves=[]
        precision=dict(phase_order=phase_order,mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits)
        for side,inventory in enumerate(record['local_factor_inventory']):
            cells=_cells(record['source_generated_local_plans'][side]);curves=[]
            for item in inventory:
                current=channel._read_input(item['initial_local_matrix'],full.DIMENSION);witnesses=[]
                for phase_index,cell_index,phase,interval,physical_interval in cells:
                    source=exact.ExactLocalPhaseSource(phase,factors._embed(current,side),interval=interval)
                    curve=exact.ExactLocalPhaseSource.generate_trial(source,order=order,mode_bits=mode_bits,
                        coefficient_bits=coefficient_bits,exponential_bits=exponential_bits)
                    witnesses.append(curve);current=factors._trial_endpoint(curve,mode_bits,side)
                curves.append({'factor_id':item['factor_id'],'cell_curves':witnesses})
            side_curves.append(curves)
        return {'schema':SCHEMA+'/untrusted-source-curves','source_record':record,'precision':precision,'side_curves':side_curves}

    def certify(self,trials):
        record=ReferenceLocalPhaseSource.record(self)
        _require(type(trials) is dict and set(trials)=={'schema','source_record','precision','side_curves'} and
                 trials['schema']==SCHEMA+'/untrusted-source-curves' and trials['source_record']==record and
                 type(trials['side_curves']) is list and len(trials['side_curves'])==2,
                 'complete untrusted same-reference local source curves required')
        precision=trials['precision'];endpoints=[{},{}];local_certificates=[[],[]]
        _require(type(precision) is dict and set(precision)=={'phase_order','mode_bits','coefficient_bits','exponential_bits'},
                 'complete original exact local checker precision required')
        clock=record['reference_clock']
        for side,inventory in enumerate(record['local_factor_inventory']):
            supplied=trials['side_curves'][side]
            _require(type(supplied) is list and [x.get('factor_id') for x in supplied]==[x['factor_id'] for x in inventory],
                     'each source-generated factor needs its own complete original witness')
            cells=_cells(record['source_generated_local_plans'][side])
            for item,witness in zip(inventory,supplied):
                _require(set(witness)=={'factor_id','cell_curves'} and type(witness['cell_curves']) is list and
                         len(witness['cell_curves'])==len(cells),'every physical local slice needs a raw source witness')
                current=channel._read_input(item['initial_local_matrix'],full.DIMENSION);error=Q(0);certificates=[]
                for (phase_index,cell_index,phase,interval,physical_interval),curve in zip(cells,witness['cell_curves']):
                    norm=bsm._entry_norm(current,bits=precision['coefficient_bits'])
                    clock_price=_phase_clock_price(phase,physical_interval,clock,norm,precision['coefficient_bits'])
                    pi_error=Q(clock_price['total_trace_norm_payment'])
                    source=exact.ExactLocalPhaseSource(phase,factors._embed(current,side),upstream_error=error,interval=interval)
                    checked=exact.ExactLocalPhaseSource.certify(source,curve,**precision)
                    _require(checked['old_error_once']==str(error) and checked['source_model_payment']=='0',
                             'original local checker dropped or repeated an inherited source price')
                    current=factors._unembed(channel._read_input(checked['full_pair_endpoint'],joint.DIMENSION),side)
                    before=error;error,rounding=_outward_error(Q(checked['trace_norm_error'])+pi_error,precision['coefficient_bits'])
                    certificates.append({'phase_index':phase_index,'cell_index':cell_index,'old_local_error_once':str(before),
                        'exact_local_certificate':checked,'source_reference_clock_price':clock_price,
                        'source_error_outward_rounding':str(rounding),
                        'complete_factor_error_after_clock':str(error)})
                endpoint={'factor_id':item['factor_id'],'local_poststate':channel._input_record(current),'trace_norm_error':str(error)}
                endpoints[side][item['factor_id']]=endpoint
                local_certificates[side].append({'factor_id':item['factor_id'],'complete_local_certificates':certificates})
        old=Q(record['upstream_trace_norm_error']);error=old;terms=[]
        for left,right in record['source_tensor_factor_ids']:
            a,b=endpoints[0][left],endpoints[1][right]
            ma=channel._read_input(a['local_poststate'],full.DIMENSION);mb=channel._read_input(b['local_poststate'],full.DIMENSION)
            price,na,nb=factors._tensor_price(ma,mb,Q(a['trace_norm_error']),Q(b['trace_norm_error']),precision['coefficient_bits'])
            error+=price;terms.append({'left':a,'right':b,'local_norm_upper':[str(na),str(nb)],'tensor_error':str(price)})
        matrix=factors._expand(terms)
        relative=[sum((Q(item['raw_controls']['duration_seconds']) for item in side),Q(0))
                  for side in record['source_generated_local_plans']]
        origin=Q(record['source_ready_physical_clock_seconds']);absolute=[origin+t for t in relative]
        return {'schema':SCHEMA+'/complete-reference-local-coimage','source_record':record,'untrusted_trials':_copy(trials),
            'complete_local_factor_certificates':local_certificates,'tensor_terms':terms,
            'full_pair_endpoint':channel._input_record(matrix),'trace_norm_error':str(error),'old_error_once':str(old),
            'source_local_and_clock_tensor_error':str(error-old),'source_model_mean_payment':'0',
            'source_ready_physical_clock_seconds':str(origin),
            'source_local_elapsed_seconds':list(map(str,relative)),'source_local_emission_origins_seconds':list(map(str,absolute)),
            'complete_preparation_then_excitation_plan':record['complete_preparation_then_excitation_plan'],
            'working_atomic_owner':record['working_atomic_owner'],'working_common_optical_source':record['working_common_optical_source'],
            'working_aperture_source':record['working_aperture_source'],'same_reference_clock':clock,
            'whole_reference_native_time_and_PC_mother':record['whole_reference_native_time_and_PC_mother'],
            'native_pending_poststate':record['native_pending_poststate'],
            'tensor_error_formula':'referenceOldE_once + sum(eA*norm(Bcentre)+eB*norm(Acentre)+eA*eB)',
            'source_input_positivity_paid_by_reference_PC_branch':True,'signed_factors_assumed_positive':False,
            'full33_pair_retained':True,'small_terms_dropped':False,'controller_advance':False}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/complete-reference-local-coimage' and
            report.get('source_record')==ReferenceLocalPhaseSource.record(self),'same-reference complete local source report required')
        _require(ReferenceLocalPhaseSource.certify(self,report['untrusted_trials'])==report,
                 'reference local matrix, raw source/time witnesses or automatic pi price changed')
        return True


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_working_package,_raw_plans,_cells,_phase_clock_price,_outward_error,_function,_execution,_guard,
        reference.ReferenceAtomicClockSource.record,reference.ReferenceAtomicClockSource.from_record,
        reference.ReferenceAtomicClockSource.verify_first_poll_ready,
        atomic.AtomicBase.__init__,atomic.AtomicBase.record,atomic.MunichAtomicProgramme.__init__,atomic.MunichAtomicProgramme.record,
        atomic.MunichAtomicProgramme.from_record,atomic.MunichAtomicProgramme.phase,atomic._operator_upper,atomic._read_phase,
        atomic.AtomicPhase.record,atomic.AtomicPhase.programme,atomic.Drive.record,atomic.Drive.from_record,
        common.CommonOpticalReadout.__init__,common.CommonOpticalReadout.record,common._read_matrix,
        aperture.ApertureCollectionDomain.record,
        factors._factor_inventory,factors._decompose,factors._embed,factors._unembed,factors._trial_endpoint,factors._tensor_price,factors._expand,
        exact.ExactLocalPhaseSource.certify,exact.ExactLocalPhaseSource.generate_trial,
        channel._canonical,channel._input_record,channel._read_input,full.radical_midpoint,bsm._entry_norm,
        exact.multitone.Programme._excitation,exact.multitone._sum)
    methods=tuple(_function(v) for v in vars(ReferenceLocalPhaseSource).values()
        if callable(v) or isinstance(v,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),full.DIMENSION,joint.DIMENSION,SCHEMA


def _guard():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED:
        raise ValueError('reference local executed source closure changed')
    for module,check,name in ((reference,reference._GUARD,'reference'),(factors,factors._CHECK,'factor')):
        function=module._guard if name=='reference' else module._check
        code=module._GUARD_CODE if name=='reference' else module._CHECK_CODE
        _require(function is check and function.__code__ is code,'reference local inherited source closure changed')
        check()


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_GUARD,_GUARD_CODE=_guard,_guard.__code__
_EXPECTED=_execution()

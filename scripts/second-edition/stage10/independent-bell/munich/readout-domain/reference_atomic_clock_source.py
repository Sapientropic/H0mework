"""Known reference linewidth generates the physical clock and CP action.

Machin bounds concern numerical pi, not an unknown apparatus parameter.  The
complete normalized source is multiplied at the superoperator level, where
the common square-root factors of every GKSL jump have already cancelled.
The old clock representative is used only to assemble the normalized source.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import munich_atomic_programme as atomic
import native_tone_frame as native
import persistent_reload_source as persistent
import persistent_ready_mother as ready
import common_optical_readout as optical
import aperture_collection_domain as aperture
import registration_window_domain as registration
import bsm_retry_source as bsm


SCHEMA='stage10-reference-atomic-physical-clock-source/v1'
ZERO=dipole.ComplexRadical()
_ISSUED=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    paths=(Path(__file__),*(Path(m.__file__) for m in
        (dipole,full,modes,channel,local,joint,atomic,native,persistent,ready,optical,aperture,registration,bsm)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _atan_inverse(denominator,terms):
    # Same exact alternating-series rule as alpha-source/units.py.
    value=sum((Q((-1)**n,(2*n+1)*denominator**(2*n+1)) for n in range(terms)),Q(0))
    adjacent=value+Q((-1)**terms,(2*terms+1)*denominator**(2*terms+1))
    return min(value,adjacent),max(value,adjacent)


def reference_clock(*,terms=40,bits=192):
    _require(type(terms) is int and 16<=terms<=256 and type(bits) is int and 64<=bits<=512,
             'registered exact Machin terms and numerical precision required')
    a,z=_atan_inverse(5,terms);b,y=_atan_inverse(239,terms)
    lo,hi=16*a-4*y,16*z-4*b
    f=registration.D1_REFERENCE_HZ;glo,ghi=2*f*lo,2*f*hi
    quantum=1<<bits;centre=Q(round((glo+ghi)*quantum/2),quantum)
    radius=max(abs(centre-glo),abs(ghi-centre))
    return {'schema':SCHEMA+'/Machin-reference-clock','pi_enclosure':[str(lo),str(hi)],
        'reference_D1_ordinary_linewidth_Hz':str(f),'angular_Gamma_enclosure_per_second':[str(glo),str(ghi)],
        'seconds_per_source_unit_enclosure':[str(1/ghi),str(1/glo)],
        'Gamma_numerical_centre':str(centre),'Gamma_numerical_error':str(radius),
        'unit_numerical_centre':str(1/centre),'terms':terms,'bits':bits,
        'identity':'pi = 16 atan(1/5) - 4 atan(1/239)',
        'remainder':'each atan lies between consecutive alternating partial sums',
        'pi_is_an_unknown_hardware_coordinate':False,
        'reference_linewidth_calibration_uncertainty_included':False,
        'reference_linewidth_role':'the frozen 5.75MHz model reference; independent physical calibration error is a separate parameter'}


def verify_reference_clock(record):
    _require(type(record) is dict and record==reference_clock(terms=record['terms'],bits=record['bits']),
             'reference pi, linewidth or numerical enclosure changed')
    return True


def _scale(state,factor):
    return {key:value*factor for key,value in state.items() if value*factor}


def _read_counter(record):
    return {(c,i,j):channel._complex_record(v) for c,i,j,v in record}


def _counter_record(state):
    return [[c,i,j,v.serialize()] for (c,i,j),v in sorted(state.items())]


def _clock_bounds(value,clock,*,rate=False):
    value=full.exact(value);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
    # Seconds -> normalized time, or normalized rates -> physical rates.
    values=(value*lo,value*hi)
    return [str(min(values)),str(max(values))]


def _capture_rate_bounds(records,clock):
    gamma_lo,gamma_hi=map(Q,clock['angular_Gamma_enclosure_per_second']);result=[]
    for side,record in enumerate(records):
        values=[]
        for mode in record['ground_reservoir_modes']:
            raw=mode['birth_rate']
            _require(type(raw) is dict,'the original real-radical capture rate record is required')
            rate=dipole.Radical({int(root):full.exact(coefficient) for root,coefficient in raw.items()})
            centre,error=full.radical_midpoint(rate,clock['bits'])
            values.append({'state':mode['state'],'normalized_birth_rate_per_source_unit':mode['birth_rate'],
                'physical_birth_rate_per_second_enclosure':[str(max(Q(0),centre-error)*gamma_lo),
                                                            str(max(Q(0),centre+error)*gamma_hi)]})
        result.append({'side':side,'modes':values})
    return result


def _exact_physical_pullback(pieces,gamma,mode_bits):
    quantum=1<<mode_bits
    return [{'duration_seconds':str(Q(piece['duration'])/gamma),'modes':[
        {'lambda_per_second':[str(Q(value,quantum)*gamma) for value in mode['lambda']],
         'coefficients':_copy(mode['coefficients'])} for mode in piece['modes']]} for piece in pieces]


def _geometry(parent,clock,duration):
    source=parent['persistent_source'];inlet=parent['incoming_state']
    old_unit=Q(source['atomic_owner']['atomic_base']['seconds_per_unit'])
    start=Q(inlet['memory']['source_relative_clock'])*old_unit
    origin=Q(source['field_phase_origin_seconds']);gamma=Q(clock['Gamma_numerical_centre'])
    original_poll=Q(parent['first_poll_geometry']['poll'])*old_unit
    _require(0<duration<=original_poll-start,'physical cell must stop at or before its original next PC poll')
    times={'start':start,'stop':start+duration,'field_phase_origin':origin,
        'next_PC_poll':original_poll,'poll_period':Q(source['poll_period_seconds']),
        'poll_phase':Q(source['poll_phase_seconds']),'rolling_APD_window':Q(1,25),
        'BSM_gate_width':bsm.GATE_SECONDS}
    physical_arrivals=[Q(t)*old_unit for t in inlet['memory']['recent_arrival_times']]
    return {'physical_seconds':{key:str(v) for key,v in times.items()},
        'normalized_time_enclosures':{key:_clock_bounds(v,clock) for key,v in times.items()},
        'normalized_time_numerical_centres':{key:str(v*gamma) for key,v in times.items()},
        'old_queue_physical_seconds':list(map(str,physical_arrivals)),
        'old_queue_source_time_enclosures':[_clock_bounds(v,clock) for v in physical_arrivals],
        'stage':inlet['stage'],'loaded_flags':inlet['loaded_flags'],
        'raw_PC_rules':source['rules'],'arrival_poll_order':source['arrival_poll_order'],
        'phase_policy':source['phase_policy'],'rolling_APD_40ms_hard_constraint':True,
        'queue_or_stage_reset':False,'old_representative_used_as_physical_clock':False}


def _norm_bound(cell,bits):
    raw=joint.JointCounterGenerator.from_record(cell['constant_counter_source'])
    result=2*raw.background_rate;prices=[]
    for side,(atom,square,capture_record,enabled) in enumerate(zip(raw.sources,cell['full_source_square'],
            cell['capture_sources'],cell['capture_enabled'])):
        h=channel._read_input(square['full33_transformed_H'],full.DIMENSION)
        hnorm=atomic._operator_upper(h,bits)
        # The complete observed/unobserved Gram sum is the original natural
        # bath, so its summed L*L is the source diagonal outgoing rate.
        outgoing=max(atom.outgoing)
        capture=native.trap.ReloadSource.from_record(capture_record)
        capture_rate=bsm._entry_norm({(0,0):dipole.ComplexRadical(capture.first_birth_rate)},bits=bits) if enabled else Q(0)
        bound=2*(hnorm+outgoing+capture_rate);result+=bound
        prices.append({'side':side,'full_H_operator_norm_upper':str(hnorm),'outgoing_max':str(outgoing),
            'capture_total_rate_upper':str(capture_rate),'induced_trace_norm_bound':str(bound)})
    return result,prices


def _read_aperture(record):
    _require(type(record) is dict and record.get('schema')==aperture.SCHEMA,'closed shared-optics aperture source required')
    common=optical.CommonOpticalReadout.from_record(record['common_optical_source'])
    result=aperture.ApertureCollectionDomain(common,
        numerical_apertures=tuple(map(Q,record['numerical_apertures'])),axes_aligned=tuple(record['axes_aligned']))
    _require(aperture.ApertureCollectionDomain.record(result)==record,'original aperture or shared optical source changed')
    return result


class _NormalizedSource:
    def __init__(self,record):
        self.native=native._ConstantSource(record['normalized_constant_source'])
        self.duration=Q(record['physical_duration_seconds'])*Q(record['reference_clock']['Gamma_numerical_centre'])
        self.threshold=self.native.threshold

    def action(self,state):
        return self.native.action(state)


class _PhysicalSource:
    def __init__(self,record):
        self.normalized=_NormalizedSource(record)
        self.gamma=Q(record['reference_clock']['Gamma_numerical_centre'])
        self.duration=Q(record['physical_duration_seconds']);self.threshold=self.normalized.threshold

    def action(self,state):
        return _scale(self.normalized.action(state),self.gamma)


class SourceKernel(channel.SourceKernel):
    def __init__(self,source,coefficient_bits=192,*,physical=False):
        record=ReferenceAtomicClockSource.record(source)
        _require(type(coefficient_bits) is int and 64<=coefficient_bits<=512 and type(physical) is bool,
                 'registered source-column precision and clock chart required')
        self.source=(_PhysicalSource if physical else _NormalizedSource)(record)
        self.dimension,self.threshold,self.bits=joint.DIMENSION,self.source.threshold,coefficient_bits
        self.columns,self.exact_columns,self.errors={},{},{}


def _centre_initial(record,bits,exp_bits):
    initial={(0,i,j):v for (i,j),v in channel._read_input(record['source_primitive_input'],joint.DIMENSION).items()}
    geometry=record['physical_geometry']['normalized_time_numerical_centres']
    cell=_copy(record['normalized_constant_source']);cell['source_phase_start']=geometry['field_phase_origin']
    rotated,phase_error=native._rotate(initial,cell,Q(geometry['start']),1,exp_bits)
    centre,rounding=native._centre(rotated,bits)
    return centre,phase_error,rounding,cell


class ReferenceAtomicClockSource:
    def __init__(self,frame,*,aperture_source,physical_duration_seconds,pi_terms=40,clock_bits=192):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('reference clock executed source closure changed')
        _GUARD()
        _require(type(frame) is native.NativeToneFrame,'closed raw native source required; Ready matrices or target generators are not inputs')
        original=native.NativeToneFrame.record(frame);parent=original['original_PRM_source']
        owner=atomic.MunichAtomicProgramme.from_record(parent['persistent_source']['atomic_owner'])
        raw=owner.record();leaf=raw['paid_si_leaf']
        _require(leaf is not None,'frozen paid spectrum and six-width reference source required; a toy atomic base is not this reference')
        expected=atomic.MunichAtomicProgramme.from_paid_run(leaf['run']['run'],raw['beam_transfers'],
            magnetic_fields=raw['atomic_base']['magnetic_fields'],magnetic_moments=raw['atomic_base']['magnetic_moments'])
        _require(expected.record()==raw,'the original normalized spectrum, widths, Zeeman or paid raw leaf changed')
        _require(type(aperture_source) is aperture.ApertureCollectionDomain,'the same source-owned aperture and optics domain is required')
        cone=aperture.ApertureCollectionDomain.record(aperture_source)
        common=optical.CommonOpticalReadout.from_record(cone['common_optical_source'])
        shared=parent['persistent_source']['shared_APD']['original_shared_source']
        transfer,background=optical.CommonOpticalReadout._parameters(common,optical.ALL_PORTS)
        _require(cone['common_optical_source']['common_atomic_owner']==raw and Q(shared['background_rate'])==background and
                 all(row['matrix']==optical._matrix(transfer) for row in shared['collection']),
                 'reference source must use this same full shared optical and background package')
        inlet=parent['incoming_state'];recipe=inlet['source_recipe']
        _require(recipe['kind']=='source-owned basis primitive' and Q(inlet['global_error'])==0,
                 'reference physical-clock source starts at an original primitive; old representative-clock Ready is not reusable')
        indices=tuple(dipole.INDEX[dipole.State(*state)] for state in recipe['basis'])
        index=joint.atom_pair_index(*indices);initial={(index,index):dipole.ComplexRadical(1)}
        _require(channel._input_record(initial)==inlet['quantum_centre'],'native input is not its source-issued primitive')
        clock=reference_clock(terms=pi_terms,bits=clock_bits);duration=full.exact(physical_duration_seconds)
        cell=native.NativeToneFrame.whole_cell(frame);geometry=_geometry(parent,clock,duration)
        gamma=Q(clock['Gamma_numerical_centre']);unit_bounds=clock['seconds_per_source_unit_enclosure']
        normalized=joint.JointCounterGenerator.from_record(cell['constant_counter_source'])
        # These are raw normalized inverse coordinates.  Their physical
        # counterparts are generated by this known reference scale.
        self._frame={'schema':SCHEMA,'normalized_native_assembler':original,'common_normalized_atomic_owner':raw,
            'same_lambda_aperture_source':cone,
            'reference_clock':clock,'physical_duration_seconds':str(duration),'physical_geometry':geometry,
            'normalized_constant_source':cell,'source_primitive_input':channel._input_record(initial),
            'source_primitive_genealogy':_copy(inlet),'upstream_trace_norm_error':'0',
            'same_lambda_physical_rate_enclosures':{
                'six_natural_widths':[_clock_bounds(Q(v),clock,rate=True) for v in raw['atomic_base']['natural_widths']],
                'four_BG_rates_source_units':parent['persistent_source']['shared_APD']['original_shared_source']['background_rate'],
                'unmerged_four_BG_rates_source_units':cone['common_optical_source']['background_rates'],
                'selected_BG_rate_per_second':_clock_bounds(normalized.background_rate,clock,rate=True),
                'capture_birth_rate_enclosures':_capture_rate_bounds(cell['capture_sources'],clock)},
            'physical_jump_rule':'L_phys=sqrt(Gamma_ref)*L_normalized; every GKSL product is Gamma_ref times its original product',
            'capture_amplitude_rule':'g_phys=sqrt(Gamma_ref)*g_normalized; n is unchanged; capture rate=Gamma_ref*n*abs(g_normalized)^2',
            'source_unit_interval':unit_bounds,'physical_action':'G_phys=Gamma_ref*G_normalized on the entire atom+Mark operator',
            'same_normalized_spectrum_bath_fields_capture_and_APD_used':True,
            'old_ready_or_old_fixed_physical_duration_certificate_relabelled':False,
            'actual_hardware_parameters_identified':False,'controller_advance':False,'source_bindings':_bindings()}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    @classmethod
    def from_paid_run(cls,run,*,beam_transfers,magnetic_fields,magnetic_moments,
            collection_a,collection_b,splitter,efficiencies,background_rates,
            reservoir_occupations,capture_couplings,drives,rules,seed,
            physical_duration_seconds,poll_period_seconds=Q(1,25),poll_phase_seconds=0,
            field_phase_origin_seconds=0,phase_policy='continuous',arrival_poll_order='arrival_then_poll',
            pi_terms=40,clock_bits=192,compilation_bits=96,axes_aligned=(False,False)):
        _require(cls is ReferenceAtomicClockSource,'closed reference physical-clock factory required')
        owner=atomic.MunichAtomicProgramme.from_paid_run(run,beam_transfers,
            magnetic_fields=magnetic_fields,magnetic_moments=magnetic_moments)
        common=optical.CommonOpticalReadout(owner,collection_a=collection_a,collection_b=collection_b,
            splitter=splitter,efficiencies=efficiencies,background_rates=background_rates)
        cone=aperture.ApertureCollectionDomain(common,axes_aligned=axes_aligned)
        aperture.ApertureCollectionDomain.record(cone)
        source,shared=optical.CommonOpticalReadout.persistent_source(common,
            reservoir_occupations=reservoir_occupations,capture_couplings=capture_couplings,drives=drives,rules=rules,
            poll_period_seconds=poll_period_seconds,poll_phase_seconds=poll_phase_seconds,
            field_phase_origin_seconds=field_phase_origin_seconds,maximum_cell_seconds=poll_period_seconds,
            phase_policy=phase_policy,arrival_poll_order=arrival_poll_order,compilation_bits=compilation_bits)
        _require(type(seed) is dict and set(seed)=={'stage','loaded_flags','clock_seconds','recent_arrivals_seconds','atomic_primitives'},
                 'raw PC/memory and named primitive seed required; a density is not input')
        state=persistent.PersistentReloadSource.seed(source,**seed)
        mother=ready.PersistentReadyMother(source,state);frame=native.NativeToneFrame(mother)
        result=cls(frame,aperture_source=cone,physical_duration_seconds=physical_duration_seconds,pi_terms=pi_terms,clock_bits=clock_bits)
        return result,{'common_optical_source':common.record(),'common_persistent_report':shared,
            'aperture_source':aperture.ApertureCollectionDomain.record(cone),
            'raw_model_variables':'normalized raw amplitudes/frequencies/B/n/g/optics; physical values generated by the known reference scale',
            'physical_raw_timing_inputs':True,'new_native_forward_execution':False}

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('reference clock executed source closure changed')
        _GUARD()
        _require(type(self) is ReferenceAtomicClockSource and set(vars(self))=={'_frame','_seal'} and self._seal in _ISSUED and
                 _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),
                 'reference clock/source/primitive/time or callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is ReferenceAtomicClockSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed reference physical-clock record required')
        frame=native.NativeToneFrame.from_record(record['normalized_native_assembler']);clock=record['reference_clock']
        result=cls(frame,aperture_source=_read_aperture(record['same_lambda_aperture_source']),
                   physical_duration_seconds=record['physical_duration_seconds'],pi_terms=clock['terms'],clock_bits=clock['bits'])
        _require(result.record()==record,'physical reference clock or normalized raw source changed')
        return result

    def action_column(self,key,*,physical=True):
        kernel=SourceKernel(self,96,physical=physical);kernel.column(tuple(key))
        return _counter_record(kernel.exact_columns[tuple(key)])

    def normalized_times(self,physical_seconds):
        record=ReferenceAtomicClockSource.record(self)
        return _clock_bounds(full.nonnegative(physical_seconds),record['reference_clock'])

    def generate_trial(self,*,order=32,mode_bits=160,coefficient_bits=192,exponential_bits=192):
        _require(type(order) is int and 1<=order<=64,'bounded source polynomial order required')
        record=ReferenceAtomicClockSource.record(self);kernel=SourceKernel(self,coefficient_bits)
        term,_,_,_=_centre_initial(record,coefficient_bits,exponential_bits);polynomials=[];quantum=1<<mode_bits
        for n in range(order+1):
            polynomials.append([[c,i,j,round(a*quantum),round(b*quantum)] for (c,i,j),(a,b) in sorted(term.items())
                                if round(a*quantum) or round(b*quantum)])
            if n<order:
                term={key:(Q(round(kernel.source.duration*a*quantum/(n+1)),quantum),
                           Q(round(kernel.source.duration*b*quantum/(n+1)),quantum))
                      for key,(a,b) in kernel.action(term).items()}
        return [{'duration':str(kernel.source.duration),'modes':[{'lambda':[0,0],'coefficients':polynomials}]}]

    def physical_trial(self,normalized_pieces,*,mode_bits=160):
        record=ReferenceAtomicClockSource.record(self);gamma=Q(record['reference_clock']['Gamma_numerical_centre']);quantum=1<<mode_bits
        _require(type(normalized_pieces) is list,'untrusted complete normalized source curve required')
        result=[]
        for item in normalized_pieces:
            modes_out=[]
            for mode in item['modes']:
                modes_out.append({'lambda':[round(Q(value,quantum)*gamma*quantum) for value in mode['lambda']],
                                  'coefficients':_copy(mode['coefficients'])})
            result.append({'duration':str(Q(item['duration'])/gamma),'modes':modes_out})
        _require(sum((Q(item['duration']) for item in result),Q(0))==Q(record['physical_duration_seconds']),
                 'transported curve must cover this raw physical duration')
        return result

    def certify(self,pieces,*,physical_time=False,mode_bits=160,coefficient_bits=192,exponential_bits=192):
        record=ReferenceAtomicClockSource.record(self);clock=record['reference_clock'];gamma=Q(clock['Gamma_numerical_centre'])
        _require(type(pieces) is list and type(physical_time) is bool and type(mode_bits) is int and 32<=mode_bits<=256,
                 'complete untrusted curve and explicit original time chart required')
        normalized=_copy(pieces);quantum=1<<mode_bits
        if physical_time:
            for item in normalized:
                item['duration']=str(Q(item['duration'])*gamma)
                for mode in item['modes']:
                    mode['lambda']=[round(Q(value,quantum)/gamma*quantum) for value in mode['lambda']]
        kernel=SourceKernel(self,coefficient_bits);centre,rotation,rounding,cell=_centre_initial(record,coefficient_bits,exponential_bits)
        error=rotation+rounding;elapsed=Q(0);prices=[]
        for item in normalized:
            width,begin,end,price,diagnostics=channel._piece(kernel,item,mode_bits,exponential_bits)
            join=channel._difference(begin,centre);error+=join+sum(price.values(),Q(0));elapsed+=width
            _require(elapsed<=kernel.source.duration,'source curve exceeds the raw physical duration')
            prices.append({'normalized_duration':str(width),'physical_duration_seconds':str(width/gamma),
                           'join_error':str(join),**{k:str(v) for k,v in price.items()},'modes':diagnostics})
            centre=end
        _require(elapsed==kernel.source.duration,'source curve must cover the full raw physical duration')
        point={(c,i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in centre.items()}
        stop=Q(record['physical_geometry']['normalized_time_numerical_centres']['stop'])
        physical,endpoint_rotation=native._rotate(point,cell,stop,-1,exponential_bits);error+=endpoint_rotation
        initial=channel._read_input(record['source_primitive_input'],joint.DIMENSION)
        norm=bsm._entry_norm(initial,bits=coefficient_bits);bound,detail=_norm_bound(cell,coefficient_bits)
        delta=Q(clock['Gamma_numerical_error']);duration=Q(record['physical_duration_seconds'])
        generator_price=delta*duration*bound*norm
        g=record['physical_geometry']['physical_seconds'];age0=abs(Q(g['start'])-Q(g['field_phase_origin']));age1=abs(Q(g['stop'])-Q(g['field_phase_origin']))
        frequencies=sum((abs(Q(w)) for w in cell['line_carrier_reciprocal_source_units'].values()),Q(0))
        frame_price=4*frequencies*delta*(age0+age1)*norm
        error+=generator_price+frame_price;old=Q(record['upstream_trace_norm_error'])
        observations=channel._observations({key:(v.real.as_rational(),v.imag.as_rational()) for key,v in physical.items()},error+old,kernel.threshold)
        return {'schema':SCHEMA+'/complete-physical-CP-coimage','source_record':record,'untrusted_pieces':_copy(pieces),
            'physical_time':physical_time,'precision':dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits),
            'checker_normalized_pieces':normalized,'physical_counter_endpoint':_counter_record(physical),
            'exact_physical_checker_curve':_exact_physical_pullback(normalized,gamma,mode_bits),
            'exact_physical_checker_curve_is_readout_not_integer_lambda_input':True,
            'old_error_once':str(old),'original_CP_checker_local_error':str(error-generator_price-frame_price),
            'reference_pi_generator_payment':str(generator_price),'reference_pi_endpoint_frame_payment':str(frame_price),
            'reference_source_induced_norm_upper':str(bound),'reference_source_norm_components':detail,
            'global_trace_norm_error':str(old+error),'piece_error_records':prices,'source_columns_checked':len(kernel.columns),
            'source_physical_duration_seconds':record['physical_duration_seconds'],'same_physical_geometry':record['physical_geometry'],
            'full33_pair_and_APD_counter_retained':True,'capture_BG_and_natural_bath_scaled_once':True,
            'old_Ready_reused':False,'pi_numerics_used_as_physical_calibration_error':False,
            'physical_input_curve_is_original_time_equivalent_to_checker_curve':not physical_time,
            'physical_curve_transport_role':'untrusted witness producer; normalized exponents are rounded and the resulting curve is independently residual-checked',
            'reported_endpoint_is_checked_reparametrized_curve_not_original_physical_trial_readout':physical_time,
            'checker_used_original_column_and_piece':True,'solver_executed':False,'controller_advance':False,**observations}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/complete-physical-CP-coimage' and
                 report.get('source_record')==ReferenceAtomicClockSource.record(self),'same reference source physical CP report required')
        expected=ReferenceAtomicClockSource.certify(self,report['untrusted_pieces'],physical_time=report['physical_time'],**report['precision'])
        _require(expected==report,'reference pi/clock/action, complete endpoint or automatic price changed')
        return True

    def first_poll_ready(self,report):
        ReferenceAtomicClockSource.verify(self,report)
        record=ReferenceAtomicClockSource.record(self);geometry=record['physical_geometry']
        seconds=geometry['physical_seconds']
        _require(Q(seconds['stop'])==Q(seconds['next_PC_poll']),
                 'a new Ready must be generated at the original physical PC poll, not at an earlier capture')
        raw=record['normalized_native_assembler']['original_PRM_source'];rule=raw['initial_poll_rule']
        rules={row['name']:row for row in geometry['raw_PC_rules']}
        poll=Q(seconds['stop']);old_count=sum(poll-Q(1,25)<Q(t)<=poll for t in geometry['old_queue_physical_seconds'])
        states=_read_counter(report['physical_counter_endpoint']);ready_state={};pending={};faces=[]
        for count in range(rule['threshold']+1):
            matrix={(i,j):v for (c,i,j),v in states.items() if c==count}
            high=old_count+count>=rule['threshold'];stage=rule['high_next'] if high else rule['low_next']
            changes=rule['high_flags'] if high else rule['low_flags']
            flags=[before if after is None else after for before,after in zip(geometry['loaded_flags'],changes)]
            is_ready=rules[stage]['ready'];target=ready_state if is_ready else pending
            for address,value in matrix.items():
                local._add(target,address,value)
            faces.append({'capped_new_count':count,'rolling_count_at_least_threshold':high,'PC_stage':stage,
                'loaded_flags':flags,'PC_ready':is_ready,'complete_poststate':channel._input_record(matrix)})
        error=Q(report['global_trace_norm_error']);trace=joint._trace(ready_state)
        _require(not trace.imag,'source-issued PC Ready trace must be real')
        mass,rounding=full.radical_midpoint(trace.real,report['precision']['coefficient_bits'])
        lo,hi=max(Q(0),mass-rounding-error),min(Q(1),mass+rounding+error)
        return {'schema':SCHEMA+'/first-physical-PC-ready','source_record':record,'physical_CP_certificate':_copy(report),
            'generated_first_ready_poststate':channel._input_record(ready_state),
            'first_poll_pending_poststate':channel._input_record(pending),'count_faces':faces,
            'first_poll_joint_error':str(error),'source_ready_normalizer':{'centre':str(mass),
                'radical_rounding':str(rounding),'lower':str(lo),'upper':str(hi),'strictly_positive':lo>0,'supplied_by_caller':False},
            'same_physical_geometry':geometry,'whole_native_primitive_and_PC_time_mother':record['normalized_native_assembler'],
            'reference_clock_and_pi_payment_retained':True,'capture_or_hidden_occupancy_used_as_ready':False,
            'old_Ready_reused':False,'native_type_or_old_report_counterfeited':False,
            'latent_new_arrival_queue_measure':'the original shared-APD counter CP curve and its source time law; count centres are not literal arrival timestamps',
            'future_pending_tail_deleted':False,'actual_hardware_parameters_identified':False,'controller_advance':False}

    def verify_first_poll_ready(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/first-physical-PC-ready' and
                 report.get('source_record')==ReferenceAtomicClockSource.record(self),'same physical reference PC-ready report required')
        _require(ReferenceAtomicClockSource.first_poll_ready(self,report['physical_CP_certificate'])==report,
                 'physical PC Ready/pending, normalizer, queue or pi price changed')
        return True


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_atan_inverse,reference_clock,verify_reference_clock,_scale,_read_counter,
        _counter_record,_clock_bounds,_capture_rate_bounds,_exact_physical_pullback,_geometry,_norm_bound,_read_aperture,_centre_initial,_function,_execution,_guard,
        native.NativeToneFrame.record,native.NativeToneFrame.from_record,native.NativeToneFrame.whole_cell,
        native._ConstantSource.__init__,native._ConstantSource.action,native._rotate,native._centre,
        channel.SourceKernel.column,channel.SourceKernel.action,channel.SourceKernel.coefficient_error,
        channel._piece,channel._coefficient,channel._key,channel._add,channel._hermitian,channel._entry_norm,channel._difference,
        channel._observations,channel._initial,channel._read_input,channel._input_record,channel._canonical,
        atomic.MunichAtomicProgramme.from_paid_run,atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.from_record,
        atomic._operator_upper,aperture.ApertureCollectionDomain.record,optical.CommonOpticalReadout.record,
        full.radical_midpoint,full._sqrt,bsm._entry_norm,joint.JointCounterGenerator.action,joint.JointCounterGenerator.record,
        joint.JointCounterGenerator.from_record,joint.JointCounterGenerator._blocks,joint.JointCounterGenerator.detected_action,
        joint.JointCounterGenerator.independent_atomic_action,local.CounterGenerator.atomic_action,local.CounterGenerator._drift,
        local._apply_recycling,persistent._capture_action,native.trap.ReloadSource.from_record,dipole.matrix_adjoint)
    methods=tuple(_function(v) for cls in (ReferenceAtomicClockSource,SourceKernel,_NormalizedSource,_PhysicalSource)
        for v in vars(cls).values() if callable(v) or isinstance(v,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),full.DIMENSION,joint.DIMENSION,registration.D1_REFERENCE_HZ,SCHEMA


def _guard():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED:
        raise ValueError('reference clock executed source closure changed')
    if native._guard is not native._GUARD or native._guard.__code__ is not native._GUARD_CODE:
        raise ValueError('reference clock executed native source closure changed')
    native._GUARD()


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_GUARD,_GUARD_CODE=_guard,_guard.__code__
_EXPECTED=_execution()

"""One Rb87 spectrum/bath generates Munich's optical programme phases.

Laser roles fix resonance centres and nominal commands, while raw amplitudes,
detunings, beam transfers and durations remain inverse coordinates.  All
off-resonant dipoles survive.  Full I/J Zeeman mixing is source-generated;
compilation to the existing diagonal-Segment consumers pays its omission.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import atom_photon_source as photons
import bsm_retry_source as bsm
import bsm_channel as marked
import certified_bsm_programme as certified
import fluorescence_channel as channel
import fluorescence_presence as presence
import joint_fluorescence_presence as joint
import mode_prefix_intake as paid
import optical_multitone as optical
import raw_command_family as commands
import registration_joint_transport as transport
import registration_window_domain as domain
import stopped_bsm_programme as stopped
import window_cem_source as window


BASE = Path(__file__).resolve().parent
SCHEMA = 'stage10-munich-common-atomic-programme/v1'
SPECTRUM_KEYS = ('ground_split', 'D1_split', 'D2_A', 'D2_B', 'D1_reference', 'D2_reference')
MOMENT_KEYS = ('ground', 'D1', 'D2', 'nuclear')
ROLES = {'cooling': ('D2', 2, 3), 'repump': ('D2', 1, 2),
         'pump2to1': ('D2', 2, 1), 'pump1to1': ('D2', 1, 1),
         'excitation': ('D2', 1, 0), 'SI_readout': ('D1', 1, 1)}
KINDS = {'native': ('cooling', 'repump'), 'preparation': ('pump2to1', 'pump1to1'),
         'recooling': ('cooling', 'repump'), 'excitation': ('excitation',)}
ZERO = dipole.ComplexRadical()


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _copy(value):
    return json.loads(json.dumps(value))


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _code():
    names = ('munich_atomic_programme.py', 'atomic_dipole.py', 'atomic_full_forward.py',
             'atom_photon_source.py', 'optical_multitone.py', 'fluorescence_presence.py',
             'joint_fluorescence_presence.py', 'raw_command_family.py', 'stopped_bsm_programme.py',
             'window_cem_source.py', 'registration_joint_transport.py', 'registration_window_domain.py',
             'mode_prefix_intake.py', 'bsm_retry_source.py', 'bsm_channel.py',
             'fluorescence_channel.py', 'certified_bsm_programme.py', 'programme-sources-hp0001.json')
    return {name: hashlib.sha256((BASE/name).read_bytes()).hexdigest() for name in names}


def _public_topology():
    catalogue = json.loads(paid.frozen(BASE/'programme-sources-hp0001.json'))
    _require(catalogue['schema'] == 'stage10-apparatus-programme-sources-hp0001/v1' and
             catalogue['source_identity'] == {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10,
                'whole_ledger_row': 'material row0 retained', 'current_tick': 16, 'next_tick': 17,
                'controller_advance': False}, 'original hp atomic programme catalogue required')
    return {'catalogue': catalogue, 'resonance_roles': {name:list(value) for name,value in ROLES.items()},
            'pump1_command': 'pi', 'pumping_schedule': 'successive direction and pump2 polarization commands alternate',
            'actual_pi_field_requires_raw_transfer': True,
            'photon_emission_preparation': photons.model_metadata()['preparation']}


def _d2_energy(f, a, b):
    k = Q(f*(f+1))-Q(15, 2)
    return a*k/2+b*(Q(3, 4)*k*(k+1)-Q(225, 16))/18


def _energies(spectrum):
    g, d1, a, b, r1, r2 = (spectrum[key] for key in SPECTRUM_KEYS)
    result = {('ground', 1): Q(0), ('ground', 2): g, ('D1', 1): r1,
              ('D1', 2): r1+d1, ('ion', None): Q(0)}
    result.update({('D2', f): r2+_d2_energy(f, a, b)-_d2_energy(3, a, b) for f in (0, 1, 2, 3)})
    return result


def _zeeman(field, moments):
    result = {}
    if not field:
        return result
    spin = dipole.NUCLEAR_SPIN
    for i, left in enumerate(dipole.STATES):
        if left.family == 'ion':
            continue
        jspin = dipole.GROUND_J if left.family == 'ground' else dipole.EXCITED_J[left.family]
        for j, right in enumerate(dipole.STATES):
            if left.family != right.family or left.m != right.m:
                continue
            value = dipole.Radical()
            for twice_m in range(-int(2*jspin), int(2*jspin)+1, 2):
                mj, mi = Q(twice_m, 2), Q(left.m)-Q(twice_m, 2)
                if abs(mi) > spin:
                    continue
                a = dipole.clebsch_gordan(jspin, mj, spin, mi, left.f, left.m)
                b = dipole.clebsch_gordan(jspin, mj, spin, mi, right.f, right.m)
                value += a*b*field*(moments[left.family]*mj+moments['nuclear']*mi)
            if value:
                result[i,j] = dipole.ComplexRadical(value)
    _require(result == dipole.matrix_adjoint(result) and not any(dipole.ION in key for key in result),
             'generated I/J Zeeman source must be Hermitian and preserve the ion sink')
    return result


def _operator_upper(matrix, bits):
    centre, error = full._midpoint_matrix(matrix, bits)
    return full._norm(centre)+full._operator_bound(error)


@lru_cache(maxsize=2)
def _paid_leaf(run):
    _require(type(run) is str and run in ('2016-04-15','2016-06-14'),'original paid raw SI run required')
    prior = domain.paid_joint_domains()
    freeze = prior['prior_full_joint_membership']['science_freeze']
    raw = paid.frozen(BASE/'hardware-inverse-first-hi0002.json',freeze)
    candidate = json.loads(raw)
    return json.dumps({'run':next(r for r in candidate['runs'] if r['run']==run),'raw_template':candidate['raw_template'],
            'geometry':prior['window_geometry'],'MP_science_freeze':freeze,'HI_raw_sha256':hashlib.sha256(raw).hexdigest(),
            'old_static_membership_is_new_dynamic_membership':False},sort_keys=True,separators=(',',':'))


def _matrix_record(matrix):
    return [[i,j,value.serialize()] for (i,j),value in sorted(matrix.items())]


def _read_phase(record):
    owner = MunichAtomicProgramme.from_record(record['parent'])
    result = owner.phase(record['kind'],record['side'],record['duration_seconds'],
                         tuple(Drive.from_record(value) for value in record['drives']))
    _require(result.record()==record,'common atomic phase record mismatch')
    return result


def _counter_price(source, initial, pieces, delta, old_error, precision):
    initial = channel._initial(initial,joint.DIMENSION)
    old_error = full.nonnegative(old_error)
    norm = bsm._entry_norm(initial,bits=precision['coefficient_bits'])
    optical_price, zeeman_price = Q(delta['multitone'])*norm,Q(delta['Zeeman'])*norm
    payment = optical_price+zeeman_price
    raw = channel.certify(source,initial,pieces,upstream_error=old_error+payment,**precision)
    local = Q(raw['trace_norm_error_bound'])-old_error-payment
    _require(local>=0,'original residual checker dropped a source price')
    return {'before_model_trace_norm_error':str(old_error),'input_trace_norm_upper':str(norm),
            'per_unit_model_delta':delta,'multitone_payment':str(optical_price),'Zeeman_payment':str(zeeman_price),
            'source_model_payment':str(payment),'source_checker_local_error':str(local),
            'global_trace_norm_error':raw['trace_norm_error_bound'],'source_certificate':raw,
            'price_transport':'true CP contracts the old Hermitian error once; true-minus-compiled acts on the complete centre',
            'input_positivity_certified_here':False,'physical_probability_requires_positive_source_input':True}


def _gate_instrument_law(source):
    checks=0
    for _,mark in marked.MARK_INVENTORY:
        for port in range(4):
            target=source.target(mark,port)
            _require(mark.receipt is None or target.receipt==mark.receipt,'original receipt must be absorbing')
            checks+=1
    return {'receipt_latch_edges_checked':checks,'raw_source':source.record(),
            'source_law':'original passive detected/unobserved jumps plus independent BG clocks; one TP marked instrument',
            'time_instrument':'freeze quantum evolution on first receipt and retain its event time; pending failure continues to gate end',
            'model_bound':'Duhamel on this CPTP receipt-time/failure direct sum: 2*T*sum(||delta H_s||)*||centre||_1',
            'Hamiltonian_difference_only':True,'same_detected_and_background_CP_maps':True}


def _complex(value):
    if type(value) is dict:
        _require(set(value) == {'real', 'imag'}, 'raw complex-radical coordinate required')
        def part(entries):
            return dipole.Radical({int(root):full.exact(coefficient) for root,coefficient in entries.items()})
        return dipole.ComplexRadical(part(value['real']),part(value['imag']))
    return dipole.complex_exact(value)


class AtomicBase:
    def __init__(self, spectrum, natural_widths, *, magnetic_fields, magnetic_moments,
                 seconds_per_unit, radiation_regime):
        _require(type(spectrum) is dict and set(spectrum) == set(SPECTRUM_KEYS), 'one complete raw hyperfine spectrum required')
        _require(type(natural_widths) is dict and set(natural_widths) == set(full.WIDTHS), 'one complete six-width natural bath required')
        _require(type(magnetic_fields) in (tuple,list) and len(magnetic_fields) == 2 and
                 type(magnetic_moments) is dict and set(magnetic_moments) == set(MOMENT_KEYS),
                 'two explicit side magnetic fields and common electronic/nuclear moments required')
        spectrum = {key:full.exact(spectrum[key]) for key in SPECTRUM_KEYS}
        widths = {key:full.nonnegative(natural_widths[key]) for key in full.WIDTHS}
        _require(all(widths.values()), 'Rb87 natural widths must be strictly positive')
        fields = tuple(map(full.exact,magnetic_fields))
        moments = {key:full.exact(magnetic_moments[key]) for key in MOMENT_KEYS}
        unit = full.exact(seconds_per_unit)
        _require(unit > 0 and radiation_regime in ('coherent_q_F','secular_rank1'), 'one positive unit and explicit common bath resolution required')
        self._frame = {'schema':SCHEMA+'/atomic-base','spectrum':{k:str(v) for k,v in spectrum.items()},
            'natural_widths':[str(widths[key]) for key in full.WIDTHS],
            'magnetic_fields':list(map(str,fields)), 'magnetic_moments':{k:str(v) for k,v in moments.items()},
            'seconds_per_unit':str(unit), 'radiation_regime':radiation_regime,
            'magnetic_frame':'local quantization axis; beam transfers carry its unknown optical orientation',
            'full_Zeeman_model':'B_s*(gJ_family J_z+gI I_z), generated in the coupled |(J I) F m> basis',
            'spectral_frequency_units':'common reciprocal source-time unit',
            'physical_dimension':33, 'actual_atomic_parameters_identified':False,'controller_advance':False,
            'source_code':_code()}
        self._seal = _digest(self._frame)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('common atomic programme execution closure changed')
        _guard()
        _require(type(self) is AtomicBase and set(vars(self)) == {'_frame','_seal'} and
                 _digest(self._frame) == self._seal and self._frame['source_code'] == _code(), 'atomic base snapshot changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls, record):
        _guard()
        _require(cls is AtomicBase and type(record) is dict and record.get('schema') == SCHEMA+'/atomic-base', 'closed common atomic base required')
        result = cls(record['spectrum'],dict(zip(full.WIDTHS,record['natural_widths'])),
            magnetic_fields=record['magnetic_fields'],magnetic_moments=record['magnetic_moments'],
            seconds_per_unit=record['seconds_per_unit'],radiation_regime=record['radiation_regime'])
        _require(result.record() == record,'atomic base record mismatch')
        return result

    def zeeman(self, side):
        _require(type(side) is int and side in (0,1),'original atomic side required')
        record = AtomicBase.record(self)
        return _zeeman(Q(record['magnetic_fields'][side]), {k:Q(v) for k,v in record['magnetic_moments'].items()})

    def off_diagonal_zeeman(self, side):
        return {key:value for key,value in AtomicBase.zeeman(self,side).items() if key[0] != key[1]}

    def segment(self, side, duration, *, ion_rates=None, r=1, c=1):
        record = AtomicBase.record(self)
        energy = _energies({k:Q(v) for k,v in record['spectrum'].items()})
        magnetic = AtomicBase.zeeman(self,side)
        diagonal = {state:-dipole.Radical(energy[state.family,state.f])-magnetic.get((i,i),ZERO).real
                    for i,state in enumerate(dipole.STATES)}
        if all(diagonal[state] == diagonal[next(s for s in dipole.STATES if (s.family,s.f)==(state.family,state.f))]
               for state in dipole.STATES):
            diagonal = {(family,f):diagonal[next(s for s in dipole.STATES if (s.family,s.f)==(family,f))]
                        for family,f in dipole.MANIFOLDS}
        return full.Segment(duration,dict.fromkeys(dipole.Q_COMPONENTS,0),dict.fromkeys(dipole.Q_COMPONENTS,0),r,c,
             diagonal,dict(zip(full.WIDTHS,record['natural_widths'])),
             dict.fromkeys(full.EXCITED,0) if ion_rates is None else ion_rates,
             radiation_regime=record['radiation_regime'],field_convention='absorption_amplitudes')


@dataclass(frozen=True)
class Drive:
    role: str
    beam: str
    amplitude: object
    detuning: Q
    polarization: str

    def __post_init__(self):
        _require(self.role in ROLES and type(self.beam) is str and self.beam,
                 'one public raw laser role and beam identifier required')
        _require(self.polarization in ('pi','sigma+','sigma-','linear_x','linear_y'), 'named nominal polarization command required')
        object.__setattr__(self,'amplitude',_complex(self.amplitude))
        object.__setattr__(self,'detuning',full.exact(self.detuning))
        _require(self.role != 'cooling' or self.detuning < 0, 'public cooling tone must be red-detuned')
        _require(self.role != 'pump1to1' or self.polarization == 'pi','public pump1to1 must use its nominal pi command')

    def record(self):
        return {'role':self.role,'beam':self.beam,'amplitude':self.amplitude.serialize(),
                'detuning':str(self.detuning),'polarization':self.polarization}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and set(record) == {'role','beam','amplitude','detuning','polarization'},'raw laser drive record required')
        return cls(**record)


def _polarization(name):
    half = dipole.sqrt_rational(Q(1,2))
    return {'pi':(0,1,0),'sigma+':(0,0,1),'sigma-':(1,0,0),
            'linear_x':(half,0,-half),'linear_y':(dipole.ComplexRadical(0,half),0,dipole.ComplexRadical(0,half))}[name]


def _transfer(value):
    _require(type(value) in (tuple,list) and len(value)==3 and all(type(row) in (tuple,list) and len(row)==3 for row in value),
             'raw 3x3 beam-to-local-spherical transfer required')
    return tuple(tuple(_complex(v) for v in row) for row in value)


class AtomicPhase:
    def __init__(self, owner, kind, side, duration_seconds, drives):
        _require(type(owner) is MunichAtomicProgramme and kind in KINDS and type(side) is int and side in (0,1),
                 'closed common programme and public atomic phase required')
        _require(type(drives) in (tuple,list) and all(type(d) is Drive for d in drives) and
                 tuple(sorted(d.role for d in drives)) == tuple(sorted(KINDS[kind])), 'complete simultaneous public laser-role inventory required')
        parent = MunichAtomicProgramme.record(owner)
        duration = full.nonnegative(duration_seconds)
        _require(duration > 0,'positive raw physical phase duration required')
        if kind == 'native':
            _require(duration == Q(parent['public_topology']['catalogue']['PRL_SI']['presence_integration_ms'],1000),
                     'native integrated-count duration must equal public 40ms')
        self._frame = {'schema':SCHEMA+'/atomic-phase','parent':parent,'kind':kind,'side':side,
                       'duration_seconds':str(duration),'drives':[d.record() for d in drives],
                       'phase_origin':'raw phase-local complex amplitudes; repeated-window phase transport/reset is a control coordinate'}
        self._seal = _digest(self._frame)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('common atomic programme execution closure changed')
        _guard()
        _require(type(self) is AtomicPhase and set(vars(self))=={'_frame','_seal'} and _digest(self._frame)==self._seal,
                 'common atomic phase snapshot changed')
        return _copy(self._frame)

    def programme(self):
        record = AtomicPhase.record(self)
        owner = MunichAtomicProgramme.from_record(record['parent'])
        base = owner.atomic_base()
        duration = Q(record['duration_seconds'])/Q(base.record()['seconds_per_unit'])
        raw = base.segment(record['side'],duration)
        energies = _energies({k:Q(v) for k,v in base.record()['spectrum'].items()})
        tones = []
        for drive_record in record['drives']:
            drive = Drive.from_record(drive_record)
            _require(drive.beam in record['parent']['beam_transfers'][record['side']], 'laser beam has no same-lambda raw transfer')
            matrix = _transfer(record['parent']['beam_transfers'][record['side']][drive.beam])
            command = _polarization(drive.polarization)
            field = {q:drive.amplitude*sum((_complex(value)*_complex(coefficient) for value,coefficient in zip(row,command)),ZERO)
                     for q,row in zip(dipole.Q_COMPONENTS,matrix)}
            line,f,excited = ROLES[drive.role]
            frequency = energies[line,excited]-energies['ground',f]+drive.detuning
            tones.append(optical.Tone(drive.role,line,frequency,field))
        return optical.Programme(raw,tuple(tones))

    def hamiltonian_derivative_at_zero(self, order=0):
        record=AtomicPhase.record(self)
        programme = AtomicPhase.programme(self)
        matrix = programme.hamiltonian_derivative_at_zero(order)
        if order == 0:
            base = MunichAtomicProgramme.from_record(record['parent']).atomic_base()
            matrix = optical._sum(matrix,base.off_diagonal_zeeman(record['side']))
        return matrix

    def action_derivative_at_zero(self, matrix, order=0):
        record=AtomicPhase.record(self)
        programme = AtomicPhase.programme(self)
        action = programme.action_derivative_at_zero(matrix,order)
        if order == 0:
            base = MunichAtomicProgramme.from_record(record['parent']).atomic_base()
            action = optical._sum(action,optical._commutator(base.off_diagonal_zeeman(record['side']),presence._matrix(matrix)))
        return action

    def compile_grid(self, cuts, *, bits=160):
        record=AtomicPhase.record(self)
        programme = AtomicPhase.programme(self)
        base = MunichAtomicProgramme.from_record(record['parent']).atomic_base()
        omitted = base.off_diagonal_zeeman(record['side'])
        norm = _operator_upper(omitted,bits)
        cells = programme.compile_grid(cuts,bits=bits)
        return {'schema':SCHEMA+'/compiled-phase','source_record':record,
                'original_multitone_programme':programme.record(),'full_Zeeman_off_diagonal':_matrix_record(omitted),
                'omitted_Zeeman_operator_norm_upper':str(norm),
                'cells':[{'original_cell':cell.record(), 'Zeeman_trace_norm_error':str(2*(cell.end-cell.start)*norm),
                          'total_trace_norm_error':str(cell.trace_norm_error+2*(cell.end-cell.start)*norm)} for cell in cells],
                'total_trace_norm_error':str(sum((cell.trace_norm_error for cell in cells),Q(0))+2*programme.base.duration*norm),
                'price_scope':'induced trace norm; multiply by the complete input trace norm; carry once per source cell',
                'unknown_atom_or_prepared_state_supplied':False,'solver_executed':False,'controller_advance':False}

    def verify_compilation(self, report, *, bits=160):
        AtomicPhase.record(self)
        cuts = [Q(report['cells'][0]['original_cell']['start'])]+[Q(c['original_cell']['end']) for c in report['cells']]
        _require(report==AtomicPhase.compile_grid(self,cuts,bits=bits),'common atomic compilation certificate mismatch')
        return True


class MunichAtomicProgramme:
    def __init__(self, base, beam_transfers, *, paid_si_leaf=None):
        _require(type(base) is AtomicBase,'closed source-generated common atomic base required; a target state is not input')
        _require(type(beam_transfers) in (tuple,list) and len(beam_transfers)==2 and
                 all(type(side) is dict and side and all(type(name) is str and name for name in side) for side in beam_transfers),
                 'two raw side/beam transfer inventories required')
        transfers = [{name:[[v.serialize() for v in row] for row in _transfer(matrix)] for name,matrix in side.items()}
                     for side in beam_transfers]
        _require(paid_si_leaf is None or (type(paid_si_leaf) is dict and
                 paid_si_leaf==json.loads(_paid_leaf(paid_si_leaf.get('run',{}).get('run')))),'paid SI leaf differs from frozen original controls')
        if paid_si_leaf is not None:
            original = full.Segment.from_record(paid_si_leaf['raw_template'])
            quiet = base.segment(0,original.duration)
            _require(quiet.gammas==original.gammas and quiet.radiation_regime==original.radiation_regime and
                     Q(base.record()['seconds_per_unit'])==Q(paid_si_leaf['geometry']['seconds_per_source_unit_enclosure'][1]),
                     'paid SI leaf and common base have incompatible widths, bath or unit')
            energy = _energies({k:Q(v) for k,v in base.record()['spectrum'].items()})
            _require(all(dipole.Radical(-energy[key])==original.detunings[key] for key in dipole.MANIFOLDS),
                     'paid SI leaf and common base have incompatible spectra')
        self._frame = {'schema':SCHEMA,'atomic_base':AtomicBase.record(base),'beam_transfers':transfers,
                       'public_topology':_public_topology(),'paid_si_leaf':_copy(paid_si_leaf),
                       'physical_dimension':33,'all_phases_share_spectrum_natural_bath_and_unit':True,
                       'actual_hardware_uniquely_identified':False,'controller_advance':False,'source_code':_code()}
        self._seal = _digest(self._frame)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('common atomic programme execution closure changed')
        _guard()
        _require(type(self) is MunichAtomicProgramme and set(vars(self))=={'_frame','_seal'} and
                 _digest(self._frame)==self._seal and self._frame['source_code']==_code(),'common atomic programme snapshot changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls, record):
        _guard()
        _require(cls is MunichAtomicProgramme and type(record) is dict and record.get('schema')==SCHEMA,'closed common atomic programme required')
        result = cls(AtomicBase.from_record(record['atomic_base']),record['beam_transfers'],paid_si_leaf=record['paid_si_leaf'])
        _require(result.record()==record,'common atomic programme record mismatch')
        return result

    def atomic_base(self):
        return AtomicBase.from_record(MunichAtomicProgramme.record(self)['atomic_base'])

    def phase(self, kind, side, duration_seconds, drives):
        return AtomicPhase(self,kind,side,duration_seconds,drives)

    def pumping_schedule(self, side, steps):
        MunichAtomicProgramme.record(self)
        _require(type(steps) in (tuple,list) and len(steps)>=2,'alternating public pumping steps required')
        phases, previous = [], None
        for duration, drives in steps:
            phase = MunichAtomicProgramme.phase(self,'preparation',side,duration,drives)
            pump = next(d for d in drives if d.role=='pump2to1')
            address = pump.beam,pump.polarization
            _require(previous is None or (address[0]!=previous[0] and address[1]!=previous[1]),
                     'public pumping must alternate directions and polarization commands')
            previous = address
            phases.append(phase)
        return tuple(phases)

    def native_counter_cells(self, first, second, first_cuts, second_cuts, *, threshold, background_rate, collection, bits=160):
        parent=MunichAtomicProgramme.record(self)
        a_record,b_record=AtomicPhase.record(first),AtomicPhase.record(second)
        _require(type(first) is AtomicPhase and type(second) is AtomicPhase and
                 a_record['parent']==parent==b_record['parent'] and
                 (a_record['side'],b_record['side'])==(0,1) and
                 a_record['kind']==b_record['kind']=='native', 'same-base two-side native phases required')
        a,b = AtomicPhase.compile_grid(first,first_cuts,bits=bits),AtomicPhase.compile_grid(second,second_cuts,bits=bits)
        _require([(c['original_cell']['start'],c['original_cell']['end']) for c in a['cells']]==
                 [(c['original_cell']['start'],c['original_cell']['end']) for c in b['cells']], 'native counter cells require the same source-time grid')
        counters = tuple(joint.JointCounterGenerator(full.Segment.from_record(x['original_cell']['raw_segment']),
                 full.Segment.from_record(y['original_cell']['raw_segment']),threshold=threshold,
                 background_rate=background_rate,collection=collection) for x,y in zip(a['cells'],b['cells']))
        return counters, {'schema':SCHEMA+'/native-counter-cells','first':a,'second':b,
                'counter_sources':[counter.record() for counter in counters],
                'model_trace_norm_error':str(Q(a['total_trace_norm_error'])+Q(b['total_trace_norm_error'])),
                'counter_boundary_policy':'transport the same counter across cells; cells do not reset or decide occupancy',
                'shared_APD_collection_and_background_preserved':True,
                'original_40ms_duration_equality_enforced':True,'controller_advance':False}

    def native_cell(self, first, second, cuts, cell_index, *, threshold, background_rate, collection, bits=160):
        parent=MunichAtomicProgramme.record(self)
        a_record,b_record=AtomicPhase.record(first),AtomicPhase.record(second)
        counters,compiled=MunichAtomicProgramme.native_counter_cells(self,first,second,cuts,cuts,threshold=threshold,
                                  background_rate=background_rate,collection=collection,bits=bits)
        _require(type(cell_index) is int and 0<=cell_index<len(counters),'source-generated native cell index required')
        a,b=(compiled[key]['cells'][cell_index] for key in ('first','second'))
        optical_delta=sum((Q(cell['original_cell']['cptp_duhamel_trace_norm_error']) for cell in (a,b)),Q(0))
        zeeman_delta=sum((Q(cell['Zeeman_trace_norm_error']) for cell in (a,b)),Q(0))
        source=counters[cell_index]
        return source, {'schema':SCHEMA+'/owned-native-cell','common_programme':parent,
                'first_phase':a_record,'second_phase':b_record,'cuts':list(map(str,cuts)),
                'cell_index':cell_index,'compilation_bits':bits,'raw_counter_source':source.record(),
                'source_cell_interval':[a['original_cell']['start'],a['original_cell']['end']],
                'per_unit_model_delta':{'multitone':str(optical_delta),'Zeeman':str(zeeman_delta),'total':str(optical_delta+zeeman_delta)},
                'first_cell':a,'second_cell':b,'model_price_scope':'induced trace norm on the whole shared-counter instrument',
                'counter_reset_at_cell_boundary':False,'controller_advance':False}

    def verify_native_cell(self, report):
        parent=MunichAtomicProgramme.record(self)
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/owned-native-cell' and
                 report['common_programme']==parent,'same common owner native cell required')
        source=joint.JointCounterGenerator.from_record(report['raw_counter_source'])
        collection={tuple(item['label']):tuple(tuple(channel._complex_record(v) for v in row) for row in item['matrix'])
                    for item in report['raw_counter_source']['collection']}
        rebuilt,expected=MunichAtomicProgramme.native_cell(self,_read_phase(report['first_phase']),_read_phase(report['second_phase']),
                    report['cuts'],report['cell_index'],threshold=source.threshold,background_rate=source.background_rate,
                    collection=collection,bits=report['compilation_bits'])
        _require(expected==report and rebuilt.record()==source.record(),'source-generated native cell/model delta mismatch')
        return True

    def certify_native_cell(self, first, second, cuts, cell_index, initial, pieces, *, threshold=1,
            background_rate, collection, upstream_error=0, initial_counter=0,
            mode_bits=60, coefficient_bits=160, exponential_bits=160, compilation_bits=160):
        MunichAtomicProgramme.record(self)
        AtomicPhase.record(first);AtomicPhase.record(second)
        source,model=MunichAtomicProgramme.native_cell(self,first,second,cuts,cell_index,threshold=threshold,
                    background_rate=background_rate,collection=collection,bits=compilation_bits)
        _require(type(initial_counter) is int and 0<=initial_counter<=threshold,'original counter input address required')
        precision=dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits,
                       initial_counter=initial_counter)
        priced=_counter_price(source,initial,pieces,model['per_unit_model_delta'],upstream_error,precision)
        return {'schema':SCHEMA+'/certified-native-cell','owned_cell':model,**priced,'controller_advance':False}

    def verify_native_certificate(self, report):
        MunichAtomicProgramme.record(self)
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/certified-native-cell','closed native original-check certificate required')
        model=report['owned_cell']
        MunichAtomicProgramme.verify_native_cell(self,model)
        raw=report['source_certificate']
        source=joint.JointCounterGenerator.from_record(model['raw_counter_source'])
        collection={tuple(item['label']):tuple(tuple(channel._complex_record(v) for v in row) for row in item['matrix'])
                    for item in model['raw_counter_source']['collection']}
        expected=MunichAtomicProgramme.certify_native_cell(self,_read_phase(model['first_phase']),_read_phase(model['second_phase']),
            model['cuts'],model['cell_index'],channel._read_input(raw['initial_state'],joint.DIMENSION),raw['trial_pieces'],
            threshold=source.threshold,background_rate=source.background_rate,collection=collection,
            upstream_error=report['before_model_trace_norm_error'],initial_counter=raw['initial_counter'],
            mode_bits=raw['mode_bits'],coefficient_bits=raw['coefficient_bits'],exponential_bits=raw['exponential_bits'],
            compilation_bits=model['compilation_bits'])
        _require(expected==report,'native original-check/model-price certificate mismatch')
        return True

    def pair_phases(self, first, second, cuts, *, bits=160):
        parent=MunichAtomicProgramme.record(self)
        a_record,b_record=AtomicPhase.record(first),AtomicPhase.record(second)
        _require(type(first) is AtomicPhase and type(second) is AtomicPhase and a_record['parent']==parent==b_record['parent']
                 and (a_record['side'],b_record['side'])==(0,1),'same-base two-side atomic phases required')
        a,b = AtomicPhase.compile_grid(first,cuts,bits=bits),AtomicPhase.compile_grid(second,cuts,bits=bits)
        phases=[]
        for index,(x,y) in enumerate(zip(a['cells'],b['cells'])):
            phase=stopped.RawPairPhase.from_multitone(AtomicPhase.programme(first),AtomicPhase.programme(second),Q(x['original_cell']['start']),
                    Q(x['original_cell']['end']),bits=bits)
            omission=Q(x['Zeeman_trace_norm_error'])+Q(y['Zeeman_trace_norm_error'])
            object.__setattr__(phase,'model_error',phase.model_error+omission)
            object.__setattr__(phase,'origin',{**phase.origin,'common_atomic_owner':parent,
                     'common_atomic_phases':[a_record,b_record],'source_cell_index':index,
                     'additional_Zeeman_trace_norm_error':str(omission)})
            phases.append(phase)
        phases=tuple(phases)
        return phases, {'schema':SCHEMA+'/pair-phases','first':a,'second':b,
                'original_pair_phases':[phase.record() for phase in phases],
                'additional_Zeeman_price':str(sum((Q(c['Zeeman_trace_norm_error']) for v in (a,b) for c in v['cells']),Q(0))),
                'original_multitone_price_already_in_RawPairPhase':True,
                'Zeeman_price_already_in_RawPairPhase':True,
                'persistent_origin_reconstruction':'common owner closed entrance; legacy multitone-only parser rejects this extended origin',
                'controller_advance':False}

    def certify_pair_cell(self, first, second, cuts, cell_index, initial, pieces, *, upstream_error=0,
                          mode_bits=60, coefficient_bits=160, exponential_bits=160, compilation_bits=160):
        parent=MunichAtomicProgramme.record(self)
        a_record,b_record=AtomicPhase.record(first),AtomicPhase.record(second)
        phases,compiled=MunichAtomicProgramme.pair_phases(self,first,second,cuts,bits=compilation_bits)
        _require(type(cell_index) is int and 0<=cell_index<len(phases),'source-generated pair cell index required')
        a,b=(compiled[key]['cells'][cell_index] for key in ('first','second'))
        optical_delta=sum((Q(c['original_cell']['cptp_duhamel_trace_norm_error']) for c in (a,b)),Q(0))
        zeeman_delta=sum((Q(c['Zeeman_trace_norm_error']) for c in (a,b)),Q(0))
        source=joint.JointCounterGenerator(phases[cell_index].first,phases[cell_index].second,
                                          threshold=1,background_rate=0,collection=((0,)*6,))
        priced=_counter_price(source,initial,pieces,{'multitone':str(optical_delta),'Zeeman':str(zeeman_delta),
                    'total':str(optical_delta+zeeman_delta)},upstream_error,
                    dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits))
        return {'schema':SCHEMA+'/certified-pair-cell','common_programme':parent,
                'first_phase':a_record,'second_phase':b_record,'cuts':list(map(str,cuts)),
                'cell_index':cell_index,'compilation_bits':compilation_bits,'raw_pair_phase':phases[cell_index].record(),
                **priced,'controller_advance':False}

    def verify_pair_certificate(self, report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/certified-pair-cell' and
                 report['common_programme']==MunichAtomicProgramme.record(self),'same common owner pair certificate required')
        raw=report['source_certificate']
        expected=MunichAtomicProgramme.certify_pair_cell(self,_read_phase(report['first_phase']),_read_phase(report['second_phase']),
                report['cuts'],report['cell_index'],channel._read_input(raw['initial_state'],joint.DIMENSION),raw['trial_pieces'],
                upstream_error=report['before_model_trace_norm_error'],mode_bits=raw['mode_bits'],
                coefficient_bits=raw['coefficient_bits'],exponential_bits=raw['exponential_bits'],compilation_bits=report['compilation_bits'])
        _require(expected==report,'pair original-check/model-price certificate mismatch')
        return True

    def bsm_gate(self, *, collection_a, collection_b, efficiencies, background_rates, splitter, bits=160):
        parent=MunichAtomicProgramme.record(self)
        base = MunichAtomicProgramme.atomic_base(self)
        unit = Q(base.record()['seconds_per_unit'])
        duration = bsm.GATE_SECONDS/unit
        atoms = tuple(base.segment(side,duration) for side in (0,1))
        source = bsm.BSMSource(*atoms,seconds_per_unit=unit,collection_a=collection_a,collection_b=collection_b,
                    efficiencies=efficiencies,background_rates=background_rates,splitter=splitter)
        omitted = tuple(base.off_diagonal_zeeman(side) for side in (0,1))
        error = sum((2*duration*_operator_upper(matrix,bits) for matrix in omitted),Q(0))
        return source, {'schema':SCHEMA+'/BSM-gate','common_programme':parent,'raw_BSM_source':source.record(),
                'full_Zeeman_off_diagonal':[_matrix_record(matrix) for matrix in omitted],
                'source_model_trace_norm_error':str(error),
                'price_scope':'whole four-pattern receipt/failure instrument; multiply by input trace norm once',
                'public_120ns_duration_equality':str(duration*unit),
                'source_model_price_must_enter_original_residual_checker':True,'controller_advance':False}

    def certify_gate(self, initial, pieces, *, collection_a, collection_b, efficiencies, background_rates,
            splitter, upstream_error=0, mode_bits=60, coefficient_bits=160, exponential_bits=160, compilation_bits=160):
        MunichAtomicProgramme.record(self)
        source,model=MunichAtomicProgramme.bsm_gate(self,collection_a=collection_a,collection_b=collection_b,
            efficiencies=efficiencies,background_rates=background_rates,splitter=splitter,bits=compilation_bits)
        initial=channel._initial(initial,joint.DIMENSION)
        old_error=full.nonnegative(upstream_error)
        norm=bsm._entry_norm(initial,bits=coefficient_bits)
        payment=Q(model['source_model_trace_norm_error'])*norm
        raw=marked.certify(source,initial,pieces,upstream_error=old_error+payment,mode_bits=mode_bits,
                          coefficient_bits=coefficient_bits,exponential_bits=exponential_bits)
        # ReceiptMeasure integrates the checked polynomial curve at the event
        # time.  The terminal Mark poststates are retained separately.
        receipt=certified.ReceiptMeasure(raw,source.interval_start).interval()
        time_local=Q(receipt['local_curve_error'])
        terminal_local=Q(raw['trace_norm_error_bound'])-old_error-payment
        _require(terminal_local>=0,'original BSM checker dropped a source price')
        failure,_=marked.poststate(raw,'failure')
        return {'schema':SCHEMA+'/certified-gate-instrument','common_programme':MunichAtomicProgramme.record(self),
                'gate_model':model,'compilation_bits':compilation_bits,'source_certificate':raw,
                'before_model_trace_norm_error':str(old_error),'input_trace_norm_upper':str(norm),
                'source_model_payment':str(payment),'source_checker_terminal_local_error':str(terminal_local),
                'source_checker_time_local_error':str(time_local),
                'global_trace_norm_error':str(old_error+payment+terminal_local+time_local),
                'first_receipt_event_poststates':[channel._input_record(matrix) for matrix in receipt['poststates']],
                'gate_end_failure_poststate':channel._input_record(failure),
                'first_receipt_time_support':list(map(str,receipt['time_support'])),
                'joint_instrument_source_law':_gate_instrument_law(source),
                'whole_price_scope':'complete first-receipt event-time quantum direct sum plus gate-end failure',
                'old_error_and_source_model_paid_once':True,'local_time_and_terminal_residual_prices_added_separately':True,
                'gate_end_success_not_substituted_for_event_poststate':True,
                'input_positivity_certified_here':False,'controller_advance':False}

    def verify_gate_certificate(self, report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/certified-gate-instrument' and
                 report['common_programme']==MunichAtomicProgramme.record(self),'same common owner BSM instrument required')
        raw=report['source_certificate']
        source=bsm.BSMSource.from_record(raw['raw_source'])
        marked_initial=marked._read_initial(raw['initial_marked_state'])
        _require(all(mark==bsm.INITIAL for mark,_,_ in marked_initial),'fresh original BSM mark inlet required')
        initial={(i,j):value for (_,i,j),value in marked_initial.items()}
        expected=MunichAtomicProgramme.certify_gate(self,initial,raw['trial_pieces'],collection_a=source.collections[0],
             collection_b=source.collections[1],efficiencies=source.efficiencies,background_rates=source.background_rates,
             splitter=source.splitter,upstream_error=report['before_model_trace_norm_error'],
             mode_bits=raw['mode_bits'],coefficient_bits=raw['coefficient_bits'],exponential_bits=raw['exponential_bits'],
             compilation_bits=report['compilation_bits'])
        _require(expected==report,'BSM original-check/joint-time/model-price certificate mismatch')
        return True

    @classmethod
    def from_paid_run(cls, run, beam_transfers, *, magnetic_fields, magnetic_moments):
        _guard()
        _require(cls is MunichAtomicProgramme,'closed common atomic programme factory required')
        leaf = json.loads(_paid_leaf(run))
        raw = full.Segment.from_record(leaf['raw_template'])
        energies = {(family,f):(-raw.detunings[family,f]).as_rational() for family,f in dipole.MANIFOLDS}
        d32,d21 = energies['D2',3]-energies['D2',2],energies['D2',2]-energies['D2',1]
        a=(d32+d21)/5
        spectrum = dict(zip(SPECTRUM_KEYS,(energies['ground',2],energies['D1',2]-energies['D1',1],
                                  a,d32-3*a,energies['D1',1],energies['D2',3])))
        _require(_energies(spectrum)==energies,'paid raw spectrum is incompatible with a common hyperfine base')
        base = AtomicBase(spectrum,raw.gammas,magnetic_fields=magnetic_fields,magnetic_moments=magnetic_moments,
                         seconds_per_unit=leaf['geometry']['seconds_per_source_unit_enclosure'][1],radiation_regime=raw.radiation_regime)
        return cls(base,beam_transfers,paid_si_leaf=leaf)

    def si_window_source(self, settings):
        record = MunichAtomicProgramme.record(self)
        _require(type(settings) is tuple and len(settings)==2 and all(type(v) is int and v in (0,1) for v in settings),
                 'two original SI command settings required')
        _require(record['paid_si_leaf'] is not None,'paid raw SI leaf required; no target SI effect accepted')
        leaf,base = record['paid_si_leaf'],MunichAtomicProgramme.atomic_base(self)
        original = transport.source_for_settings(leaf['run'],full.Segment.from_record(leaf['raw_template']),settings,geometry=leaf['geometry'])
        programmes = transport._side_programs(leaf['run'],full.Segment.from_record(leaf['raw_template']))
        waveforms, sources, error = [], [], Q(0)
        for side,waveform in enumerate(original.waveforms):
            rows = []
            for pulse in waveform:
                raw = base.segment(side,pulse.duration,ion_rates=pulse.ion_rates,r=pulse.r,c=pulse.c)
                rows.append(replace(raw,fields_r=pulse.fields_r,fields_c=pulse.fields_c))
            waveforms.append(tuple(rows))
            omission = 2*original.duration*_operator_upper(base.off_diagonal_zeeman(side),160)
            command = programmes[side][settings[side]].command_trace_norm_error
            error += omission+command
            sources.append({'side':side,'Zeeman_trace_norm_error':str(omission),'command_trace_norm_error':str(command)})
        source = window.WindowCEMSource(*waveforms,registrations=original.registrations,backgrounds=original.backgrounds,
                  logic_deadlines=original.logic_deadlines,seconds_per_unit=Q(base.record()['seconds_per_unit']))
        return source, {'schema':SCHEMA+'/SI-window','common_programme':record,'raw_window_source':source.record(),
                'source_model_trace_norm_error':str(error),'local_prices':sources,
                'SI_C_role':'the paid hypothesis D2 auxiliary field and resolved ion sink; actual optical identity not inferred',
                'same_raw_template_bath_and_spectrum_used':True,'adjoint_modes_are_forward_poststates':False,
                'controller_advance':False,'actual_hardware_uniquely_identified':False}


def _signature():
    functions = (_require,_copy,_digest,_code,_public_topology,_d2_energy,_energies,_zeeman,_operator_upper,_matrix_record,
        _complex,_polarization,_transfer,_read_phase,_counter_price,_gate_instrument_law,_signature,_guard,
        AtomicBase.__init__,AtomicBase.record,AtomicBase.from_record.__func__,
        AtomicBase.zeeman,AtomicBase.off_diagonal_zeeman,AtomicBase.segment,Drive.__init__,Drive.__post_init__,Drive.record,
        Drive.from_record.__func__,AtomicPhase.__init__,AtomicPhase.record,AtomicPhase.programme,
        AtomicPhase.hamiltonian_derivative_at_zero,AtomicPhase.action_derivative_at_zero,AtomicPhase.compile_grid,
        AtomicPhase.verify_compilation,MunichAtomicProgramme.__init__,MunichAtomicProgramme.record,MunichAtomicProgramme.from_record.__func__,
        MunichAtomicProgramme.atomic_base,MunichAtomicProgramme.phase,MunichAtomicProgramme.pumping_schedule,
        MunichAtomicProgramme.native_counter_cells,MunichAtomicProgramme.native_cell,MunichAtomicProgramme.verify_native_cell,
        MunichAtomicProgramme.certify_native_cell,MunichAtomicProgramme.verify_native_certificate,
        MunichAtomicProgramme.pair_phases,MunichAtomicProgramme.certify_pair_cell,MunichAtomicProgramme.verify_pair_certificate,
        MunichAtomicProgramme.from_paid_run.__func__,MunichAtomicProgramme.si_window_source,
        MunichAtomicProgramme.bsm_gate,MunichAtomicProgramme.certify_gate,MunichAtomicProgramme.verify_gate_certificate,
        bsm.BSMSource.__init__,bsm.BSMSource.target,bsm.BSMSource.port_action,bsm.BSMSource.action,
        bsm.BSMSource.success_flux,bsm.BSMSource.blocks,
        getattr(bsm.BSMSource.from_record,'__func__',bsm.BSMSource.from_record),bsm._entry_norm,
        channel.certify,channel._initial,channel._read_input,channel._input_record,
        marked.certify,marked.certify_marked,marked.verify_certificate,marked.poststate,
        certified.ReceiptMeasure.interval,
        dipole.clebsch_gordan,dipole.hamiltonian,dipole.natural_jumps,
        optical.Programme.__init__,optical.Programme.compile_grid,optical.Programme.compile_cell,
        optical.Programme.hamiltonian_derivative_at_zero,optical.Programme.action_derivative_at_zero,
        full._midpoint_matrix,full._norm,full._operator_bound,transport.source_for_settings,transport._side_programs)
    return (tuple((id(f),id(f.__code__)) for f in functions),tuple(SPECTRUM_KEYS),tuple(MOMENT_KEYS),
            id(_paid_leaf),id(_paid_leaf.__wrapped__),id(_paid_leaf.__wrapped__.__code__),
            tuple((k,tuple(v)) for k,v in ROLES.items()),tuple((k,tuple(v)) for k,v in KINDS.items()),
            tuple((s.family,s.f,s.m) for s in dipole.STATES),tuple(dipole.INDEX.items()),
            tuple(full.WIDTHS),tuple(full.EXCITED),dipole.ION,dipole.NUCLEAR_SPIN,dipole.GROUND_J,tuple(dipole.EXCITED_J.items()))


def _guard():
    if not (_signature is _SIGNATURE and _signature.__code__ is _SIGNATURE_CODE and _signature()==_EXPECTED):
        raise ValueError('common atomic programme execution closure changed')


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_GUARD_FUNCTION = _guard
_GUARD_CODE = _guard.__code__
_EXPECTED = _signature()

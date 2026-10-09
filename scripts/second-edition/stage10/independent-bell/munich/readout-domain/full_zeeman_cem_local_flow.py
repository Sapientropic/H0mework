"""The original complete-Z CEM generates its unmarked local CP flow.

Local witnesses use the existing full-column exponential residual.  Terminal
registration is supplied by the independently checked original gate
intertwiner; no desired effect or final state is accepted as source data.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import numpy as np
import fourier_local_phase_source as fourier

import full_zeeman_cem_terminal_reduction as reduction
import full_zeeman_cem_integer_columns as integer_columns
import factorized_local_phase_source as factors

cem = reduction.cem
SCHEMA = 'stage10-full-Z-CEM-source-unmarked-local-flow/v1'
_SOURCE_CHECK, _REDUCTION_CHECK = cem._CHECK, reduction._CHECK
_FOURIER_CHECK = fourier._GUARD
_INTEGER_CHECK = integer_columns._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), Path(cem.__file__), Path(reduction.__file__), Path(cem.channel.__file__),
         Path(factors.__file__),Path(fourier.__file__),Path(integer_columns.__file__))}


def _column_backend(value):
    _require(type(value) is str and value in ('rational', 'integer'),
             'named original local CEM column backend required')
    return value


def _factors(source, initial):
    cem.FullZeemanCEMSource.record(source)
    initial = cem.channel._initial(initial, cem.joint.DIMENSION)
    _require(all((i//33 == cem.dipole.ION) == (j//33 == cem.dipole.ION) and
                 (i%33 == cem.dipole.ION) == (j%33 == cem.dipole.ION) for i, j in initial),
             'original neutral/ION cohort block structure required; coherences are not erased')
    blocks = {}
    for (i, j), value in initial.items():
        occupancy = i//33 != cem.dipole.ION, i%33 != cem.dipole.ION
        blocks.setdefault(occupancy, {})[i, j] = value
    return [(occupancy, *factors._factor_inventory(factors._decompose(matrix)))
            for occupancy, matrix in sorted(blocks.items())]


class _LocalPhase:
    def __init__(self, source, index, side):
        _CHECK()
        _require(type(source) is cem.FullZeemanCEMSource and type(side) is int and side in (0, 1),
                 'same complete-Z source and original local side required')
        self.phase = cem.FullZeemanCEMPhase(source, index)
        self.side = side
        self.duration, self.threshold = self.phase.duration, 0

    def action(self, state):
        _CHECK()
        matrix = {(i, j): value for (count, i, j), value in state.items() if count == 0}
        _require(len(matrix) == len(state), 'unmarked local source has one quantum block')
        atom = self.phase._original.sources[self.side]
        result = atom.atomic_action(matrix)
        for key, value in reduction._commute(self.phase._z[self.side], matrix).items():
            cem.local._add(result, key, value)
        return {(0, i, j): value for (i, j), value in result.items()}


class _Kernel(cem.channel.SourceKernel):
    def __init__(self, source, index, side, bits):
        self.source = _LocalPhase(source, index, side)
        self.dimension, self.threshold, self.bits = cem.full.DIMENSION, 0, bits
        self.columns, self.exact_columns, self.errors = {}, {}, {}


class _StaticColumns:
    def __init__(self, kernel):
        _require(type(kernel) is _Kernel, 'fixed original local CEM kernel required')
        self.kernel, self.bits, self.frequencies = kernel, kernel.bits, ()

    def action(self, component, matrix):
        _require(component == 'static', 'the original CEM phase is one constant source action')
        lifted = {(0, i, j): value for (i, j), value in matrix.items()}
        image = self.kernel.action(lifted)
        price = self.kernel.coefficient_error(lifted)
        image = {(i,j):value for (_,i,j),value in image.items()}
        rounded,quantization=fourier.exact._dyadic_state(image,self.bits)
        return rounded,price+quantization


def _piece(kernel, piece, mode_bits, exponential_bits, column_backend='rational'):
    backend = _column_backend(column_backend)
    _require(type(piece) is dict and set(piece) == {'duration', 'modes'}, 'original local CEM curve piece required')
    modes = []
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode) == {'lambda', 'coefficients'}, 'original local CEM mode required')
        coefficients = []
        for matrix in mode['coefficients']:
            parsed = cem.channel._coefficient(matrix, 1 << mode_bits, kernel)
            coefficients.append([[i, j, int(a*(1 << mode_bits)), int(b*(1 << mode_bits))]
                                 for (_, i, j), (a, b) in sorted(parsed.items())])
        modes.append({'lambda':mode['lambda'],'frequency_word':[],'coefficients':coefficients})
    if backend == 'integer':
        phase = kernel.source.phase
        columns = integer_columns.CEMIntegerColumns(phase.parent, phase.index, kernel.source.side, kernel.bits)
    else:
        columns = _StaticColumns(kernel)
    width, begin, end, prices, diagnostics = fourier._piece(columns,
        {'duration':piece['duration'],'modes':modes}, Q(0), mode_bits, exponential_bits)
    return width, {(0,i,j):v for (i,j),v in begin.items()}, {(0,i,j):v for (i,j),v in end.items()}, prices, diagnostics


def certify_local(source, side, initial, families, *, upstream_error=0,
                  mode_bits=96, coefficient_bits=192, exponential_bits=192, column_backend='rational'):
    backend = _column_backend(column_backend)
    _CHECK(); cem._closed(source)
    _require(type(source) is cem.FullZeemanCEMSource and type(side) is int and side in (0, 1),
             'closed original full-Z CEM source and side required')
    record = cem.FullZeemanCEMSource.record(source)
    initial = cem.channel._initial(initial, cem.full.DIMENSION)
    precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
    cem.window._precisions(**precision)
    centre = {}; rounding = Q(0)
    for (i, j), value in initial.items():
        a, ea = cem.full.radical_midpoint(value.real, coefficient_bits)
        b, eb = cem.full.radical_midpoint(value.imag, coefficient_bits)
        cem.full._add(centre, (0, i, j), a, b); rounding += ea+eb
    phases = source.phases()
    _require(type(families) is list and len(families) == len(phases), 'all original CEM phases require local witnesses')
    price = cem.full.nonnegative(upstream_error)+rounding; records = []
    for phase, pieces in zip(phases, families):
        kernel = _Kernel(source, phase.index, side, coefficient_bits)
        elapsed = Q(0); payments = []
        for piece in pieces:
            width, begin, end, errors, diagnostics = _piece(kernel, piece, mode_bits, exponential_bits, backend)
            join = cem.channel._difference(begin, centre)
            price += join+sum(errors.values(), Q(0)); elapsed += width
            _require(elapsed <= phase.duration, 'local CEM curve crossed an original source phase boundary')
            payments.append({'duration': str(width), 'join': str(join),
                'source_prices': {key:str(value) for key, value in errors.items()}, 'modes': diagnostics})
            centre = end
        _require(elapsed == phase.duration, 'local CEM curve must cover the complete source phase')
        records.append({'phase_index':phase.index, 'source_residual_payments':payments})
    endpoint = {(i, j):cem.dipole.ComplexRadical(a, b) for (_, i, j), (a, b) in centre.items()}
    return {'schema': SCHEMA+'/checked-local-flow', 'source_record':record, 'source_side':side,
        'complete_initial_local_matrix':cem.channel._input_record(initial), 'untrusted_phase_families':cem._copy(families),
        'complete_local_endpoint':cem.channel._input_record(endpoint), 'whole_local_trace_norm_error':str(price),
        'whole_upstream_error_once':str(cem.full.nonnegative(upstream_error)), 'precision':precision,
        'local_column_backend':backend,
        'source_phase_residual_inventory':records, 'background_applied':False, 'registration_applied':False,
        'source_bindings':_bindings(), 'actual_hardware_member_asserted':False, 'controller_advance':False}


def verify_local(source, report):
    initial = cem.channel._read_input(report['complete_initial_local_matrix'], cem.full.DIMENSION)
    expected = certify_local(source, report['source_side'], initial, report['untrusted_phase_families'],
        upstream_error=report['whole_upstream_error_once'], column_backend=report['local_column_backend'], **report['precision'])
    _require(expected == report, 'complete source local CEM curve, endpoint or price changed')
    return expected


def _proposal_endpoint(piece, mode_bits):
    quantum = 1 << mode_bits
    width = float(Q(piece['duration']))
    endpoint = {}
    for mode in piece['modes']:
        lr, li = mode['lambda']
        scalar = np.exp(complex(lr/quantum, li/quantum)*width)
        for _, i, j, a, b in mode['coefficients'][0]:
            endpoint[i, j] = endpoint.get((i, j), 0j)+complex(a/quantum, b/quantum)*scalar
    answer = {}
    for i, j in set(endpoint) | {(j, i) for i, j in endpoint}:
        value = (endpoint.get((i, j), 0j)+endpoint.get((j, i), 0j).conjugate())/2
        _require(np.isfinite(value), 'finite complete local CEM proposal endpoint required')
        a, b = round(float(value.real)*quantum), round(float(value.imag)*quantum)
        if a or b:
            answer[0, i, j] = Q(a, quantum), Q(b, quantum)
    return answer


def generate_local_trials(source, side, initial, *, mode_bits=96, coefficient_bits=192,
                          krylov_dimension=1089):
    _CHECK()
    _require(type(krylov_dimension) is int and 1<=krylov_dimension<=1089,
             'finite local source-frequency proposal budget required')
    initial = cem.channel._initial(initial, cem.full.DIMENSION)
    current = {}
    for (i,j),value in initial.items():
        a,_=cem.full.radical_midpoint(value.real,coefficient_bits)
        b,_=cem.full.radical_midpoint(value.imag,coefficient_bits)
        cem.full._add(current,(0,i,j),a,b)
    quantum=1<<mode_bits; families=[]
    for phase in source.phases():
        kernel=_Kernel(source,phase.index,side,coefficient_bits)
        coordinates=kernel.reachable(tuple(current),max_coordinates=1089)
        index={key:n for n,key in enumerate(coordinates)}
        entries=[(index[out],index[key],complex(float(a),float(b)))
                 for key in coordinates for out,(a,b) in kernel.column(key).items()]
        rows=np.array([a for a,_,_ in entries],dtype=np.int64)
        cols=np.array([b for _,b,_ in entries],dtype=np.int64)
        values=np.array([v for _,_,v in entries],dtype=np.complex128)
        vector=np.array([complex(float(current.get(k,(0,0))[0]),float(current.get(k,(0,0))[1]))
                         for k in coordinates],dtype=np.complex128)
        norm=np.linalg.norm(vector); modes=[]
        if norm:
            maximum=min(krylov_dimension,len(coordinates))
            basis=np.zeros((len(coordinates),maximum+1),dtype=np.complex128)
            hessenberg=np.zeros((maximum+1,maximum),dtype=np.complex128)
            basis[:,0]=vector/norm; used=maximum
            for n in range(maximum):
                image=np.zeros_like(vector);np.add.at(image,rows,values*basis[cols,n])
                for _ in range(2):
                    projections=basis[:,:n+1].conj().T@image
                    hessenberg[:n+1,n]+=projections;image-=basis[:,:n+1]@projections
                residual=np.linalg.norm(image);hessenberg[n+1,n]=residual
                if residual<=1e-13:
                    used=n+1;break
                basis[:,n+1]=image/residual
            exponents,eigenvectors=np.linalg.eig(hessenberg[:used,:used])
            start=np.zeros(used,dtype=np.complex128);start[0]=norm
            amplitudes=(basis[:,:used]@eigenvectors)*np.linalg.solve(eigenvectors,start)
            for exponent,amplitude in zip(exponents,amplitudes.T):
                encoded=[]
                for (count,i,j),value in zip(coordinates,amplitude):
                    a,b=round(float(value.real)*quantum),round(float(value.imag)*quantum)
                    if a or b:encoded.append([count,i,j,a,b])
                lr=min(0.,exponent.real)
                modes.append({'lambda':[round(float(lr)*quantum),round(float(exponent.imag)*quantum)],
                              'coefficients':[encoded]})
        if not modes:
            modes=[{'lambda':[0,0],'coefficients':[[]]}]
        piece={'duration':str(phase.duration),'modes':modes}
        # Candidate generation may use a numerical endpoint.  The independent
        # source checker pays its actual next-piece join; it never trusts this.
        current = _proposal_endpoint(piece, mode_bits)
        families.append([piece])
    return families


def generate_trials(source, initial, **budget):
    return [{'initial_occupancy':list(occupancy),'two_local_factor_inventories':[
        [{'factor_id':item['factor_id'],'untrusted_phase_families':generate_local_trials(source,side,
          cem.channel._read_input(item['initial_local_matrix'],cem.full.DIMENSION),**budget)} for item in items]
        for side,items in enumerate(inventory)]} for occupancy,inventory,_ in _factors(source,initial)]


def image(source, initial, witness_inventory, *, input_error=0,
          mode_bits=96, coefficient_bits=192, exponential_bits=192, column_backend='rational'):
    backend = _column_backend(column_backend)
    _CHECK()
    terminal = reduction.certify(source)
    inventory = _factors(source, initial)
    _require(type(witness_inventory) is list and len(witness_inventory) == len(inventory),
             'all source-generated initial cohort restrictions require local curve inventories')
    geometry = source.geometry_source()
    etas = tuple(1-r.probabilities[0] for r in geometry.registrations)
    price = Q(0); marked = {}; records = []
    precision = dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
    for (occupancy, local_factors, terms), witnesses in zip(inventory, witness_inventory):
        _require(type(witnesses) is dict and set(witnesses) == {'initial_occupancy', 'two_local_factor_inventories'} and
                 witnesses['initial_occupancy'] == list(occupancy), 'original initial cohort identity changed')
        rows = witnesses['two_local_factor_inventories']
        _require(type(rows) is list and len(rows) == 2, 'two original local CEM curve inventories required')
        endpoints = [{}, {}]; certified = [[], []]
        for side, (items, curves) in enumerate(zip(local_factors, rows)):
            _require(type(curves) is list and [row['factor_id'] for row in curves] == [item['factor_id'] for item in items],
                     'complete original Hermitian factor identities required')
            for item, row in zip(items, curves):
                report = certify_local(source, side,
                    cem.channel._read_input(item['initial_local_matrix'], cem.full.DIMENSION),
                    row['untrusted_phase_families'], upstream_error=0, column_backend=backend, **precision)
                matrix = cem.channel._read_input(report['complete_local_endpoint'], cem.full.DIMENSION)
                endpoints[side][item['factor_id']] = matrix, Q(report['whole_local_trace_norm_error'])
                certified[side].append({'factor_id':item['factor_id'], 'complete_local_CEM_certificate':report})
        for first, second in terms:
            a, ea = endpoints[0][first]; b, eb = endpoints[1][second]
            na = factors.bsm._entry_norm(a,bits=coefficient_bits)
            nb = factors.bsm._entry_norm(b,bits=coefficient_bits)
            price += ea*nb+eb*na+ea*eb
            left, right = reduction._mark(a, etas[0], occupancy[0]), reduction._mark(b, etas[1], occupancy[1])
            for (sa, i, j), va in left.items():
                for (sb, k, l), vb in right.items():
                    mark = cem.window.Mark((sa, sb))
                    cem.local._add(marked,(mark,33*i+k,33*j+l),va*vb)
        records.append({'initial_occupancy':list(occupancy),'source_factor_inventory':local_factors,
            'source_tensor_factor_ids':terms,'two_complete_local_CEM_certificates':certified})
    final = geometry.background_action(marked)
    outcomes = [{(i,j):value for (mark,i,j),value in final.items() if mark==selected} for selected in cem.window.MARKS]
    old = cem.full.nonnegative(input_error)
    return {'schema':SCHEMA+'/complete-four-output-image','source_record':source.record(),
        'original_terminal_reduction':terminal,'complete_initial_joint_matrix':cem.channel._input_record(initial),
        'untrusted_witness_inventory':cem._copy(witness_inventory),'source_cohort_factor_certificates':records,
        'complete_four_outcomes':[cem.channel._input_record(matrix) for matrix in outcomes],
        'whole_input_trace_norm_error_once':str(old),'new_local_tensor_error':str(price),
        'whole_four_output_trace_norm_error':str(old+price),'precision':precision,
        'local_column_backend':backend,
        'background_OR_applied_once':True,'initial_ION_registered_as_new_birth':False,
        'local_factor_positivity_assumed':False,'source_model_difference_included':False,
        'source_bindings':_bindings(),'actual_hardware_member_asserted':False,'controller_advance':False}


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    return tuple(map(_function, (_require, _bindings, _column_backend, _factors, certify_local, verify_local,
        generate_local_trials,generate_trials,image, _proposal_endpoint, _function, _signature, _check,
        _LocalPhase.__init__, _LocalPhase.action, _Kernel.__init__, _StaticColumns.__init__, _StaticColumns.action, _piece,
        fourier._piece, fourier._upper_price, fourier.exact._dyadic_state,
        cem.channel._coefficient, cem.channel.SourceKernel.column,
        cem.channel.SourceKernel.action, cem.channel.SourceKernel.coefficient_error, cem.channel._piece,
        cem.channel._difference, cem.FullZeemanCEMSource.record, cem.FullZeemanCEMSource.phases,
        cem.FullZeemanCEMPhase.__init__, reduction._commute, reduction.certify, reduction._mark,
        factors._factor_inventory, factors._decompose, factors.bsm._entry_norm,
        integer_columns.CEMIntegerColumns.__init__, integer_columns.CEMIntegerColumns.column,
        integer_columns.CEMIntegerColumns.action,
        cem.window.WindowCEMSource.background_action))), SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        cem._CHECK is _SOURCE_CHECK and reduction._CHECK is _REDUCTION_CHECK and fourier._GUARD is _FOURIER_CHECK and
        integer_columns._CHECK is _INTEGER_CHECK,
        'original complete-Z local flow execution changed')
    _SOURCE_CHECK(); _REDUCTION_CHECK(); _FOURIER_CHECK(); _INTEGER_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()

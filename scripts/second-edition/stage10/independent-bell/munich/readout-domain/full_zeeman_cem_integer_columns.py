"""The original local CEM source acts on complete matrices on one integer grid.

Source columns include every output.  Radical, column quantization and actual
image quantization are paid separately; the grid does not restrict the law.
"""
from fractions import Fraction as Q

import full_zeeman_cem_source as cem

_SOURCE_CHECK = cem._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _ceil(value):
    return -(-value.numerator//value.denominator)


def _nearest(numerator, denominator):
    value, remainder = divmod(abs(numerator), denominator)
    if 2*remainder > denominator or (2*remainder == denominator and value % 2):
        value += 1
    return -value if numerator < 0 else value


class _UnmarkedLocalSource:
    def __init__(self, source, phase_index, side):
        self.phase = cem.FullZeemanCEMPhase(source, phase_index)
        self.side, self.duration, self.threshold = side, self.phase.duration, 0

    def action(self, state):
        _CHECK()
        ion = cem.dipole.ION
        def address(value):
            return cem.joint.atom_pair_index(value, ion) if self.side == 0 else cem.joint.atom_pair_index(ion, value)
        _require(all(count == 0 for count, _, _ in state), 'one complete local quantum block required')
        lifted = {(cem.window.INITIAL, address(i), address(j)): value
                  for (count, i, j), value in state.items()}
        # Forget only the accepted-bit Mark.  The original full-Z action
        # supplies every birth, natural jump and quantum coherence.
        answer = {}
        for (_, i, j), value in cem.FullZeemanCEMPhase.action(self.phase, lifted).items():
            ia, ib = divmod(i, 33); ja, jb = divmod(j, 33)
            _require((ib == jb == ion) if self.side == 0 else (ia == ja == ion),
                     'original Empty spectator changed under the full source action')
            cem.local._add(answer, (0, ia, ja) if self.side == 0 else (0, ib, jb), value)
        return answer


class _Kernel(cem.channel.SourceKernel):
    def __init__(self, source, phase_index, side, bits):
        self.source = _UnmarkedLocalSource(source, phase_index, side)
        self.dimension, self.threshold, self.bits = 33, 0, bits
        self.columns, self.exact_columns, self.errors = {}, {}, {}


class CEMIntegerColumns:
    def __init__(self, source, phase_index, side, bits=192):
        _CHECK()
        _require(type(source) is cem.FullZeemanCEMSource and type(phase_index) is int and
                 type(side) is int and side in (0, 1) and type(bits) is int and 64 <= bits <= 512,
                 'closed original full-Z source, local phase, side and precision required')
        cem.FullZeemanCEMSource.record(source)
        self.kernel = _Kernel(source, phase_index, side, bits)
        self.bits, self.frequencies = bits, ()
        self._columns = {}

    def column(self, key):
        _CHECK()
        _require(type(key) is tuple and len(key) == 2 and all(type(x) is int and 0 <= x < 33 for x in key),
                 'original local CEM matrix address required')
        if key not in self._columns:
            quantum = 1 << self.bits
            raw = self.kernel.column((0, *key))
            price = self.kernel.errors[(0, *key)]
            rows = []
            for (_, i, j), (a, b) in sorted(raw.items()):
                real = _nearest(a.numerator*quantum, a.denominator)
                imag = _nearest(b.numerator*quantum, b.denominator)
                price += abs(a-Q(real, quantum))+abs(b-Q(imag, quantum))
                if real or imag:
                    rows.append(((i, j), real, imag))
            self._columns[key] = tuple(rows), _ceil(price*quantum)
        return self._columns[key]

    def action(self, component, state):
        _CHECK()
        _require(component == 'static' and type(state) is dict,
                 'one original constant CEM action and a complete dyadic matrix required')
        state_bits = self.bits
        for pair in state.values():
            _require(type(pair) is tuple and len(pair) == 2, 'dyadic complex CEM coefficient pair required')
            for value in pair:
                _require(type(value) in (Q, int), 'exact dyadic CEM coefficient required')
                denominator = Q(value).denominator
                _require(denominator & (denominator-1) == 0 and denominator <= 1 << 512,
                         'CEM coefficient denominator must be a registered power of two')
                state_bits = max(state_bits, denominator.bit_length()-1)
        state_grid = 1 << state_bits
        sums = {}; error = 0
        for key, pair in state.items():
            a, b = (int(Q(v)*state_grid) for v in pair)
            rows, price = self.column(key)
            error += (abs(a)+abs(b))*price
            for out, r, s in rows:
                before = sums.get(out, (0, 0))
                sums[out] = before[0]+a*r-b*s, before[1]+a*s+b*r
        image = {}; quantum = 1 << self.bits
        for key, (a, b) in sums.items():
            real, imag = _nearest(a, state_grid), _nearest(b, state_grid)
            error += abs(a-real*state_grid)+abs(b-imag*state_grid)
            if real or imag:
                image[key] = Q(real, quantum), Q(imag, quantum)
        return image, Q(error, quantum*state_grid)


def _function(value):
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    return tuple(map(_function, (_require, _ceil, _nearest, _function, _signature, _check,
        CEMIntegerColumns.__init__, CEMIntegerColumns.column, CEMIntegerColumns.action,
        _UnmarkedLocalSource.__init__, _UnmarkedLocalSource.action, _Kernel.__init__,
        cem.FullZeemanCEMPhase.action, cem.channel.SourceKernel.column,
        cem.FullZeemanCEMSource.record)))


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             cem._CHECK is _SOURCE_CHECK, 'original CEM integer column execution changed')
    _SOURCE_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()

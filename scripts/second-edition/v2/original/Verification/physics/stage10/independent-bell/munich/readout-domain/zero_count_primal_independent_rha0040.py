"""Independent local TNI primal columns from the raw natural bath and optics."""
from fractions import Fraction as Q
import gaussian_atomic_pulse_source as gaussian
import gaussian_operator_independent_rha0037_1 as independent_operator
import chebyshev_density_rha0032 as basis
import joint_fluorescence_presence as joint


def require(value,reason):
    if not value:raise ValueError(reason)


def local_recycling(original,side,ports):
    field=original['complete_driven_field_source']
    transfer=tuple(tuple(gaussian.channel._complex_record(z) for z in row)
        for row in field['working_common_optical_source']['generated_four_by_six_transfer'])
    _,gram,complement=joint.passive_transfer(tuple(transfer[p] for p in ports))
    require(all(not gram[i][j] for i in range(3) for j in range(3,6)),
            'independent source query requires the coupled generator')
    groups={}
    for item in field['physical_legs'][side]['original_physical_natural_jumps']:
        group=tuple(item['group']);rate=Q(item['physical_amplitude_squared_per_second']);mu=3*side+gaussian.dipole.Q_COMPONENTS.index(item['q'])
        current=groups.setdefault(group,(rate,{}));require(current[0]==rate and mu not in current[1],'raw bath identity changed')
        current[1][mu]=gaussian._matrix(item['normalized_natural_jump_operator'])
    rows=[]
    for group,(rate,modes) in sorted(groups.items()):
        for mu,first in sorted(modes.items()):
            for nu,second in sorted(modes.items()):
                coefficient=rate*complement[nu][mu]
                if coefficient:rows.append({'group':list(group),'mu':mu,'nu':nu,'coefficient_per_second':coefficient.serialize(),
                    'forward_left':gaussian.channel._input_record(first),
                    'forward_right_adjoint':gaussian.channel._input_record(gaussian.dipole.matrix_adjoint(second))})
    return rows


class Columns:
    def __init__(self,record):
        require(record['schema']=='stage10-source-first-receipt-primal-zero-count-flow/rha0040' and
                record['source_clock']=='local_a+u','closed source primal record required')
        self.raw=record;self.bits=record['coefficient_bits'];self.phase_error=Q(0);self.cache={}
        self.k,self.ek,self.v,self.ev=independent_operator.parts({**record,'direction':'forward'})
        self.recycle=[(gaussian.channel._complex_record(r['coefficient_per_second']),
            gaussian._matrix(r['forward_left']),gaussian._matrix(r['forward_right_adjoint']))
            for r in record['complete_unobserved_local_recycling']]

    def column(self,component,key):
        require(component in ('quiet','drive'),'same original primal component required')
        if (component,key) not in self.cache:
            e={key:gaussian.dipole.ComplexRadical(1)}
            k={address:gaussian.dipole.ComplexRadical(*z) for address,z in (self.k if component=='quiet' else self.v).items()}
            result=gaussian.dipole.matrix_product(k,e)
            gaussian.field._add(result,gaussian.dipole.matrix_product(e,gaussian.dipole.matrix_adjoint(k)))
            if component=='quiet':
                for c,left,right in self.recycle:
                    gaussian.field._add(result,gaussian.dipole.matrix_product(gaussian.dipole.matrix_product(left,e),right),c)
            centre,errors=gaussian.full._midpoint_matrix(result,self.bits)
            centre,rounding=basis.density.fourier.exact._dyadic_state(centre,self.bits)
            self.cache[component,key]=centre,sum(errors.values(),Q(0))+rounding+2*(self.ek if component=='quiet' else self.ev)
        return self.cache[component,key]

    def action(self,component,matrix):
        result={};price=Q(0)
        for key,z in matrix.items():
            column,error=self.column(component,key);basis.density.fourier._add_rational(result,column,z)
            price+=(abs(z[0])+abs(z[1]))*error
        return result,price


def scalar(record):
    return {**record['original_Gaussian_source'],'centre_seconds':record['scalar_Gaussian_centre_in_flow_coordinate']}


def piece(record,value,current,elapsed,mode_bits,envelope_order=20):
    return basis.piece(Columns(record),scalar(record),value,current,elapsed,mode_bits,envelope_order)[:3]

from fractions import Fraction as Q
from functools import lru_cache
import copy
import unittest
import late_registered_integral_rha0038_1 as code
import positive_quadrature_rha0038 as quadrature


@lru_cache(maxsize=1)
def grid():
    value=quadrature.propose();return {'grid':value,'checked':quadrature.check(value)}


def constant_program():
    d=code.source.dipole;g=next(i for i,s in enumerate(d.STATES) if s.family=='ground')
    excitations={line:next(i for i,s in enumerate(d.STATES) if s.family==line) for line in ('D1','D2')}
    width=code.source.PIECE_SECONDS;rows=[];same=[[{} for _ in range(4)] for _ in range(2)]
    for line,e in excitations.items():
        jump={(g,e):d.ComplexRadical(Q(1,100))}
        for port in range(4):
            rows.append({'group':[line,1,1],'port':port,'physical_rate_per_second':str(1/width),
                'local_operators':[code.source.channel._input_record(jump)]*2,'local_operator_norm_bounds':['1/100']*2})
            for side in range(2):same[side][port][e,e]=d.ComplexRadical(Q(1,10000))
    return {'schema':code.source.SCHEMA,'all_physical_natural_baths_retained':True,'same_arm_spectator_no_jump_survival_inserted':False,
        'quadrature':grid(),'late_source_operator_errors':['0','0'],
        'late_source_no_jump_tail_prices_with_Gamma_upper':['0','0'],'Gamma_rate_scale_interval':['1','1'],
        'Gamma_relative_error_upper':'0','complete_detected_jump_rows':rows,
        'same_arm_effects_scaled_by_piece_seconds':[[code.source.channel._input_record(m) for m in side] for side in same],
        'relative_line_frequencies_per_second':{'D1':'0','D2':'0'},'original_background_rates_per_second':['0']*4,
        'raised_operator_bases':{line:[[i,j] for i,s in enumerate(d.STATES) for j,t in enumerate(d.STATES)
            if s.family==line and t.family=='ground'] for line in ('D1','D2')}},excitations


class LateRegisteredIntegralControls(unittest.TestCase):
    def test_noncommuting_96bit_effect_projection_covers_exact_Fraction_product(self):
        q=1 << code.B
        g={(0,0):(38876618128911212041002630869,24643573255196467983256448123),
           (0,1):(-37970524647208510856380814483,20301925188936982129626190888),
           (1,0):(-18526469017581737873930746076,34989341908932999935376076042),
           (1,1):(-36918794327207905203520478066,32108370538695231937209830506)}
        r={(0,0):(q//4,0),(1,1):(q//3,0),(0,1):(q//10,q//20),(1,0):(q//10,-(q//20))}
        approximation=code.PricedMatrix(g).adjoint().multiply(code.PricedMatrix(r)).multiply(code.PricedMatrix(g))
        self.assertNotEqual(approximation.centre,code.integer.adjoint(approximation.centre))
        projected,price=code.hermitian_effect(approximation.centre)
        self.assertEqual(projected,code.integer.adjoint(projected));self.assertGreater(price,0)
        def exact_product(a,b):
            answer={}
            for (i,k),(x,y) in a.items():
                for (l,j),(u,v) in b.items():
                    if k!=l:continue
                    c,d=answer.get((i,j),(Q(0),Q(0)));answer[i,j]=c+x*u-y*v,d+x*v+y*u
            return answer
        a={k:(Q(x,q),Q(y,q)) for k,(x,y) in g.items()};b={k:(Q(x,q),Q(y,q)) for k,(x,y) in r.items()}
        exact=exact_product(exact_product(code.integer.adjoint(a),b),a)
        difference=sum((abs(z[0]-Q(projected.get(k,(0,0))[0],q))+abs(z[1]-Q(projected.get(k,(0,0))[1],q)) for k,z in exact.items()),Q(0))
        self.assertLessEqual(difference,approximation.error+price)

    def test_complete_constant_polynomial_integral_and_TP_spectator(self):
        programme,excitations=constant_program();q=1 << code.B
        # Constant matrices test the finite integration, independently of a
        # physical flow certificate. The source constructor admits no such table.
        coefficients=[[[i,i,q//2 if s.family in ('D1','D2') else q,0] for i,s in enumerate(code.source.dipole.STATES)]]+[[]]*64
        piece={'duration_seconds':str(code.source.PIECE_SECONDS),'chebyshev_coefficients':coefficients}
        report=code.integrate_piece(programme,piece,piece,0)
        self.assertEqual(report['numeric_revision'],'rha0038.1')
        self.assertTrue(report['same_arm_Hermitian_projection_priced'])
        for port in report['ports']:
            a={(i,j):(Q(x,q),Q(y,q)) for i,j,x,y in port['same_arm_A']}
            self.assertLess(abs(a[excitations['D2'],excitations['D2']][0]-Q(1,40000)),Q(port['whole_operator_error_upper']))
            self.assertFalse(report['old_inlet_error_applied_to_effect'])
            self.assertEqual(report['source_spectator_reader'],'full TP identity')
            self.assertEqual(len(port['coherent_cross_kernels']),2)
            for kernel in port['coherent_cross_kernels']:
                basis=programme['raised_operator_bases'][kernel['line']]
                index=basis.index([excitations[kernel['line']],next(i for i,s in enumerate(code.source.dipole.STATES) if s.family=='ground')])
                values={(i,j):Q(x,q) for i,j,x,y in kernel['raised_A_lowered_B_coefficients']}
                self.assertLess(abs(values[index,index]-Q(1,40000)),Q(port['whole_operator_error_upper']))

    def test_source_override_is_explicit_and_survival_lookalike_rejected(self):
        programme,_=constant_program();bad=copy.deepcopy(programme);bad['same_arm_spectator_no_jump_survival_inserted']=True
        with self.assertRaises(ValueError):code.integrate_piece(bad,{}, {},0)
        with self.assertRaises(ValueError):code.integrate_piece(programme,{}, {},60)
        with self.assertRaises(ValueError):code.polynomial({'duration_seconds':'1/1000000000','chebyshev_coefficients':[[[0,0,1,0]]]})


if __name__=='__main__':unittest.main()

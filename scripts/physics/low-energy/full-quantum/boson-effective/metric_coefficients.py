#!/usr/bin/env python3
"""Read the true source response and its second algorithm before writing the Lean coefficient consumer."""
import json
import sys
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
a=json.loads((HERE/'dynamic-receipt.json').read_text());b=json.loads((HERE/'cofactor-receipt.json').read_text())
u,q,r=s.symbols('u q r',real=True);names={'u':u,'q':q,'r':r}
response=s.sympify(a['dynamic_metric_inverse_response'],locals=names)
assert s.cancel(response-s.sympify(b['dynamic_metric_inverse_response'],locals=names))==0
n,d=s.fraction(s.cancel(response/(-162*s.sqrt(30)/3125)))
assert all(sum(power)>=2 for poly in [n,d] for power,_ in s.Poly(poly,u,q).terms())

def lean_poly(poly,ray=False):
 terms=[]
 for (pu,pq),coefficient in s.Poly(poly,u,q).terms():
  assert coefficient.is_Integer
  variable='r' if ray else 'u';power=pu+pq-2 if ray else pq
  terms.append(f'({coefficient} : ℝ)'+(f'*{variable}^{pu}' if pu else '')+(f'*q^{power}' if power else ''))
 return '+\n    '.join(terms)
file=ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/BosonEffective/Metric.lean'
text='''import Mathlib.Analysis.SpecialFunctions.Pow.Real\nimport Mathlib.Analysis.SpecialFunctions.Sqrt\nimport Mathlib.Tactic\n\n/-! Coefficients are generated from the exact original dynamic g00 response;\nthe original289/cofactor identity is replayed in boson-effective evidence. -/\nset_option autoImplicit false\nnamespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric\nopen Filter Topology\nnoncomputable section\n\n'''
for name,poly in [('numerator',n),('denominator',d)]:
 text+=f'def {name} (u q : ℝ) : ℝ :=\n  {lean_poly(poly)}\n\n'
 text+=f'def {name}Ray (r q : ℝ) : ℝ :=\n  {lean_poly(poly,True)}\n\n'
text+='''def response (u q : ℝ) : ℝ := (-162*Real.sqrt 30/3125)*(numerator u q/denominator u q)
def rayResponse (r q : ℝ) : ℝ := (-162*Real.sqrt 30/3125)*(numeratorRay r q/denominatorRay r q)
def leading (r : ℝ) : ℝ := 54*Real.sqrt 30*(297*r^2-125)/(3125*(162*r^2-125))

theorem numerator_factor (r q : ℝ) : numerator (r*q) q=q^2*numeratorRay r q := by
  unfold numerator numeratorRay
  ring

theorem denominator_factor (r q : ℝ) : denominator (r*q) q=q^2*denominatorRay r q := by
  unfold denominator denominatorRay
  ring

theorem response_on_ray (r q : ℝ) (nonzero : q≠0) : response (r*q) q=rayResponse r q := by
  rw [response,rayResponse,numerator_factor,denominator_factor]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 nonzero)]

theorem ray_denominator_nonzero (r : ℝ) (regular : 162*r^2-125≠0) : denominatorRay r 0≠0 := by
  have factor : denominatorRay r 0=(-619650000000 : ℝ)*(162*r^2-125) := by
    norm_num [denominatorRay]
    ring
  rw [factor]
  exact mul_ne_zero (by norm_num) regular

theorem ray_value (r : ℝ) (regular : 162*r^2-125≠0) : rayResponse r 0=leading r := by
  unfold rayResponse leading
  have n : numeratorRay r 0=(206550000000 : ℝ)*(297*r^2-125) := by
    norm_num [numeratorRay]
    ring
  have d : denominatorRay r 0=(-619650000000 : ℝ)*(162*r^2-125) := by
    norm_num [denominatorRay]
    ring
  rw [n,d]
  field_simp [regular]
  ring

theorem source_ray_limit (r : ℝ) (regular : 162*r^2-125≠0) :
    Tendsto (fun q : ℝ => response (r*q) q) (𝓝[≠] 0) (𝓝 (leading r)) := by
  have cn : Continuous (numeratorRay r) := by unfold numeratorRay; fun_prop
  have cd : Continuous (denominatorRay r) := by unfold denominatorRay; fun_prop
  have continuous : ContinuousAt (rayResponse r) 0 := by
    exact continuousAt_const.mul (cn.continuousAt.div cd.continuousAt (ray_denominator_nonzero r regular))
  have generated := continuous.tendsto.mono_left (show 𝓝[≠] (0 : ℝ)≤𝓝 0 from inf_le_left)
  rw [ray_value r regular] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with q nonzero
  exact (response_on_ray r q (by simpa using nonzero)).symm

theorem two_directional_limits_differ : leading 0≠leading 1 := by
  norm_num [leading]
  intro same
  have positive : 0<Real.sqrt 30 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric
'''
if '--emit-lean' in sys.argv:
    file.write_text(text)
else:
    assert file.read_text()==text, 'The frozen Lean coefficient consumer differs from the source-generated body.'
lead=s.sympify(a['ray_leading'],locals=names);quad=s.sympify(a['ray_quadratic'],locals=names)
static=s.simplify(lead.subs(r,0));temporal=s.simplify(s.limit(lead,r,s.oo))
assert static==54*s.sqrt(30)/3125 and temporal==99*s.sqrt(30)/3125
report={'scope':'SOURCE_DYNAMIC_METRIC_COFACTOR_AND_DIRECTIONAL_LOW_ENERGY','source_sha256':a['source_sha256'],
 'source_cofactor_and_full289_solution_equal':True,'static_origin_limit':str(static),'time_origin_limit':str(temporal),
 'unequal_limits':True,'ray_leading':str(lead),'ray_second_order':str(quad),
 'leading_low_momentum_divisor':'162 r^2=125; equivalently lambda^2=k^2/3 at leading order; the full denominator has a nonzero q^4 remainder on this line',
 'nonzero_leading_numerator_at_light_pole':str(s.simplify((297*r*r-125).subs(r*r,s.Rational(125,162)))),
 'raw55_local_joint_Taylor_not_used':True}
(HERE/'infrared-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

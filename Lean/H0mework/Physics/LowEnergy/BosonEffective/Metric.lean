import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Coefficients are generated from the exact original dynamic g00 response;
the original289/cofactor identity is replayed in boson-effective evidence. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric
open Filter Topology
noncomputable section

def numerator (u q : ℝ) : ℝ :=
  (114791256000 : ℝ)*u^12+
    (255839634000 : ℝ)*u^10*q^2+
    (2103826115520 : ℝ)*u^10+
    (-2680350750000 : ℝ)*u^8*q^4+
    (-2270560973760 : ℝ)*u^8*q^2+
    (10363221377136 : ℝ)*u^8+
    (-4021106159250 : ℝ)*u^6*q^6+
    (-12678839986320 : ℝ)*u^6*q^4+
    (-5328877751172 : ℝ)*u^6*q^2+
    (42272391780000 : ℝ)*u^6+
    (448242187500 : ℝ)*u^4*q^8+
    (20061010293750 : ℝ)*u^4*q^6+
    (87303386822250 : ℝ)*u^4*q^4+
    (116532077355000 : ℝ)*u^4*q^2+
    (152545506984000 : ℝ)*u^4+
    (1647949218750 : ℝ)*u^2*q^10+
    (21030510937500 : ℝ)*u^2*q^8+
    (48313058078125 : ℝ)*u^2*q^6+
    (-96377802300000 : ℝ)*u^2*q^4+
    (-144501489000000 : ℝ)*u^2*q^2+
    (61345350000000 : ℝ)*u^2+
    (-988769531250 : ℝ)*q^10+
    (-11821044921875 : ℝ)*q^8+
    (-18812578125000 : ℝ)*q^6+
    (62475468750000 : ℝ)*q^4+
    (-25818750000000 : ℝ)*q^2

def numeratorRay (r q : ℝ) : ℝ :=
  (114791256000 : ℝ)*r^12*q^10+
    (255839634000 : ℝ)*r^10*q^10+
    (2103826115520 : ℝ)*r^10*q^8+
    (-2680350750000 : ℝ)*r^8*q^10+
    (-2270560973760 : ℝ)*r^8*q^8+
    (10363221377136 : ℝ)*r^8*q^6+
    (-4021106159250 : ℝ)*r^6*q^10+
    (-12678839986320 : ℝ)*r^6*q^8+
    (-5328877751172 : ℝ)*r^6*q^6+
    (42272391780000 : ℝ)*r^6*q^4+
    (448242187500 : ℝ)*r^4*q^10+
    (20061010293750 : ℝ)*r^4*q^8+
    (87303386822250 : ℝ)*r^4*q^6+
    (116532077355000 : ℝ)*r^4*q^4+
    (152545506984000 : ℝ)*r^4*q^2+
    (1647949218750 : ℝ)*r^2*q^10+
    (21030510937500 : ℝ)*r^2*q^8+
    (48313058078125 : ℝ)*r^2*q^6+
    (-96377802300000 : ℝ)*r^2*q^4+
    (-144501489000000 : ℝ)*r^2*q^2+
    (61345350000000 : ℝ)*r^2+
    (-988769531250 : ℝ)*q^8+
    (-11821044921875 : ℝ)*q^6+
    (-18812578125000 : ℝ)*q^4+
    (62475468750000 : ℝ)*q^2+
    (-25818750000000 : ℝ)

def denominator (u q : ℝ) : ℝ :=
  (103312130400 : ℝ)*u^12+
    (88042059000 : ℝ)*u^10*q^2+
    (-1326196135152 : ℝ)*u^10+
    (-2812927273200 : ℝ)*u^8*q^4+
    (7146135894492 : ℝ)*u^8*q^2+
    (-10666675605312 : ℝ)*u^8+
    (-348356420550 : ℝ)*u^6*q^6+
    (-4054836616488 : ℝ)*u^6*q^4+
    (54877225175424 : ℝ)*u^6*q^2+
    (-29979885888000 : ℝ)*u^6+
    (8566446093750 : ℝ)*u^4*q^8+
    (14320336749875 : ℝ)*u^4*q^6+
    (-13331559163500 : ℝ)*u^4*q^4+
    (-44274070098000 : ℝ)*u^4*q^2+
    (-232960429728000 : ℝ)*u^4+
    (7105914843750 : ℝ)*u^2*q^10+
    (20863513093750 : ℝ)*u^2*q^8+
    (-54526414743750 : ℝ)*u^2*q^6+
    (54793278225000 : ℝ)*u^2*q^4+
    (333108288000000 : ℝ)*u^2*q^2+
    (-100383300000000 : ℝ)*u^2+
    (988769531250 : ℝ)*q^12+
    (3515380859375 : ℝ)*q^10+
    (10071269531250 : ℝ)*q^8+
    (30510703125000 : ℝ)*q^6+
    (-166986562500000 : ℝ)*q^4+
    (77456250000000 : ℝ)*q^2

def denominatorRay (r q : ℝ) : ℝ :=
  (103312130400 : ℝ)*r^12*q^10+
    (88042059000 : ℝ)*r^10*q^10+
    (-1326196135152 : ℝ)*r^10*q^8+
    (-2812927273200 : ℝ)*r^8*q^10+
    (7146135894492 : ℝ)*r^8*q^8+
    (-10666675605312 : ℝ)*r^8*q^6+
    (-348356420550 : ℝ)*r^6*q^10+
    (-4054836616488 : ℝ)*r^6*q^8+
    (54877225175424 : ℝ)*r^6*q^6+
    (-29979885888000 : ℝ)*r^6*q^4+
    (8566446093750 : ℝ)*r^4*q^10+
    (14320336749875 : ℝ)*r^4*q^8+
    (-13331559163500 : ℝ)*r^4*q^6+
    (-44274070098000 : ℝ)*r^4*q^4+
    (-232960429728000 : ℝ)*r^4*q^2+
    (7105914843750 : ℝ)*r^2*q^10+
    (20863513093750 : ℝ)*r^2*q^8+
    (-54526414743750 : ℝ)*r^2*q^6+
    (54793278225000 : ℝ)*r^2*q^4+
    (333108288000000 : ℝ)*r^2*q^2+
    (-100383300000000 : ℝ)*r^2+
    (988769531250 : ℝ)*q^10+
    (3515380859375 : ℝ)*q^8+
    (10071269531250 : ℝ)*q^6+
    (30510703125000 : ℝ)*q^4+
    (-166986562500000 : ℝ)*q^2+
    (77456250000000 : ℝ)

def response (u q : ℝ) : ℝ := (-162*Real.sqrt 30/3125)*(numerator u q/denominator u q)
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

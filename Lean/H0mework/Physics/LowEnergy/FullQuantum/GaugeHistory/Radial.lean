import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Generator

/-! A bounded radial extension preserves the skew source generator on its generated norm sphere. -/
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def boundedRadial (v : E) : E := (1+‖v‖)⁻¹ • v

theorem boundedRadial_norm (v : E) : ‖boundedRadial v‖≤1 := by
  rw [boundedRadial,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact (inv_mul_le_one₀ (by positivity)).mpr (by linarith [norm_nonneg v])

theorem boundedRadial_lipschitz : LipschitzWith 2 (boundedRadial (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have pu : 0<1+‖u‖ := by positivity
  have pv : 0<1+‖v‖ := by positivity
  have decompose : boundedRadial u-boundedRadial v=
      (1+‖u‖)⁻¹ • (u-v)+((1+‖u‖)⁻¹-(1+‖v‖)⁻¹) • v := by
    unfold boundedRadial
    module
  have inverses : |(1+‖u‖)⁻¹-(1+‖v‖)⁻¹|=
      |‖v‖-‖u‖|/((1+‖u‖)*(1+‖v‖)) := by
    rw [inv_sub_inv (ne_of_gt pu) (ne_of_gt pv)]
    simp only [add_sub_add_left_eq_sub,abs_div,abs_mul,abs_of_pos pu,abs_of_pos pv]
  have first : (1+‖u‖)⁻¹ * ‖u-v‖≤‖u-v‖ := by
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (inv_le_one₀ pu).mpr (by linarith [norm_nonneg u])
  have second : (|‖v‖-‖u‖|/((1+‖u‖)*(1+‖v‖)))*‖v‖≤‖u-v‖ := by
    have diff := abs_norm_sub_norm_le v u
    rw [norm_sub_rev v u] at diff
    have denominator : ‖v‖≤(1+‖u‖)*(1+‖v‖) := by nlinarith [norm_nonneg u,norm_nonneg v]
    calc
      _≤(‖u-v‖/((1+‖u‖)*(1+‖v‖)))*‖v‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right diff (by positivity)) (norm_nonneg v)
      _=‖u-v‖*(‖v‖/((1+‖u‖)*(1+‖v‖))) := by ring
      _≤‖u-v‖ := mul_le_of_le_one_right (norm_nonneg _) ((div_le_one (mul_pos pu pv)).mpr denominator)
  rw [dist_eq_norm,dist_eq_norm,decompose]
  calc
    _≤‖(1+‖u‖)⁻¹ • (u-v)‖+‖((1+‖u‖)⁻¹-(1+‖v‖)⁻¹) • v‖ := norm_add_le _ _
    _=(1+‖u‖)⁻¹ * ‖u-v‖+(|‖v‖-‖u‖|/((1+‖u‖)*(1+‖v‖)))*‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr pu.le),Real.norm_eq_abs,inverses]
    _≤2*‖u-v‖ := by linarith

def sphereField (perturbation : ℝ → E →L[ℂ] E)
    (epsilon : ℝ) (initial : E) (time : ℝ) (v : E) : E :=
  generator perturbation epsilon time ((1+‖initial‖) • boundedRadial v)

theorem sphereField_norm (perturbation : ℝ → E →L[ℂ] E)
    (epsilon : ℝ) (initial v : E) (time : ℝ) :
    ‖sphereField perturbation epsilon initial time v‖≤|epsilon| * ‖perturbation time‖*(1+‖initial‖) := by
  apply (generator_bound perturbation epsilon time _).trans
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  exact mul_le_of_le_one_right (by positivity) (boundedRadial_norm v)

theorem sphereField_parallel (perturbation : ℝ → E →L[ℂ] E)
    (epsilon : ℝ) (initial v : E) (time : ℝ) :
    sphereField perturbation epsilon initial time v=
      generator perturbation (epsilon*((1+‖initial‖)/(1+‖v‖))) time v := by
  change (-Complex.I*(epsilon : ℂ)) • perturbation time
      ((1+‖initial‖) • ((1+‖v‖)⁻¹ • v))=_
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,smul_smul,generator,smul_apply]
  congr 1
  push_cast
  ring_nf
  rfl

theorem sphereField_on_sphere (perturbation : ℝ → E →L[ℂ] E)
    (epsilon : ℝ) (initial v : E) (time : ℝ) (same : ‖v‖=‖initial‖) :
    sphereField perturbation epsilon initial time v=generator perturbation epsilon time v := by
  rw [sphereField_parallel,same,div_self (by positivity),mul_one]


theorem sphereField_lipschitz (perturbation : ℝ → E →L[ℂ] E)
    (epsilon : ℝ) (initial : E) (time : ℝ) (K : ℝ≥0) (bounded : ‖perturbation time‖≤K) :
    LipschitzWith (‖epsilon‖₊*K*(1+‖initial‖₊)*2) (sphereField perturbation epsilon initial time) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_add,coe_nnnorm,NNReal.coe_ofNat,NNReal.coe_one,Real.norm_eq_abs]
  rw [sphereField,sphereField,← map_sub,← smul_sub]
  have radial := boundedRadial_lipschitz.dist_le_mul u v
  simp only [dist_eq_norm,NNReal.coe_ofNat] at radial
  calc
    _≤|epsilon| * ‖perturbation time‖*‖(1+‖initial‖) • (boundedRadial u-boundedRadial v)‖ :=
      generator_bound perturbation epsilon time _
    _=|epsilon| * ‖perturbation time‖*((1+‖initial‖)*‖boundedRadial u-boundedRadial v‖) := by
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    _≤|epsilon| * (K : ℝ)*((1+‖initial‖)*(2*‖u-v‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left bounded (abs_nonneg epsilon))
        (mul_le_mul_of_nonneg_left radial (by positivity)) (by positivity) (by positivity)
    _=_ := by ring

theorem sphereField_continuous (perturbation : ℝ → E →L[ℂ] E)
    (continuousPerturbation : ∀ v, Continuous (fun t => perturbation t v)) (epsilon : ℝ) (initial v : E) :
    Continuous (fun t => sphereField perturbation epsilon initial t v) :=
  generator_continuous perturbation continuousPerturbation epsilon _

variable [CompleteSpace E]

theorem sphere_curve_norm (perturbation : ℝ → E →L[ℂ] E)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon delta : ℝ) (initial : E)
    (curve : ℝ → E) (evolves : ∀ t ∈ Ioo (-delta) delta,
      HasDerivAt curve (sphereField perturbation epsilon initial t (curve t)) t)
    (first second : ℝ) (inFirst : first ∈ Ioo (-delta) delta) (inSecond : second ∈ Ioo (-delta) delta) :
    ‖curve first‖=‖curve second‖ := by
  have squared (t : ℝ) (inside : t ∈ Ioo (-delta) delta) : HasDerivAt (fun s => ‖curve s‖^2) 0 t := by
    have generated := evolves t inside
    rw [sphereField_parallel] at generated
    exact norm_derivative perturbation symmetric _ t curve generated
  have constant := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-delta) delta).isPreconnected
    (fun t inside => (squared t inside).differentiableAt.differentiableWithinAt)
    (fun t inside => (squared t inside).deriv) inFirst inSecond
  nlinarith [norm_nonneg (curve first),norm_nonneg (curve second)]

theorem sphere_curve_original (perturbation : ℝ → E →L[ℂ] E)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon delta start : ℝ)
    (initial : E) (curve : ℝ → E) (located : start ∈ Ioo (-delta) delta)
    (starts : curve start=initial) (evolves : ∀ t ∈ Ioo (-delta) delta,
      HasDerivAt curve (sphereField perturbation epsilon initial t (curve t)) t) :
    ∀ t ∈ Ioo (-delta) delta,
      HasDerivAt curve (generator perturbation epsilon t (curve t)) t := by
  intro t inside
  have norm := sphere_curve_norm perturbation symmetric epsilon delta initial curve evolves t start inside located
  rw [starts] at norm
  have generated := evolves t inside
  rwa [sphereField_on_sphere perturbation epsilon initial (curve t) t norm] at generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory

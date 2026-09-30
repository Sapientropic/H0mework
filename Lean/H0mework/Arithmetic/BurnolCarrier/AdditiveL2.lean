import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import H0mework.Arithmetic.BurnolCarrier.AdditiveCoSum

/-!
# Positive and full-line L² realizations of the Burnol additive co-sum

The additive co-sum is first placed in positive-half Lebesgue `L²` by the
actual half-density change of variables

`H(x) = exp (x / 2) * F(exp x)`.

The already proved reciprocal identity identifies this function pointwise
with one half of the reflected modified-Poisson log orbit.  Its `L²`
integrability therefore comes from the source-owned log orbit; exponential
change of variables then returns `F` itself on `(0, ∞)`.  No integrability,
Fourier equality, or physical landing is accepted as input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal SchwartzMap InnerProductSpace

noncomputable section

abbrev BurnolPositiveL2 : Type :=
  Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioi 0))

/-- The positive-variable half-density in additive logarithmic coordinates.
This definition is made from the additive co-sum, not from the existing log
orbit. -/
def burnolAdditivePositiveHalfDensity (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * burnolAdditiveCoSum (Real.exp x)

private theorem complexExp_cpow_half (x : ℝ) :
    (Real.exp x : ℂ) ^ (1 / 2 : ℂ) =
      (Real.exp (x / 2) : ℂ) := by
  calc
    _ = ((Real.exp x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos x).le (1 / 2 : ℝ) using 1
      all_goals norm_num
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
      congr 1
      ring

/-- Pointwise commuting law for the half-density chart.  Reflection is
forced by the reciprocal coordinate `t = exp x`: the additive chart at `x`
reads the existing modified-Poisson log orbit at `-x`. -/
theorem burnolAdditivePositiveHalfDensity_eq_logOrbit (x : ℝ) :
    burnolAdditivePositiveHalfDensity x =
      (1 / 2 : ℂ) *
        coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (-x) := by
  have bridge := coPoissonLogOrbitMap_reciprocal_eq_additiveCoSum
    (t := Real.exp x) (Real.exp_pos x)
  rw [Real.log_inv, Real.log_exp] at bridge
  have inverseHalf :
      (Real.exp x : ℂ)⁻¹ ^ (1 / 2 : ℂ) =
        (Real.exp (-x / 2) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg, complexExp_cpow_half]
  rw [inverseHalf] at bridge
  have expProduct :
      (Real.exp (-x / 2) : ℂ) * (Real.exp x : ℂ) =
        (Real.exp (x / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    burnolAdditivePositiveHalfDensity x =
        (Real.exp (x / 2) : ℂ) *
          burnolAdditiveCoSum (Real.exp x) := rfl
    _ = ((Real.exp (-x / 2) : ℂ) * (Real.exp x : ℂ)) *
          burnolAdditiveCoSum (Real.exp x) := by rw [expProduct]
    _ = (1 / 2 : ℂ) *
        ((Real.exp (-x / 2) : ℂ) *
          (((2 * Real.exp x : ℝ) : ℂ) *
            burnolAdditiveCoSum (Real.exp x))) := by
      push_cast
      ring
    _ = (1 / 2 : ℂ) *
        coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (-x) := by
      rw [bridge]

theorem burnolAdditivePositiveHalfDensity_measurable :
    Measurable burnolAdditivePositiveHalfDensity := by
  rw [show burnolAdditivePositiveHalfDensity = fun x : ℝ =>
      (1 / 2 : ℂ) *
        coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (-x) by
    funext x
    exact burnolAdditivePositiveHalfDensity_eq_logOrbit x]
  exact Measurable.mul measurable_const
    ((coPoissonLogOrbitMap_measurable burnolEvenAnnulusSchwartz).comp
      measurable_neg)

/-- The half-density is in full logarithmic `L²`, derived from the existing
source-owned co-Poisson energy realization. -/
theorem burnolAdditivePositiveHalfDensity_memLp :
    MemLp burnolAdditivePositiveHalfDensity 2
      (volume : Measure ℝ) := by
  have reflected :=
    (coPoissonLogOrbitMap_memLp burnolEvenAnnulusSchwartz).comp_measurePreserving
      negMeasurePreserving
  change MemLp (fun x : ℝ =>
    coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (-x)) 2
      (volume : Measure ℝ) at reflected
  have scaled := reflected.const_smul (1 / 2 : ℂ)
  exact (memLp_congr_ae <| ae_of_all (volume : Measure ℝ) fun x =>
    burnolAdditivePositiveHalfDensity_eq_logOrbit x).mpr scaled

/-- A measurable reconstruction of the additive co-sum from its
half-density.  Only its restriction to `(0, ∞)` is used. -/
def burnolAdditivePositiveReconstruction (t : ℝ) : ℂ :=
  (Real.exp (-Real.log t / 2) : ℂ) *
    burnolAdditivePositiveHalfDensity (Real.log t)

theorem burnolAdditivePositiveReconstruction_eq
    {t : ℝ} (positive : 0 < t) :
    burnolAdditivePositiveReconstruction t =
      burnolAdditiveCoSum t := by
  have expProduct :
      (Real.exp (-Real.log t / 2) : ℂ) *
          (Real.exp (Real.log t / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -Real.log t / 2 + Real.log t / 2 = 0 by ring,
      Real.exp_zero]
    norm_num
  unfold burnolAdditivePositiveReconstruction
  rw [burnolAdditivePositiveHalfDensity, Real.exp_log positive]
  calc
    (Real.exp (-Real.log t / 2) : ℂ) *
        ((Real.exp (Real.log t / 2) : ℂ) * burnolAdditiveCoSum t) =
      ((Real.exp (-Real.log t / 2) : ℂ) *
        (Real.exp (Real.log t / 2) : ℂ)) * burnolAdditiveCoSum t :=
        mul_assoc _ _ _ |>.symm
    _ = burnolAdditiveCoSum t := by rw [expProduct, one_mul]

theorem burnolAdditivePositiveReconstruction_measurable :
    Measurable burnolAdditivePositiveReconstruction := by
  unfold burnolAdditivePositiveReconstruction
  apply Measurable.mul
  · fun_prop
  · exact burnolAdditivePositiveHalfDensity_measurable.comp
      Real.measurable_log

theorem burnolAdditiveCoSum_aestronglyMeasurable_positive :
    AEStronglyMeasurable burnolAdditiveCoSum
      ((volume : Measure ℝ).restrict (Ioi 0)) := by
  refine burnolAdditivePositiveReconstruction_measurable.aestronglyMeasurable.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
  exact burnolAdditivePositiveReconstruction_eq positive

private theorem integrableOn_exp_weight_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      Integrable (fun x : ℝ => Real.exp x * g (Real.exp x)) := by
  have change :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun _ _ _ _ equality => Real.exp_injective equality) g
  simpa only [image_univ, Real.range_exp,
    abs_of_pos (Real.exp_pos _), smul_eq_mul,
    integrableOn_univ] using change

private theorem burnolAdditivePositiveHalfDensity_sq_norm (x : ℝ) :
    ‖burnolAdditivePositiveHalfDensity x‖ ^ 2 =
      Real.exp x * ‖burnolAdditiveCoSum (Real.exp x)‖ ^ 2 := by
  rw [burnolAdditivePositiveHalfDensity, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos (x / 2)).le,
    mul_pow,
    ← Real.exp_nat_mul]
  congr 2
  ring

/-- Positive-half Lebesgue `L²` is generated by the log-orbit `L²` theorem
and the exact exponential Jacobian. -/
theorem burnolAdditiveCoSum_memLp_positive :
    MemLp burnolAdditiveCoSum 2
      ((volume : Measure ℝ).restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    burnolAdditiveCoSum_aestronglyMeasurable_positive).mpr
  have chartIntegrable : Integrable
      (fun x : ℝ => ‖burnolAdditivePositiveHalfDensity x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      burnolAdditivePositiveHalfDensity_measurable.aestronglyMeasurable).mp
        burnolAdditivePositiveHalfDensity_memLp
  have weightedIntegrable : Integrable (fun x : ℝ =>
      Real.exp x * ‖burnolAdditiveCoSum (Real.exp x)‖ ^ 2) :=
    chartIntegrable.congr <| ae_of_all (volume : Measure ℝ) fun x =>
      burnolAdditivePositiveHalfDensity_sq_norm x
  exact (integrableOn_exp_weight_iff
    (fun t : ℝ => ‖burnolAdditiveCoSum t‖ ^ 2)).mpr
      weightedIntegrable

/-- Concrete positive-half `L²` realization of Burnol's additive co-sum. -/
def burnolAdditivePositiveL2 : BurnolPositiveL2 :=
  burnolAdditiveCoSum_memLp_positive.toLp burnolAdditiveCoSum

theorem burnolAdditivePositiveL2_coeFn :
    (burnolAdditivePositiveL2 : ℝ → ℂ) =ᵐ[
      (volume : Measure ℝ).restrict (Ioi 0)] burnolAdditiveCoSum :=
  MemLp.coeFn_toLp burnolAdditiveCoSum_memLp_positive

/-- The logarithmic half-density as an actual `L²(ℝ)` value. -/
def burnolAdditiveHalfDensityL2 : BurnolL2 :=
  burnolAdditivePositiveHalfDensity_memLp.toLp
    burnolAdditivePositiveHalfDensity

theorem burnolAdditiveHalfDensityL2_coeFn :
    (burnolAdditiveHalfDensityL2 : ℝ → ℂ) =ᵐ[volume]
      burnolAdditivePositiveHalfDensity :=
  MemLp.coeFn_toLp burnolAdditivePositiveHalfDensity_memLp

/-- `L²` commuting square: the additive half-density is exactly one half of
the reflected existing modified-Poisson energy value. -/
theorem burnolAdditiveHalfDensityL2_eq_reflectedLogOrbit :
    burnolAdditiveHalfDensityL2 =
      (1 / 2 : ℂ) • reflectL2
        (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz) := by
  apply Lp.ext
  have energyAtNeg := negMeasurePreserving.quasiMeasurePreserving.ae
    (coPoissonLogOrbitEnergyMap_coeFn burnolEvenAnnulusSchwartz)
  filter_upwards [
    burnolAdditiveHalfDensityL2_coeFn,
    Lp.coeFn_smul (1 / 2 : ℂ)
      (reflectL2
        (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz)),
    Lp.coeFn_compMeasurePreserving
      (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz)
      negMeasurePreserving,
    energyAtNeg] with x hhalf hsmul href henergy
  calc
    burnolAdditiveHalfDensityL2 x =
        burnolAdditivePositiveHalfDensity x := hhalf
    _ = (1 / 2 : ℂ) *
        coPoissonLogOrbitMap burnolEvenAnnulusSchwartz (-x) :=
      burnolAdditivePositiveHalfDensity_eq_logOrbit x
    _ = (1 / 2 : ℂ) *
        coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz (-x) := by
      rw [henergy.symm]
    _ = (1 / 2 : ℂ) *
        reflectL2
          (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz) x := by
      change (1 / 2 : ℂ) *
          coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz (-x) =
        (1 / 2 : ℂ) *
          (Lp.compMeasurePreserving (fun y : ℝ => -y)
            negMeasurePreserving
            (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz)) x
      rw [href]
      simp only [Function.comp_apply]
    _ = ((1 / 2 : ℂ) • reflectL2
          (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz)) x :=
      hsmul.symm

private theorem integral_exp_weight (g : ℝ → ℂ) :
    (∫ x : ℝ, Real.exp x • g (Real.exp x)) =
      ∫ t : ℝ in Ioi 0, g t := by
  have change :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun _ _ _ _ equality => Real.exp_injective equality) g
  simpa only [image_univ, Real.range_exp,
    abs_of_pos (Real.exp_pos _), setIntegral_univ] using change.symm

private theorem burnolAdditivePositiveHalfDensity_inner_self (x : ℝ) :
    inner ℂ (burnolAdditivePositiveHalfDensity x)
        (burnolAdditivePositiveHalfDensity x) =
      Real.exp x • inner ℂ
        (burnolAdditiveCoSum (Real.exp x))
        (burnolAdditiveCoSum (Real.exp x)) := by
  simp only [inner_self_eq_norm_sq_to_K, Complex.real_smul]
  have equality := congrArg Complex.ofReal
    (burnolAdditivePositiveHalfDensity_sq_norm x)
  simp only [Complex.ofReal_pow, Complex.ofReal_mul] at equality
  convert equality using 1 <;> rfl

private theorem burnolAdditiveHalfDensity_inner_eq_positive :
    inner ℂ burnolAdditiveHalfDensityL2 burnolAdditiveHalfDensityL2 =
      inner ℂ burnolAdditivePositiveL2 burnolAdditivePositiveL2 := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ x : ℝ, inner ℂ (burnolAdditiveHalfDensityL2 x)
        (burnolAdditiveHalfDensityL2 x)) =
      ∫ x : ℝ, inner ℂ (burnolAdditivePositiveHalfDensity x)
        (burnolAdditivePositiveHalfDensity x) := by
      apply integral_congr_ae
      filter_upwards [burnolAdditiveHalfDensityL2_coeFn] with x equality
      rw [equality]
    _ = ∫ x : ℝ, Real.exp x • inner ℂ
        (burnolAdditiveCoSum (Real.exp x))
        (burnolAdditiveCoSum (Real.exp x)) := by
      apply integral_congr_ae
      exact ae_of_all (volume : Measure ℝ) fun x =>
        burnolAdditivePositiveHalfDensity_inner_self x
    _ = ∫ t : ℝ in Ioi 0, inner ℂ
        (burnolAdditiveCoSum t) (burnolAdditiveCoSum t) :=
      integral_exp_weight fun t => inner ℂ
        (burnolAdditiveCoSum t) (burnolAdditiveCoSum t)
    _ = ∫ t : ℝ, inner ℂ (burnolAdditivePositiveL2 t)
        (burnolAdditivePositiveL2 t)
          ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
      apply integral_congr_ae
      filter_upwards [burnolAdditivePositiveL2_coeFn] with t equality
      rw [equality]

/-- Exact concrete isometry: the positive-half additive realization and its
logarithmic half-density have identical `L²` norms. -/
theorem burnolAdditiveHalfDensityL2_norm_eq_positiveL2 :
    ‖burnolAdditiveHalfDensityL2‖ = ‖burnolAdditivePositiveL2‖ := by
  have squaresEqual : ‖burnolAdditiveHalfDensityL2‖ ^ 2 =
      ‖burnolAdditivePositiveL2‖ ^ 2 := by
    calc
      ‖burnolAdditiveHalfDensityL2‖ ^ 2 =
          (inner ℂ burnolAdditiveHalfDensityL2
            burnolAdditiveHalfDensityL2).re :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (inner ℂ burnolAdditivePositiveL2
          burnolAdditivePositiveL2).re :=
        congrArg Complex.re burnolAdditiveHalfDensity_inner_eq_positive
      _ = ‖burnolAdditivePositiveL2‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  nlinarith [norm_nonneg burnolAdditiveHalfDensityL2,
    norm_nonneg burnolAdditivePositiveL2]

/-- The source-owned normalized log-orbit readout. -/
def burnolAdditiveNormalizedLogOrbitL2 : BurnolL2 :=
  (1 / 2 : ℂ) • reflectL2
    (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz)

theorem burnolAdditiveNormalizedLogOrbitL2_eq_halfDensity :
    burnolAdditiveNormalizedLogOrbitL2 =
      burnolAdditiveHalfDensityL2 :=
  burnolAdditiveHalfDensityL2_eq_reflectedLogOrbit.symm

/-- The half-density change of variables is isometric after the exact
full-line factor `1/2` forced by the even integer normalization. -/
theorem burnolAdditiveNormalizedLogOrbitL2_norm_eq_positiveL2 :
    ‖burnolAdditiveNormalizedLogOrbitL2‖ =
      ‖burnolAdditivePositiveL2‖ := by
  rw [burnolAdditiveNormalizedLogOrbitL2_eq_halfDensity,
    burnolAdditiveHalfDensityL2_norm_eq_positiveL2]

end


end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

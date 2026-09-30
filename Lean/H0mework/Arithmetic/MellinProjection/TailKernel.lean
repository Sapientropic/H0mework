import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusClosedRange
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Positive-radius completed-Mellin tail kernel

This is the radius-parametrized source for the completed-Mellin tail and
constant-gap coefficient.  The historical quarter-radius declarations are
specializations of these definitions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

def burnolRadiusMellinTailKernelRaw
    (radius : ℝ) (coordinate : ℂ) (t : ℝ) : ℂ :=
  if t ∈ Ioi radius then (t : ℂ) ^ (-star coordinate) else 0

theorem star_burnolRadiusMellinTailKernelRaw
    {radius : ℝ} (positive : 0 < radius) (coordinate : ℂ) (t : ℝ) :
    star (burnolRadiusMellinTailKernelRaw radius coordinate t) =
      if t ∈ Ioi radius then (t : ℂ) ^ (-coordinate) else 0 := by
  by_cases ht : t ∈ Ioi radius
  · have tPositive : 0 < t := lt_trans positive ht
    have argNe : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg tPositive.le]
      exact ne_of_lt Real.pi_pos
    have conjugated := Complex.conj_cpow (t : ℂ) (-coordinate) argNe
    simpa [burnolRadiusMellinTailKernelRaw, ht, Complex.star_def] using
      conjugated.symm
  · simp [burnolRadiusMellinTailKernelRaw, ht]

theorem burnolRadiusMellinTailKernelRaw_measurable
    {radius : ℝ} (positive : 0 < radius) (coordinate : ℂ) :
    Measurable (burnolRadiusMellinTailKernelRaw radius coordinate) := by
  let positiveBase : ℝ → ℂ := fun t => ((max radius t : ℝ) : ℂ)
  have baseContinuous : Continuous positiveBase :=
    Complex.continuous_ofReal.comp (continuous_const.max continuous_id)
  have baseSlit : ∀ t, positiveBase t ∈ Complex.slitPlane := by
    intro t
    apply Complex.ofReal_mem_slitPlane.mpr
    exact lt_of_lt_of_le positive (le_max_left _ _)
  have powered : Measurable (fun t => positiveBase t ^ (-star coordinate)) :=
    (continuousOn_univ.mp
      (baseContinuous.continuousOn.cpow_const fun t _ => baseSlit t)).measurable
  have rawFormula : burnolRadiusMellinTailKernelRaw radius coordinate =
      (Ioi radius).indicator (fun t => positiveBase t ^ (-star coordinate)) := by
    funext t
    by_cases ht : t ∈ Ioi radius
    · rw [burnolRadiusMellinTailKernelRaw, if_pos ht, indicator_of_mem ht]
      simp only [positiveBase]
      rw [max_eq_right ht.le]
    · rw [burnolRadiusMellinTailKernelRaw, if_neg ht,
        indicator_of_notMem ht]
  rw [rawFormula]
  exact powered.indicator measurableSet_Ioi

theorem burnolRadiusMellinTailKernelRaw_memLp
    {radius : ℝ} (positive : 0 < radius)
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re) :
    MemLp (burnolRadiusMellinTailKernelRaw radius coordinate) 2 volume := by
  have measurable :=
    (burnolRadiusMellinTailKernelRaw_measurable positive coordinate
      ).aestronglyMeasurable (μ := volume)
  apply (memLp_two_iff_integrable_sq_norm measurable).mpr
  have exponent : -2 * coordinate.re < -1 := by linarith
  have integrablePower : IntegrableOn (fun t : ℝ => t ^ (-2 * coordinate.re))
      (Ioi radius) :=
    (integrableOn_Ioi_rpow_iff positive).mpr exponent
  apply (integrablePower.integrable_indicator measurableSet_Ioi).congr
  exact ae_of_all volume fun t => by
    by_cases ht : t ∈ Ioi radius
    · have tPositive : 0 < t := lt_trans positive ht
      simp only [burnolRadiusMellinTailKernelRaw, ht, if_true]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos tPositive,
        indicator_of_mem ht]
      simp only [neg_re, Complex.star_def, Complex.conj_re]
      rw [← Real.rpow_mul_natCast tPositive.le]
      congr 1
      ring
    · simp [burnolRadiusMellinTailKernelRaw, ht]

def burnolRadiusMellinTailKernelL2
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re) : BurnolL2 :=
  (burnolRadiusMellinTailKernelRaw_memLp positive coordinate rightHalf).toLp
    (burnolRadiusMellinTailKernelRaw radius coordinate)

def burnolRadiusMellinTailEvaluator
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re) :
    BurnolL2 →L[ℂ] ℂ :=
  innerSL ℂ (burnolRadiusMellinTailKernelL2
    radius positive coordinate rightHalf)

theorem burnolRadiusMellinTailEvaluator_eq_integral
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re)
    (value : BurnolL2) :
    burnolRadiusMellinTailEvaluator radius positive coordinate rightHalf value =
      ∫ t : ℝ in Ioi radius, (t : ℂ) ^ (-coordinate) * value t := by
  change inner ℂ
      (burnolRadiusMellinTailKernelL2 radius positive coordinate rightHalf)
      value = _
  rw [L2.inner_def, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
      (burnolRadiusMellinTailKernelRaw_memLp positive coordinate rightHalf)]
      with t kernelRead
  simp only [burnolRadiusMellinTailKernelL2]
  rw [kernelRead, RCLike.inner_apply, starRingEnd_apply,
    star_burnolRadiusMellinTailKernelRaw positive coordinate]
  by_cases ht : t ∈ Ioi radius <;> simp [ht, mul_comm]

theorem burnolRadiusMellinWeight_integrableOn_tail
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : ℂ) (rightHalf : 1 / 2 < coordinate.re)
    (value : BurnolL2) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-coordinate) * value t)
      (Ioi radius) := by
  rw [← integrable_indicator_iff measurableSet_Ioi]
  apply (L2.integrable_inner
    (burnolRadiusMellinTailKernelL2 radius positive coordinate rightHalf)
      value).congr
  filter_upwards [MemLp.coeFn_toLp
      (burnolRadiusMellinTailKernelRaw_memLp positive coordinate rightHalf)]
      with t kernelRead
  simp only [burnolRadiusMellinTailKernelL2]
  rw [kernelRead, RCLike.inner_apply, starRingEnd_apply,
    star_burnolRadiusMellinTailKernelRaw positive coordinate]
  by_cases ht : t ∈ Ioi radius <;> simp [ht, mul_comm]

def burnolConstantGapCoefficient (radius : ℝ) :
    EvenBurnolPhysicalCarrier radius →L[ℂ] ℂ :=
  ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹) •
    ((innerSL ℂ (intervalConstant radius)).comp
      ((restrictToInterval radius).comp
        (Submodule.subtypeL (evenBurnolClosedFace radius).toSubmodule)))

theorem burnolConstantGapCoefficient_eq
    (radius : ℝ) (positive : 0 < radius)
    (value : EvenBurnolPhysicalCarrier radius) (coefficient : ℂ)
    (gap : coefficient • intervalConstant radius =
      restrictToInterval radius (value : BurnolL2)) :
    burnolConstantGapCoefficient radius value = coefficient := by
  have normNe : (‖intervalConstant radius‖ ^ 2 : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (intervalConstant_ne_zero positive))
  change (‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹ *
      inner ℂ (intervalConstant radius)
        (restrictToInterval radius (value : BurnolL2)) = coefficient
  rw [← gap, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rw [← mul_assoc,
    mul_comm ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹) coefficient,
    mul_assoc]
  simp [normNe]

def burnolRadiusMellinGapMoment (radius : ℝ) (coordinate : ℂ) : ℂ :=
  (radius : ℂ) ^ (1 - coordinate) / (1 - coordinate)

structure BurnolCompletedMellinCoordinate where
  value : ℂ
  rightHalf : 1 / 2 < value.re
  belowOne : value.re < 1

theorem no_burnolCompletedMellinCoordinate_at_one :
    ¬ ∃ coordinate : BurnolCompletedMellinCoordinate,
      coordinate.value = 1 := by
  rintro ⟨coordinate, equality⟩
  have below := coordinate.belowOne
  rw [equality] at below
  norm_num at below

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

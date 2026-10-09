import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.RieszCanonicalRaw
import H0mework.Versions.V2.Arithmetic.TruncatedFourier.DilationAction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The generated mean-zero Fourier return has a canonical continuous first derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Interval SchwartzMap Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" =>
  (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

local instance burnolQuarterFiniteMeasure : IsFiniteMeasure μq where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def burnolRieszReturnRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate) x

def burnolRieszReturnWindow (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
      BurnolQuarterIntervalL2)

def burnolRieszReturnRawDerivative
    (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : ℂ :=
  (VectorFourier.fourierIntegral 𝐞 μq (innerSL ℝ).toLinearMap₁₂
    (VectorFourier.fourierSMulRight (innerSL ℝ)
      ((burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
        ℝ → ℂ)) u) 1

private theorem burnolQuarterSource_integrable
    (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable
      ((burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
        ℝ → ℂ) μq :=
  (Lp.memLp (burnolRieszSingleFourierSource coordinate :
    BurnolQuarterIntervalL2)).integrable (by norm_num)

private theorem burnolQuarterSource_normMoment_integrable
    (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (fun x : ℝ => ‖x‖ *
      ‖(burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x‖)
      μq := by
  have source := (burnolQuarterSource_integrable coordinate).norm.const_mul q
  apply source.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg _))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [symmetricInterval, mem_Icc, Real.norm_eq_abs, abs_le] using hx

private theorem burnolQuarterSource_fourierSMulRight_integrable
    (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable
      (VectorFourier.fourierSMulRight (innerSL ℝ)
        ((burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
          ℝ → ℂ)) μq := by
  have majorant := (burnolQuarterSource_normMoment_integrable coordinate).const_mul
    (2 * Real.pi * ‖innerSL (E := ℝ) ℝ‖)
  apply majorant.mono'
  · exact (Lp.memLp (burnolRieszSingleFourierSource coordinate :
      BurnolQuarterIntervalL2)).aestronglyMeasurable.fourierSMulRight
  · filter_upwards with x
    simpa only [mul_assoc] using
      VectorFourier.norm_fourierSMulRight_le (innerSL (E := ℝ) ℝ)
        (((burnolRieszSingleFourierSource coordinate :
          BurnolQuarterIntervalL2) : ℝ → ℂ)) x

/-- The actual source derivative keeps its complete finite Fourier integral. -/
theorem burnolRieszReturnRawDerivative_integral
    (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    burnolRieszReturnRawDerivative coordinate frequency =
      ∫ x : ℝ in symmetricInterval q,
        𝐞 (-(frequency * x)) *
          (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) *
            (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x) := by
  unfold burnolRieszReturnRawDerivative
  rw [Real.fourierIntegral_continuousLinearMap_apply'
    (burnolQuarterSource_fourierSMulRight_integrable coordinate)]
  unfold VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  have innerOne : (innerSL ℝ) x 1 = x := by
    rw [innerSL_apply_apply, Real.inner_apply, mul_one]
  have innerFrequency : (innerSL ℝ) x frequency = x * frequency := by
    rw [innerSL_apply_apply, Real.inner_apply]
  simp only [VectorFourier.fourierSMulRight_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerOne, innerFrequency,
    Circle.smul_def, smul_eq_mul, real_smul]
  rw [mul_comm x frequency]
  ring

theorem burnolRieszReturnRaw_hasDerivAt
    (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) :
    HasDerivAt (burnolRieszReturnRaw coordinate)
      (burnolRieszReturnRawDerivative coordinate u) u := by
  have generated := VectorFourier.hasFDerivAt_fourierIntegral
    (innerSL ℝ) (burnolQuarterSource_integrable coordinate)
    (burnolQuarterSource_normMoment_integrable coordinate) u
  unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw
    burnolRadiusTruncatedFourierRaw burnolRieszReturnRawDerivative
  have innerEq : (innerₗ ℝ) = (innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [innerₗ_apply_apply,
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply]
  rw [innerEq]
  simpa only [hasDerivAt_sub_const_iff] using generated.hasDerivAt

theorem burnolRieszReturnRaw_continuous
    (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (burnolRieszReturnRaw coordinate) :=
  continuous_iff_continuousAt.mpr fun u =>
    (burnolRieszReturnRaw_hasDerivAt coordinate u).continuousAt

theorem burnolRieszReturnRawDerivative_continuous
    (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (burnolRieszReturnRawDerivative coordinate) := by
  unfold burnolRieszReturnRawDerivative
  exact (VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar
    (by
      simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
        innerSL_apply_apply] using
        (continuous_inner : Continuous (fun p : ℝ × ℝ => inner ℝ p.1 p.2)))
    (burnolQuarterSource_fourierSMulRight_integrable coordinate)).clm_apply
      continuous_const


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

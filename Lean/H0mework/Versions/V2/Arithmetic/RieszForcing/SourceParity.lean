import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.Forcing
import H0mework.Versions.V2.Arithmetic.TruncatedFourier.Overlap
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
noncomputable section

def sourceMeanZeroReflection (state : BurnolQuarterMeanZeroCarrier) :
    BurnolQuarterMeanZeroCarrier :=
  ⟨reflectRestricted (1 / 4 : ℝ) (state : BurnolQuarterIntervalL2),
    reflectRestricted_quarter_preserves_meanZero state.property⟩

theorem sourceTruncatedFourier_reflect (state : BurnolQuarterIntervalL2) :
    burnolTruncatedFourier (reflectRestricted (1 / 4 : ℝ) state) =
      reflectRestricted (1 / 4 : ℝ) (burnolTruncatedFourier state) := by
  change restrictToInterval (1 / 4 : ℝ)
      (fourierL2 (burnolRadiusZeroExtension (1 / 4 : ℝ)
        (reflectRestricted (1 / 4 : ℝ) state))) = _
  rw [← burnolRadiusZeroExtension_reflect,
    fourierL2_reflectL2_commute, restrictToInterval_reflectL2]
  rfl

theorem sourceMeanZeroFourier_reflect (state : BurnolQuarterMeanZeroCarrier) :
    burnolMeanZeroTruncatedFourier (sourceMeanZeroReflection state) =
      sourceMeanZeroReflection (burnolMeanZeroTruncatedFourier state) := by
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection
      (burnolTruncatedFourier (reflectRestricted (1 / 4 : ℝ)
        (state : BurnolQuarterIntervalL2))) =
    reflectRestricted (1 / 4 : ℝ)
      (burnolQuarterMeanZeroProjection
        (burnolTruncatedFourier (state : BurnolQuarterIntervalL2)))
  rw [sourceTruncatedFourier_reflect, burnolQuarterMeanZeroProjection_reflect]

private theorem sourceOneMinusSquare_reflect (state : BurnolQuarterMeanZeroCarrier) :
    burnolMeanZeroOneMinusSquare (sourceMeanZeroReflection state) =
      sourceMeanZeroReflection (burnolMeanZeroOneMinusSquare state) := by
  change sourceMeanZeroReflection state -
      burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (sourceMeanZeroReflection state)) = _
  rw [sourceMeanZeroFourier_reflect, sourceMeanZeroFourier_reflect]
  apply Subtype.ext
  exact (map_sub (reflectRestricted (1 / 4 : ℝ))
    (state : BurnolQuarterIntervalL2)
    (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier state) :
      BurnolQuarterIntervalL2)).symm

theorem burnolRieszSingleFourierSource_reflection_fixed
    (coordinate : BurnolCompletedMellinCoordinate) :
    reflectRestricted (1 / 4 : ℝ)
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) := by
  have forcingFixed : sourceMeanZeroReflection
      (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)) =
      burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) := by
    apply Subtype.ext
    exact burnolAmbientMeanZeroFourier_reflection_fixed _
  have reflectedSolved :
      burnolMeanZeroOneMinusSquare
          (sourceMeanZeroReflection (burnolRieszSingleFourierSource coordinate)) =
        burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) := by
    rw [sourceOneMinusSquare_reflect, burnolRieszSingleFourierSource_equation, forcingFixed]
  have inverseLeft : burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have recovered := congrArg burnolMeanZeroBlockInverse reflectedSolved
  change (burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare)
      (sourceMeanZeroReflection (burnolRieszSingleFourierSource coordinate)) =
    burnolRieszSingleFourierSource coordinate at recovered
  rw [inverseLeft] at recovered
  exact congrArg (fun state : BurnolQuarterMeanZeroCarrier =>
    (state : BurnolQuarterIntervalL2)) recovered

theorem burnolRieszSingleFourierReturn_reflection_fixed
    (coordinate : BurnolCompletedMellinCoordinate) :
    reflectRestricted (1 / 4 : ℝ)
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2) =
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
        BurnolQuarterIntervalL2) := by
  have sourceFixed : sourceMeanZeroReflection (burnolRieszSingleFourierSource coordinate) =
      burnolRieszSingleFourierSource coordinate := by
    apply Subtype.ext
    exact burnolRieszSingleFourierSource_reflection_fixed coordinate
  have returned := sourceMeanZeroFourier_reflect (burnolRieszSingleFourierSource coordinate)
  rw [sourceFixed] at returned
  exact congrArg (fun state : BurnolQuarterMeanZeroCarrier =>
    (state : BurnolQuarterIntervalL2)) returned.symm

private theorem sourceRaw_reflection_ae
    (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] raw)
    (fixed : reflectRestricted (1 / 4 : ℝ) state = state) :
    (fun x : ℝ => raw (-x)) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] raw := by
  let reflection := negMeasurePreserving_restrict (1 / 4 : ℝ)
  filter_upwards [Lp.coeFn_compMeasurePreserving state reflection,
    reflection.quasiMeasurePreserving.ae read, read] with x reflected negative direct
  change reflectRestricted (1 / 4 : ℝ) state x = state (-x) at reflected
  rw [fixed] at reflected
  exact negative.symm.trans (reflected.symm.trans direct)

private theorem sourceRaw_endpoints
    (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] raw)
    (fixed : reflectRestricted (1 / 4 : ℝ) state = state)
    (continuous : ∀ x : ℝ, x ≠ 0 → ContinuousAt raw x) :
    raw (-(1 / 4 : ℝ)) = raw (1 / 4 : ℝ) := by
  have inside : Icc (1 / 8 : ℝ) (1 / 4 : ℝ) ⊆ symmetricInterval (1 / 4 : ℝ) := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have restricted : (fun x : ℝ => raw (-x)) =ᵐ[
      volume.restrict (Icc (1 / 8 : ℝ) (1 / 4 : ℝ))] raw :=
    ae_restrict_of_ae_restrict_of_subset inside (sourceRaw_reflection_ae state raw read fixed)
  have directContinuous : ContinuousOn raw (Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
    intro x hx
    exact (continuous x (by linarith [hx.1])).continuousWithinAt
  have reflectedContinuous :
      ContinuousOn (fun x : ℝ => raw (-x)) (Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
    intro x hx
    exact ((continuous (-x) (by linarith [hx.1])).comp
      continuous_neg.continuousAt).continuousWithinAt
  exact Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
    (by norm_num : (1 / 8 : ℝ) ≠ 1 / 4) restricted
    reflectedContinuous directContinuous (by norm_num)

theorem burnolRieszSingleFourierSourceRaw_endpoints
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszSingleFourierSourceRaw coordinate (-(1 / 4 : ℝ)) =
      burnolRieszSingleFourierSourceRaw coordinate (1 / 4 : ℝ) := by
  exact sourceRaw_endpoints
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    (burnolRieszSingleFourierSourceRaw coordinate)
    (burnolRieszSingleFourierSource_ae_raw coordinate)
    (burnolRieszSingleFourierSource_reflection_fixed coordinate)
    (fun _ nonzero => burnolRieszSingleFourierSourceRaw_continuousAt coordinate nonzero)

theorem burnolRieszSingleFourierReturnRaw_endpoints
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate) (-(1 / 4 : ℝ)) =
      burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate) (1 / 4 : ℝ) := by
  apply sourceRaw_endpoints
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
      BurnolQuarterIntervalL2)
    (burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate))
    (burnolMeanZeroFourier_ae_raw (burnolRieszSingleFourierSource coordinate))
    (burnolRieszSingleFourierReturn_reflection_fixed coordinate)
  intro x _
  exact (burnolRadiusTruncatedFourierRaw_continuous
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)).continuousAt.sub
      continuousAt_const

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

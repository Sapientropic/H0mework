import H0mework.NavierStokes.GeneratedPaths.FiniteObservedCompactness
import H0mework.NavierStokes.GeneratedPaths.ReceiptSquareCascadeBound

/-!
# Uniform receipt-square bound in the common critical regime

The receipt-square cascade theorem is already independent of path length
and generated frequencies, but its displayed right side still reads the
particular endpoint's initial half-enstrophy and negative-one ceiling.

This consumer eliminates both source-specific quantities using the common
critical coefficient ceiling.  The resulting bound depends only on
viscosity and the strict critical parameter.  It accepts no amplitude
lower bound, observation coverage, cutoff, path length, or target scenario.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareUniformBound

open scoped BigOperators

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistenceWindow
open ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareCascadeBound
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness

noncomputable section

/-- The common cutoff-, frequency-, and path-length-independent
receipt-square ceiling in one strict critical regime. -/
def uniformReceiptTraceSquareCeiling
    (ν : Viscosity)
    (θ : ℝ) : ℝ :=
  48 * (2 * Real.pi) ^ 2 *
        max 1 (criticalNegativeOneTimeCeiling ν θ) *
        ((1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling ν θ) /
      criticalEnstrophyAbsorptionCoefficient θ ν

/-- Every finite source-generated cascade in one strict critical regime has
a receipt-square bound depending only on `ν` and `θ`.

The path contributes only the generated receipt square mass on the left.
Both endpoint-specific quantities from the underlying cascade theorem are
eliminated in the proof. -/
theorem GeneratedCriticalScalePath.receiptTraceSquareMass_le_uniform
    {ν : Viscosity}
    {θ : ℝ}
    (path : GeneratedCriticalScalePath ν θ)
    (θLtOne : θ < 1) :
    generatedPathReceiptTraceSquareMass path.arrival ≤
      uniformReceiptTraceSquareCeiling ν θ := by
  let initialEnstrophy :=
    finiteStateVorticityCoefficientEnstrophy
      (generatedSupport path.current)
      (generatedComplexVorticityState path.current
        (generatedSupport path.current))
  let commonCeiling :=
    criticalCoefficientEnstrophyCeiling ν θ
  have initialEnstrophyNonneg : 0 ≤ initialEnstrophy := by
    unfold initialEnstrophy
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun _ _ =>
      complexCoordinateAmplitudeSq_nonneg _
  have commonCeilingNonneg : 0 ≤ commonCeiling := by
    exact criticalCoefficientEnstrophyCeiling_nonneg ν θ
  have initialEnstrophyLe :
      initialEnstrophy ≤ commonCeiling := by
    simpa [initialEnstrophy, commonCeiling] using
      path.initialEnstrophy_le_ceiling
  have initialSqLe :
      initialEnstrophy ^ 2 ≤ commonCeiling ^ 2 :=
    (sq_le_sq₀ initialEnstrophyNonneg commonCeilingNonneg).2
      initialEnstrophyLe
  have negativeOneNumeratorLe :
      4 * criticalEnstrophyLatticeConstant *
            initialEnstrophy ^ 2 +
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            initialEnstrophy ≤
        4 * criticalEnstrophyLatticeConstant *
            commonCeiling ^ 2 +
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            commonCeiling := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left initialSqLe
        (mul_nonneg (by norm_num)
          criticalEnstrophyLatticeConstant_nonneg))
      (mul_le_mul_of_nonneg_left initialEnstrophyLe
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have absorptionPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν :=
    criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  have negativeOneCeilingLe :
      generatedPathNegativeOneTimeCeiling path.current ν θ ≤
        criticalNegativeOneTimeCeiling ν θ := by
    unfold generatedPathNegativeOneTimeCeiling
      criticalNegativeOneTimeCeiling
    dsimp [initialEnstrophy, commonCeiling] at negativeOneNumeratorLe ⊢
    exact
      (div_le_div_iff_of_pos_right absorptionPos).2
        negativeOneNumeratorLe
  have protectedNegativeOneLe :
      max 1
          (generatedPathNegativeOneTimeCeiling
            path.current ν θ) ≤
        max 1 (criticalNegativeOneTimeCeiling ν θ) :=
    max_le_max le_rfl negativeOneCeilingLe
  have initialHalfEnstrophyLe :
      finiteStateVorticityHalfEnstrophy
          (generatedSupport path.current)
          (generatedComplexVorticityState path.current
            (generatedSupport path.current)) ≤
        (1 / 2 : ℝ) * commonCeiling := by
    unfold finiteStateVorticityHalfEnstrophy
    exact
      mul_le_mul_of_nonneg_left initialEnstrophyLe
        (by norm_num)
  have initialHalfEnstrophyNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          (generatedSupport path.current)
          (generatedComplexVorticityState path.current
            (generatedSupport path.current)) :=
    finiteStateVorticityHalfEnstrophy_nonneg _ _
  have commonHalfCeilingNonneg :
      0 ≤ (1 / 2 : ℝ) * commonCeiling :=
    mul_nonneg (by norm_num) commonCeilingNonneg
  have scaleNonneg :
      0 ≤ 48 * (2 * Real.pi) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have protectedCommonNonneg :
      0 ≤ max 1 (criticalNegativeOneTimeCeiling ν θ) :=
    le_trans zero_le_one (le_max_left _ _)
  have numeratorLe :
      48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedPathNegativeOneTimeCeiling
                path.current ν θ) *
            finiteStateVorticityHalfEnstrophy
              (generatedSupport path.current)
              (generatedComplexVorticityState path.current
                (generatedSupport path.current)) ≤
        48 * (2 * Real.pi) ^ 2 *
            max 1 (criticalNegativeOneTimeCeiling ν θ) *
            ((1 / 2 : ℝ) * commonCeiling) := by
    exact
      mul_le_mul
        (mul_le_mul_of_nonneg_left
          protectedNegativeOneLe scaleNonneg)
        initialHalfEnstrophyLe
        initialHalfEnstrophyNonneg
        (mul_nonneg scaleNonneg protectedCommonNonneg)
  have sourceBound :=
    generatedIntegerShellReachable_critical_receiptTraceSquareMass_le
      path.arrival ν θ θLtOne path.initialMargin
  unfold uniformReceiptTraceSquareCeiling
  exact sourceBound.trans
    ((div_le_div_iff_of_pos_right absorptionPos).2
      (by
        simpa [commonCeiling] using numeratorLe))

/--
Any exact finite source-generated cascade which spends more than the common
receipt-square budget has crossed the classical critical enstrophy threshold
at its actual endpoint.

This is the direct critical-norm consumer of the receipt-square cascade
bound.  It does not require an infinite extension, support coverage, a
continuation witness, or a caller-supplied target state.
-/
theorem
    generatedIntegerShellReachable_criticalThresholdCrossing_of_uniform_lt_receiptTraceSquareMass
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (budgetExceeded :
      uniformReceiptTraceSquareCeiling ν θ <
        generatedPathReceiptTraceSquareMass arrival) :
    θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
      criticalEnstrophyLatticeConstant *
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport current)
          (generatedComplexVorticityState current
            (generatedSupport current)) := by
  by_contra thresholdNotCrossed
  have endpointCriticalMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current)) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    not_lt.mp thresholdNotCrossed
  let path : GeneratedCriticalScalePath ν θ :=
    { seed := seed
      current := current
      arrival := arrival
      initialMargin := endpointCriticalMargin }
  have bounded :
      generatedPathReceiptTraceSquareMass arrival ≤
        uniformReceiptTraceSquareCeiling ν θ := by
    simpa [path] using
      GeneratedCriticalScalePath.receiptTraceSquareMass_le_uniform
        path θLtOne
  exact (not_lt_of_ge bounded) budgetExceeded

end

end ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareUniformBound
end NavierStokes
end SaturationMonoid

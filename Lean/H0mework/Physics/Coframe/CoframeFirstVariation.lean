import H0mework.Physics.Coframe.CoframeLocalDifferentiability

/-!
# S9-C3e2a: actual pointwise coframe first variation

The local stress producer from C3e1 is composed with the genuine affine
coframe path in the primitive holonomic configuration.  This yields the
pointwise Fréchet derivative of the common generated density and defines its
actual first-variation density.  Compact support follows from linearity of the
generated stress covector; no stress, first-density, derivative, or
integrability receipt is accepted.

This module deliberately stops before differentiation under the spacetime
integral.  Uniform domination on the nondegenerate corridor, the integrated
derivative, and the weak/pointwise equations remain later gates.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeFirstVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

def holonomicCoframeFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (point : BasePoint) : ℝ :=
  coframeLocalStressCovector source point
    (toContinuumPointField configuration point) (variation point)

theorem coframeLocalDensity_line_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (direction : LorentzianCoframe) :
    HasFDerivAt
      (fun parameter : ℝ =>
        coframeLocalDensity source point field
          (field.coframe + parameter • direction))
      ((coframeLocalStressCovector source point field).comp
        (ContinuousLinearMap.toSpanSingleton ℝ direction)) 0 := by
  have pathDerivative : HasFDerivAt
      (fun parameter : ℝ => field.coframe + parameter • direction)
      (ContinuousLinearMap.toSpanSingleton ℝ direction) 0 := by
    exact (hasFDerivAt_const_add_iff
      (f := fun parameter : ℝ =>
        (ContinuousLinearMap.toSpanSingleton ℝ direction) parameter)
      field.coframe).2
        (ContinuousLinearMap.toSpanSingleton ℝ direction).hasFDerivAt
  have outerDerivative := coframeLocalDensity_hasFDerivAt
    source point field nondegenerate
  have outerAtPath : HasFDerivAt
      (coframeLocalDensity source point field)
      (coframeLocalStressCovector source point field)
      (field.coframe + (0 : ℝ) • direction) := by
    simpa using outerDerivative
  exact outerAtPath.comp 0 pathDerivative

theorem holonomicLocalDensity_coframe_hasFDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (variation : BasePoint → LorentzianCoframe)
    (point : BasePoint) :
    HasFDerivAt
      (fun parameter : ℝ =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField
            (varyCoframe configuration variation parameter) point))
      ((coframeLocalStressCovector source point
          (toContinuumPointField configuration point)).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (variation point))) 0 := by
  rw [show (fun parameter : ℝ =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyCoframe configuration variation parameter) point)) =
      fun parameter =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (withCoframe (toContinuumPointField configuration point)
            (configuration.coframe point + parameter • variation point)) by
    funext parameter
    rw [toContinuumPointField_varyCoframe]]
  simpa only [coframeLocalDensity, toContinuumPointField,
    StageNineContinuumPointField.coframe] using
      coframeLocalDensity_line_hasFDerivAt source point
        (toContinuumPointField configuration point)
        (nondegenerate point) (variation point)

theorem holonomicCoframeFirstVariationDensity_eq_zero_of_variation_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicCoframeFirstVariationDensity source configuration variation point =
      0 := by
  simp [holonomicCoframeFirstVariationDensity, variationZero]

theorem holonomicCoframeFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    HasCompactSupport
      (holonomicCoframeFirstVariationDensity source configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  exact holonomicCoframeFirstVariationDensity_eq_zero_of_variation_zero
    source configuration variation point variationZero

end

end SaturationMonoid.PhysicsCore.StageNineCoframeFirstVariation

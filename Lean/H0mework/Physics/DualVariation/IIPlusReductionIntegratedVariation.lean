import H0mework.Physics.Geometry.AffineCompactCorridorIntegratedCalculus
import H0mework.Physics.Coframe.CoframeJointCalculus
import H0mework.Physics.DualVariation.IIPlusReductionHolonomicRegularity

/-!
# Integrated nonlinear `II+` reduction of the Dirac-dual form-native root

This module lifts the actual repaired-root path

`e(t) = e + t h`,  `B(t) = II+(e(t))`

through the spacetime integral.  Joint `C¹` regularity and compact support
generate the differentiation corridor internally.  The coefficient is the
integral of the repaired action's own local nonlinear response.

No old total derivative, dominator, equation, stationarity receipt, fixed
actual, or target covector enters the theorem mouth.  The final restriction
theorem only transports the same derivative across an already proved equality
of repaired action values.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusReductionIntegratedVariation

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineAffineCompactCorridorIntegratedCalculus
open StageNineCoframeJointCalculus
open StageNineCoframeVariation
open StageNineDiracDualFormNativeIIPlusReductionHolonomicRegularity
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusReductionHolonomicRegularity
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineCompactSupportIntegrationByParts
open scoped ContDiff Matrix.Norms.Elementwise Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Internally generated joint corridor -/

private theorem holonomicCoframe_contDiff_one
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ 1 configuration.coframe := by
  have infinite : ContDiff ℝ ∞ configuration.coframe := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro column
    exact smooth.1 row column
  exact infinite.of_le (by norm_num)

private theorem exists_diracDualFormNativeIIPlusReducedCoframeJointC1Corridor
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    ∃ parameterSet : Set ℝ,
      IsOpen parameterSet ∧
        0 ∈ parameterSet ∧
        ContDiffOn ℝ 1
          (Function.uncurry
            (affineDensityIncrement
              (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
                source configuration)
              configuration.coframe variation))
          (parameterSet ×ˢ (univ : Set BasePoint)) := by
  have eventuallyAdmitted : ∀ᶠ parameter in nhds (0 : ℝ), ∀ point,
      Matrix.det
        (configuration.coframe point + parameter • variation point) ≠ 0 := by
    simpa [StageNineHolonomicConfiguration.Nondegenerate, varyCoframe] using
      compactCoframeVariation_eventually_nondegenerate configuration smooth
        nondegenerate variation
  obtain ⟨parameterSet, parameterSetOpen, zeroMem, jointC1⟩ :=
    exists_open_affineCorridorDensityIncrement_contDiffOn
      (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
        source configuration)
      configuration.coframe variation
      (fun candidate : LorentzianCoframe => Matrix.det candidate ≠ 0)
      eventuallyAdmitted
      (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily_joint_contDiffAt
        source configuration smooth)
      (holonomicCoframe_contDiff_one configuration smooth)
      (variation.smooth.of_le (by norm_num))
  refine ⟨parameterSet, parameterSetOpen, zeroMem, ?_⟩
  have incrementEquality :
      affineDensityIncrement
          (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation =
        affineCorridorDensityIncrement
          (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation := by
    funext parameter point
    rfl
  rw [incrementEquality]
  exact jointC1

/-! ## Exact reduced path and local derivative identification -/

private theorem affineVariedDensity_eq_diracDualFormNativeIIPlusReducedDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) :
    affineVariedDensity
        (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation parameter point =
      generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
        source (sourceGeneratedUnifiedCouplings source) 0 point
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (varyCoframe configuration variation parameter) point)) := by
  unfold affineVariedDensity
    holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
  rw [toContinuumPointField_varyCoframe]
  rfl

private theorem
    holonomicDiracDualFormNativeIIPlusReducedPointFieldFamily_background
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    holonomicFormNativeIIPlusReducedPointFieldFamily configuration
        (point, configuration.coframe point) =
      toContinuumPointField
        (restrictHolonomicConfigurationToIIPlus configuration) point := by
  apply StageNineContinuumPointField.ext <;>
    rfl

private theorem affineDensityIncrementParameterFDeriv_zero_eq_actual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement
          (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (point : BasePoint) :
    affineDensityIncrementParameterFDeriv
        (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation 0 point =
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source
          point (toContinuumPointField configuration point)
          (variation point))) := by
  let field := toContinuumPointField configuration point
  have variedDerivative : HasDerivAt
      (diracDualFormNativeIIPlusReducedLocalDensityPath source point field
        (variation point))
      (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source
        point field (variation point)) 0 :=
    diracDualFormNativeIIPlusReducedLocalDensityPath_hasDerivAt source point
      field (nondegenerate point) (variation point)
  have incrementDerivativeScalar : HasDerivAt
      (fun parameter : ℝ =>
        affineDensityIncrement
          (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation parameter point)
      (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source
        point field (variation point)) 0 := by
    unfold affineDensityIncrement
    apply (variedDerivative.sub_const
      (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
        source configuration point (configuration.coframe point)))
      |>.congr_of_eventuallyEq
    filter_upwards [] with parameter
    simpa [affineVariedDensity, field] using
      congrArg (fun value => value -
        holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration point (configuration.coframe point))
        (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily_affine_eq_reducedPath
          source configuration variation parameter point)
  have incrementDerivative : HasFDerivAt
      (fun parameter : ℝ =>
        affineDensityIncrement
          (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation parameter point)
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source
          point field (variation point))) 0 :=
    incrementDerivativeScalar.hasFDerivAt
  exact (affineDensityIncrement_hasFDerivAt
    (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
      source configuration)
    configuration.coframe variation parameterSet parameterSetOpen jointC1
      0 zeroMem point).unique incrementDerivative

/-- Pointwise coefficient read from the repaired local nonlinear producer on
the same holonomic configuration and compact coframe direction. -/
def holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (point : BasePoint) : ℝ :=
  diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source point
    (toContinuumPointField configuration point) (variation point)

/-! ## Public integrated variation and action-value transporter -/

/-- The repaired nonlinear reduced action has the integrated derivative
generated by its own actual local path. -/
theorem
    holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration))
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    HasDerivAt
      (fun parameter =>
        holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
          source 0 (varyCoframe configuration variation parameter))
      (∫ point : BasePoint,
        holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source configuration variation point) 0 := by
  obtain ⟨parameterSet, parameterSetOpen, zeroMem, jointC1⟩ :=
    exists_diracDualFormNativeIIPlusReducedCoframeJointC1Corridor source
      configuration smooth nondegenerate variation
  have backgroundIntegrable : Integrable fun point : BasePoint =>
      holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
        source configuration point (configuration.coframe point) := by
    have backgroundEquality : (fun point : BasePoint =>
        holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration point (configuration.coframe point)) =
      fun point =>
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus configuration) point) := by
      funext point
      unfold
        holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
      rw [holonomicDiracDualFormNativeIIPlusReducedPointFieldFamily_background]
      rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
      exact
        (generatedDiracDualFormNativeUnifiedLocalDensity_restrictToIIPlus
          source (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point)).symm
    rw [backgroundEquality]
    exact densityIntegrable
  have actual := integratedDensityAlongAffine_hasDerivAt_of_jointC1
    (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
      source configuration)
    configuration.coframe variation backgroundIntegrable parameterSet
      parameterSetOpen zeroMem jointC1
  have actionPathEquality :
      (fun parameter =>
        holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
          source 0 (varyCoframe configuration variation parameter)) =
      (fun parameter => ∫ point : BasePoint,
        affineVariedDensity
          (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation parameter point) := by
    funext parameter
    unfold holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
    apply integral_congr_ae
    filter_upwards with point
    exact
      (affineVariedDensity_eq_diracDualFormNativeIIPlusReducedDensity source
        configuration variation parameter point).symm
  rw [← actionPathEquality] at actual
  rw [show (fun point : BasePoint =>
      affineDensityIncrementParameterFDeriv
        (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation 0 point 1) =
      fun point =>
        holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source configuration variation point by
    funext point
    rw [affineDensityIncrementParameterFDeriv_zero_eq_actual source
      configuration nondegenerate variation parameterSet parameterSetOpen
        zeroMem jointC1 point]
    simp
      [holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity]]
      at actual
  exact actual

/-- The same derivative transported across the repaired root's computed
action-value restriction.  This adds no independent field equation. -/
theorem
    holonomicDiracDualFormNativeIntegratedUnifiedAction_iiPlusReductionPath_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration))
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (restrictHolonomicConfigurationToIIPlus
            (varyCoframe configuration variation parameter)))
      (∫ point : BasePoint,
        holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source configuration variation point) 0 := by
  have reduced :=
    holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
      source configuration smooth nondegenerate densityIntegrable variation
  simpa only [holonomicDiracDualFormNativeIntegratedAction_restrictIIPlus]
    using reduced

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusReductionIntegratedVariation

import H0mework.Physics.Geometry.AffineCompactCorridorIntegratedCalculus
import H0mework.Physics.Coframe.CoframeJointCalculus
import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity

/-!
# Integrated coframe variation of the Dirac-dual form-native root

The repaired root's actual local coframe derivative is lifted through the
spacetime integral.  A primitive compactly supported coframe variation and a
smooth nondegenerate holonomic configuration generate an open joint `C¹`
corridor.  The neutral affine integral calculus then supplies domination and
differentiation under the integral sign.

The public coefficient is the integral of the new-root local Euler covector.
No old action derivative, dominator, equation, stationarity receipt, fixed
actual, or target covector is accepted at the theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeIntegratedVariation

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineAffineCompactCorridorIntegratedCalculus
open StageNineCoframeJointCalculus
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
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

private theorem exists_diracDualFormNativeCoframeJointC1Corridor
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
              (holonomicDiracDualFormNativeCoframeLocalDensityFamily
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
      (holonomicDiracDualFormNativeCoframeLocalDensityFamily
        source configuration)
      configuration.coframe variation
      (fun candidate : LorentzianCoframe => Matrix.det candidate ≠ 0)
      eventuallyAdmitted
      (holonomicDiracDualFormNativeCoframeLocalDensityFamily_joint_contDiffAt
        source configuration smooth)
      (holonomicCoframe_contDiff_one configuration smooth)
      (variation.smooth.of_le (by norm_num))
  refine ⟨parameterSet, parameterSetOpen, zeroMem, ?_⟩
  have incrementEquality :
      affineDensityIncrement
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation =
        affineCorridorDensityIncrement
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation := by
    funext parameter point
    rfl
  rw [incrementEquality]
  exact jointC1

/-! ## Exact action path and local derivative identification -/

private theorem affineVariedDensity_eq_diracDualFormNativeDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) :
    affineVariedDensity
        (holonomicDiracDualFormNativeCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation parameter point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (varyCoframe configuration variation parameter) point) := by
  unfold affineVariedDensity
    holonomicDiracDualFormNativeCoframeLocalDensityFamily
    diracDualFormNativeCoframeLocalDensity
  rw [toContinuumPointField_varyCoframe]

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
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (point : BasePoint) :
    affineDensityIncrementParameterFDeriv
        (holonomicDiracDualFormNativeCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation 0 point =
      (diracDualFormNativeCoframeEulerCovector source point
        (toContinuumPointField configuration point)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (variation point)) := by
  let field := toContinuumPointField configuration point
  have variedDerivative : HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeLocalDensity source point field
          (field.coframe + parameter • variation point))
      (diracDualFormNativeCoframeEulerCovector source point field
        (variation point)) 0 :=
    diracDualFormNativeCoframeLocalDensity_path_hasDerivAt source point field
      (nondegenerate point) (variation point)
  rw [show field.coframe = configuration.coframe point by rfl]
    at variedDerivative
  have incrementDerivativeScalar : HasDerivAt
      (fun parameter : ℝ =>
        affineDensityIncrement
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation parameter point)
      (diracDualFormNativeCoframeEulerCovector source point field
        (variation point)) 0 := by
    simpa [affineDensityIncrement, affineVariedDensity,
      holonomicDiracDualFormNativeCoframeLocalDensityFamily, field] using
      variedDerivative.sub_const
        (diracDualFormNativeCoframeLocalDensity source point field
          field.coframe)
  have incrementDerivative : HasFDerivAt
      (fun parameter : ℝ =>
        affineDensityIncrement
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation parameter point)
      ((diracDualFormNativeCoframeEulerCovector source point field).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (variation point))) 0 := by
    rw [ContinuousLinearMap.comp_toSpanSingleton]
    exact incrementDerivativeScalar.hasFDerivAt
  exact (affineDensityIncrement_hasFDerivAt
    (holonomicDiracDualFormNativeCoframeLocalDensityFamily
      source configuration)
    configuration.coframe variation parameterSet parameterSetOpen jointC1
      0 zeroMem point).unique incrementDerivative

/-- Pointwise coefficient generated by the repaired local Euler covector. -/
def holonomicDiracDualFormNativeCoframeFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (point : BasePoint) : ℝ :=
  diracDualFormNativeCoframeEulerCovector source point
    (toContinuumPointField configuration point) (variation point)

/-! ## Public integrated variation theorem -/

/-- Smoothness, nondegeneracy, integrability of this same repaired density,
and a compact primitive coframe variation generate the integrated derivative.
-/
theorem holonomicDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyCoframe configuration variation parameter))
      (∫ point : BasePoint,
        holonomicDiracDualFormNativeCoframeFirstVariationDensity
          source configuration variation point) 0 := by
  obtain ⟨parameterSet, parameterSetOpen, zeroMem, jointC1⟩ :=
    exists_diracDualFormNativeCoframeJointC1Corridor source configuration
      smooth nondegenerate variation
  have backgroundIntegrable : Integrable fun point : BasePoint =>
      holonomicDiracDualFormNativeCoframeLocalDensityFamily source
        configuration point (configuration.coframe point) := by
    have backgroundEquality : (fun point : BasePoint =>
        holonomicDiracDualFormNativeCoframeLocalDensityFamily source
          configuration point (configuration.coframe point)) =
      fun point =>
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField configuration point) := by
      funext point
      simpa [affineVariedDensity] using
        affineVariedDensity_eq_diracDualFormNativeDensity source configuration
          variation 0 point
    rw [backgroundEquality]
    exact densityIntegrable
  have actual := integratedDensityAlongAffine_hasDerivAt_of_jointC1
    (holonomicDiracDualFormNativeCoframeLocalDensityFamily
      source configuration)
    configuration.coframe variation backgroundIntegrable parameterSet
      parameterSetOpen zeroMem jointC1
  have actionPathEquality :
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyCoframe configuration variation parameter)) =
      (fun parameter => ∫ point : BasePoint,
        affineVariedDensity
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily
            source configuration)
          configuration.coframe variation parameter point) := by
    funext parameter
    unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
      sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
      integratedDiracDualFormNativeUnifiedActionAtBoundary
      toContinuumFieldSection
    apply integral_congr_ae
    filter_upwards with point
    exact (affineVariedDensity_eq_diracDualFormNativeDensity source
      configuration variation parameter point).symm
  rw [← actionPathEquality] at actual
  rw [show (fun point : BasePoint =>
      affineDensityIncrementParameterFDeriv
        (holonomicDiracDualFormNativeCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation 0 point 1) =
      fun point =>
        holonomicDiracDualFormNativeCoframeFirstVariationDensity
          source configuration variation point by
    funext point
    rw [affineDensityIncrementParameterFDeriv_zero_eq_actual source
      configuration nondegenerate variation parameterSet parameterSetOpen
        zeroMem jointC1 point]
    simp [holonomicDiracDualFormNativeCoframeFirstVariationDensity]] at actual
  exact actual

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeIntegratedVariation

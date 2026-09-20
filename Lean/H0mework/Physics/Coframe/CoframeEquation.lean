import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.Coframe.CoframeIntegratedVariation
import H0mework.Physics.Coframe.CoframePointwiseEquation
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# S9-C3e: generated coframe equation

This module closes the coframe variational route.  A compactly supported
coframe direction first generates a uniformly nondegenerate parameter
corridor.  The actual joint regularity theorem for the complete generated
density then supplies the open `C¹` corridor needed for differentiation
under the spacetime integral.

No regularity, dominator, derivative, stress, continuity, weak equation, or
pointwise equation receipt is accepted.  The only local admission predicate
passed through the abstract corridor calculus is the structural condition
`Matrix.det candidate ≠ 0`.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open StageNineCoframeFirstVariation
open StageNineCoframeJointCalculus
open MeasureTheory Filter Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

noncomputable section

set_option maxHeartbeats 1200000

local instance coframeNontrivialTopology :
    NontrivialTopology LorentzianCoframe :=
  NontrivialTopology.of_exists_norm_ne_zero ⟨1, by simp⟩

local instance coframeDualNormedAddCommGroup :
    NormedAddCommGroup (LorentzianCoframe →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coframeDualNormedSpace :
    NormedSpace ℝ (LorentzianCoframe →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem affineCorridorDensityIncrement_eq_actual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe) :
    affineCorridorDensityIncrement
        (StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily
          source configuration)
        configuration.coframe variation =
      StageNineCoframeIntegratedVariation.coframeLocalDensityIncrement
        source configuration variation := by
  funext parameter point
  unfold affineCorridorDensityIncrement affineCorridorDensity
  unfold StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily
  unfold StageNineCoframeIntegratedVariation.coframeLocalDensityIncrement
  unfold StageNineCoframeIntegratedVariation.coframeVariedLocalDensity
  rw [toContinuumPointField_varyCoframe,
    toContinuumPointField_varyCoframe]
  simp [coframeLocalDensity]

/-- The compact nondegenerate corridor and actual finite-coordinate joint
regularity generate the precise open `C¹` corridor consumed by the integrated
variation module.  The caller supplies only the primitive smooth and
nondegenerate holonomic configuration. -/
theorem exists_holonomicCoframeJointC1Corridor
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
            (StageNineCoframeIntegratedVariation.coframeLocalDensityIncrement
              source configuration variation))
          (parameterSet ×ˢ (univ : Set BasePoint)) := by
  have eventuallyAdmitted : ∀ᶠ parameter in nhds (0 : ℝ), ∀ point,
      Matrix.det
        (configuration.coframe point + parameter • variation point) ≠ 0 := by
    simpa [StageNineHolonomicConfiguration.Nondegenerate, varyCoframe] using
      compactCoframeVariation_eventually_nondegenerate configuration smooth
        nondegenerate variation
  obtain ⟨parameterSet, parameterSetOpen, zeroMem, jointC1⟩ :=
    exists_open_affineCorridorDensityIncrement_contDiffOn
      (StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily
        source configuration)
      configuration.coframe variation
      (fun candidate : LorentzianCoframe => Matrix.det candidate ≠ 0)
      eventuallyAdmitted
      (StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily_joint_contDiffAt
        source
          configuration smooth)
      ((StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
        configuration smooth).of_le (by simp))
      (variation.smooth.of_le (by simp))
  refine ⟨parameterSet, parameterSetOpen, zeroMem, ?_⟩
  rw [← affineCorridorDensityIncrement_eq_actual source configuration
    variation]
  exact jointC1

/-- The actual integrated action has the generated coframe derivative.  The
open joint-regularity corridor and its uniform dominator are outputs of the
previous theorem, not premises of this interface. -/
theorem holonomicIntegratedUnifiedAction_coframe_hasFDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    HasFDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyCoframe configuration variation parameter))
      (∫ point : BasePoint,
        (coframeLocalStressCovector source point
          (toContinuumPointField configuration point)).comp
            (ContinuousLinearMap.toSpanSingleton ℝ (variation point)))
      0 := by
  obtain ⟨parameterSet, parameterSetOpen, zeroMem, jointC1⟩ :=
    exists_holonomicCoframeJointC1Corridor source configuration smooth
      nondegenerate variation
  have actual :=
    StageNineCoframeIntegratedVariation.holonomicIntegratedUnifiedAction_coframe_hasFDerivAt_of_jointC1
      source
      configuration densityIntegrable variation parameterSet parameterSetOpen
      zeroMem jointC1
  rw [show (fun point : BasePoint =>
      StageNineCoframeIntegratedVariation.coframeIncrementParameterFDeriv
        source configuration variation 0
          point) =
      fun point : BasePoint =>
        (coframeLocalStressCovector source point
          (toContinuumPointField configuration point)).comp
            (ContinuousLinearMap.toSpanSingleton ℝ (variation point)) by
    funext point
    exact StageNineCoframeIntegratedVariation.coframeIncrementParameterFDeriv_zero_eq_actual
      source configuration
        nondegenerate variation parameterSet parameterSetOpen zeroMem jointC1
        point] at actual
  exact actual

/-- Stationarity of the actual integrated action forces the integrated weak
coframe equation.  Joint regularity, derivative integrability, and the stress
identification are all generated inside the proof. -/
theorem canonicalCoframeActionStationaryF_implies_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary :
      StageNineCoframeIntegratedVariation.CanonicalCoframeActionStationaryF
        source configuration) :
    StageNineCoframeIntegratedVariation.CanonicalCoframeWeakEquation
      source configuration := by
  intro variation
  obtain ⟨parameterSet, parameterSetOpen, zeroMem, jointC1⟩ :=
    exists_holonomicCoframeJointC1Corridor source configuration smooth
      nondegenerate variation
  have actual :=
    StageNineCoframeIntegratedVariation.holonomicIntegratedUnifiedAction_coframe_hasFDerivAt_of_jointC1
      source
      configuration densityIntegrable variation parameterSet parameterSetOpen
      zeroMem jointC1
  have derivativeZero :
      (∫ point : BasePoint,
        StageNineCoframeIntegratedVariation.coframeIncrementParameterFDeriv
          source configuration variation 0
            point) = 0 :=
    ((stationary variation).unique actual).symm
  have derivativeIntegrable :=
    StageNineCoframeIntegratedVariation.coframeIncrementParameterFDeriv_zero_integrable
      source configuration
      variation parameterSet parameterSetOpen zeroMem jointC1
  have evaluated := congrArg
    (fun derivative : ℝ →L[ℝ] ℝ => derivative 1) derivativeZero
  rw [ContinuousLinearMap.integral_apply derivativeIntegrable] at evaluated
  simp only [zero_apply] at evaluated
  rw [← evaluated]
  apply integral_congr_ae
  filter_upwards with point
  rw [StageNineCoframeIntegratedVariation.coframeIncrementParameterFDeriv_zero_eq_actual
    source configuration
      nondegenerate variation parameterSet parameterSetOpen zeroMem jointC1
      point]
  simp [holonomicCoframeFirstVariationDensity,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- The integrated weak equation is definitionally the weak equation used by
the ultralocal pointwise extractor. -/
theorem canonicalCoframeWeakEquation_to_pointwiseWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (weakEquation :
      StageNineCoframeIntegratedVariation.CanonicalCoframeWeakEquation
        source configuration) :
    StageNineCoframePointwiseEquation.CanonicalCoframeWeakEquation
      source configuration := by
  simpa [StageNineCoframeIntegratedVariation.CanonicalCoframeWeakEquation,
    StageNineCoframePointwiseEquation.CanonicalCoframeWeakEquation,
    holonomicCoframeFirstVariationDensity] using weakEquation

/-- Joint `C¹` regularity of the actual complete density produces continuity
of every fixed-direction stress coefficient.  The operator-norm structure is
local analytic infrastructure, not a continuity or stress receipt. -/
theorem holonomicCoframeDirectionalStressCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzianCoframe) :
    Continuous
      (StageNineCoframePointwiseEquation.coframeDirectionalStressCoefficient
        source configuration direction) := by
  rw [continuous_iff_continuousAt]
  intro point
  have jointC1 :=
    StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily_joint_contDiffAt
      source configuration
      smooth point (configuration.coframe point) (nondegenerate point)
  have sectionC0 : ContDiffAt ℝ 0 configuration.coframe point :=
    (StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      configuration smooth).contDiffAt.of_le (by simp)
  have derivativeC0 : ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        fderiv ℝ
          (StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily
            source configuration candidate)
          (configuration.coframe candidate)) point :=
    ContDiffAt.fderiv (m := 0) jointC1 sectionC0 (by simp)
  have evaluatedContinuous : ContinuousAt
      (fun candidate : BasePoint =>
        fderiv ℝ
          (StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily
            source configuration candidate)
          (configuration.coframe candidate) direction) point :=
    derivativeC0.continuousAt.clm_apply continuousAt_const
  change ContinuousAt
    (fun candidate : BasePoint =>
      fderiv ℝ
        (StageNineCoframeHolonomicRegularity.holonomicCoframeLocalDensityFamily
          source configuration candidate)
        (configuration.coframe candidate) direction) point
  exact evaluatedContinuous

/-- Actual joint regularity makes the generated stress covector continuous;
the fundamental-lemma extractor therefore turns the weak equation into the
pointwise coframe equation without a caller-provided continuity receipt. -/
theorem canonicalCoframeWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      StageNineCoframeIntegratedVariation.CanonicalCoframeWeakEquation
        source configuration) :
    StageNineCoframePointwiseEquation.CanonicalCoframePointwiseEquation
      source configuration := by
  apply
    StageNineCoframePointwiseEquation.canonicalCoframeWeakEquation_implies_pointwiseEquation_of_continuous
      source configuration
  · intro direction
    exact holonomicCoframeDirectionalStressCoefficient_continuous source
      configuration smooth nondegenerate direction
  · exact canonicalCoframeWeakEquation_to_pointwiseWeakEquation source
      configuration weakEquation

/-- Final C3e root theorem: smooth nondegenerate stationary holonomic data
with an integrable generated density satisfy the pointwise coframe equation. -/
theorem canonicalCoframeActionStationaryF_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary :
      StageNineCoframeIntegratedVariation.CanonicalCoframeActionStationaryF
        source configuration) :
    StageNineCoframePointwiseEquation.CanonicalCoframePointwiseEquation
      source configuration := by
  apply canonicalCoframeWeakEquation_implies_pointwiseEquation source
    configuration smooth nondegenerate
  exact canonicalCoframeActionStationaryF_implies_weakEquation source
    configuration smooth nondegenerate densityIntegrable stationary

end

end SaturationMonoid.PhysicsCore.StageNineCoframeEquation

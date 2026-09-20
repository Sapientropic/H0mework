import H0mework.Physics.CoframeVariation.CoframeIntegratedVariation
import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.Coframe.CoframePointwiseEquation
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Coframe pointwise equation of the Dirac-dual form-native root

The repaired action has generated both the complete local coframe Euler
covector and its compact-support integrated derivative.  This module performs
the remaining localization.  Joint `C¹` regularity produces continuity of
every fixed-direction coefficient, and compact scalar bumps separate the
full finite-dimensional coframe dual.

All weak, pointwise, and stationarity predicates below belong to the repaired
action hash.  No old action stationarity, continuity receipt, equation,
solution, or fixed actual is accepted at a theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframePointwiseEquation

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicRegularity
open StageNineCoframePointwiseEquation
open StageNineCoframeVariation
open StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFundamentalLemma
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

local instance coframeNontrivialTopology :
    NontrivialTopology LorentzianCoframe :=
  NontrivialTopology.of_exists_norm_ne_zero ⟨1, by simp⟩

local instance coframeDualNormedAddCommGroup :
    NormedAddCommGroup (LorentzianCoframe →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coframeDualNormedSpace :
    NormedSpace ℝ (LorentzianCoframe →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-! ## Repaired weak, pointwise, and stationarity carriers -/

def DiracDualFormNativeGravityCoframeWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzianCoframe,
    (∫ point : BasePoint,
      holonomicDiracDualFormNativeCoframeFirstVariationDensity source
        configuration variation point) = 0

def DiracDualFormNativeGravityCoframePointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    diracDualFormNativeCoframeEulerCovector source point
      (toContinuumPointField configuration point) = 0

/-- Compact-support coframe stationarity of the repaired root, with the
gravity auxiliary held as an independent primitive field. -/
def DiracDualFormNativeGravityCoframeActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzianCoframe,
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyCoframe configuration variation parameter))
      0 0

def holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzianCoframe)
    (point : BasePoint) : ℝ :=
  diracDualFormNativeCoframeEulerCovector source point
    (toContinuumPointField configuration point) direction

/-! ## Internally generated continuity -/

theorem holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzianCoframe) :
    Continuous
      (holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient source
        configuration direction) := by
  rw [continuous_iff_continuousAt]
  intro point
  have jointC1 :=
    holonomicDiracDualFormNativeCoframeLocalDensityFamily_joint_contDiffAt
      source configuration smooth point (configuration.coframe point)
        (nondegenerate point)
  have sectionC0 : ContDiffAt ℝ 0 configuration.coframe point :=
    (holonomicCoframe_contDiff configuration smooth).contDiffAt.of_le (by simp)
  have derivativeC0 : ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        fderiv ℝ
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily source
            configuration candidate)
          (configuration.coframe candidate)) point :=
    ContDiffAt.fderiv (m := 0) jointC1 sectionC0 (by simp)
  have evaluatedContinuous : ContinuousAt
      (fun candidate : BasePoint =>
        fderiv ℝ
          (holonomicDiracDualFormNativeCoframeLocalDensityFamily source
            configuration candidate)
          (configuration.coframe candidate) direction) point :=
    derivativeC0.continuousAt.clm_apply continuousAt_const
  change ContinuousAt
    (fun candidate : BasePoint =>
      fderiv ℝ
        (holonomicDiracDualFormNativeCoframeLocalDensityFamily source
          configuration candidate)
        (configuration.coframe candidate) direction) point
  exact evaluatedContinuous

/-! ## Compact-bump localization -/

theorem diracDualFormNativeGravityCoframeWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (weakEquation :
      DiracDualFormNativeGravityCoframeWeakEquation source configuration)
    (direction : LorentzianCoframe)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient source
          configuration direction point) = 0 := by
  have weakDirection :=
    weakEquation (scalarTimesCoframeVariation direction variation)
  simpa [holonomicDiracDualFormNativeCoframeFirstVariationDensity,
    holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient] using
    weakDirection

theorem diracDualFormNativeGravityCoframeWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      DiracDualFormNativeGravityCoframeWeakEquation source configuration) :
    DiracDualFormNativeGravityCoframePointwiseEquation source
      configuration := by
  intro point
  apply ContinuousLinearMap.ext
  intro direction
  have directionZero :
      holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient source
          configuration direction = 0 := by
    apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
      (holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient source
        configuration direction)
      (holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient_continuous
        source configuration smooth nondegenerate direction)
    intro variation
    exact
      diracDualFormNativeGravityCoframeWeakEquation_direction_integral source
        configuration weakEquation direction variation
  simpa [holonomicDiracDualFormNativeCoframeDirectionalEulerCoefficient] using
    congrFun directionZero point

theorem diracDualFormNativeGravityCoframePointwiseEquation_implies_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (pointwiseEquation :
      DiracDualFormNativeGravityCoframePointwiseEquation source
        configuration) :
    DiracDualFormNativeGravityCoframeWeakEquation source configuration := by
  intro variation
  apply integral_eq_zero_of_ae
  filter_upwards with point
  unfold holonomicDiracDualFormNativeCoframeFirstVariationDensity
  rw [pointwiseEquation point]
  exact zero_apply _

theorem diracDualFormNativeGravityCoframeWeakEquation_iff_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    DiracDualFormNativeGravityCoframeWeakEquation source configuration ↔
      DiracDualFormNativeGravityCoframePointwiseEquation source
        configuration := by
  constructor
  · exact
      diracDualFormNativeGravityCoframeWeakEquation_implies_pointwiseEquation
        source configuration smooth nondegenerate
  · exact
      diracDualFormNativeGravityCoframePointwiseEquation_implies_weakEquation
        source configuration

/-! ## Action-derived final characterization -/

theorem diracDualFormNativeGravityCoframeActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    DiracDualFormNativeGravityCoframeActionStationary source configuration ↔
      DiracDualFormNativeGravityCoframeWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    have coefficientZero := weakEquation variation
    rw [coefficientZero] at actual
    exact actual

theorem diracDualFormNativeGravityCoframeActionStationary_iff_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    DiracDualFormNativeGravityCoframeActionStationary source configuration ↔
      DiracDualFormNativeGravityCoframePointwiseEquation source
        configuration := by
  rw [diracDualFormNativeGravityCoframeActionStationary_iff_weakEquation source
    configuration smooth nondegenerate densityIntegrable]
  exact
    diracDualFormNativeGravityCoframeWeakEquation_iff_pointwiseEquation source
      configuration smooth nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframePointwiseEquation

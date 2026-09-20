import H0mework.Physics.Coframe.CoframeFirstVariation
import H0mework.Physics.Coframe.CoframeJointCalculus
import H0mework.Physics.Geometry.FundamentalLemma
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# S9-C3e2c: ultralocal coframe weak equation to pointwise equation

This module isolates the pointwise extraction after the actual C3e1 local
stress producer. Coframe dependence is ultralocal, so no integration by parts
is needed: a scalar compact bump multiplied by an arbitrary constant coframe
direction is enough.

The theorem ending in `_of_continuous` is the internal extraction interface.
It does not accept a joint-regularity certificate: the physics-specific joint
regularity producer is connected to this interface by the later aggregator.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframePointwiseEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open StageNineFundamentalLemma
open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 600000

local instance coframeNontrivialTopology :
    NontrivialTopology LorentzianCoframe :=
  NontrivialTopology.of_exists_norm_ne_zero ⟨1, by simp⟩

local instance coframeDualNormedAddCommGroup :
    NormedAddCommGroup (LorentzianCoframe →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance coframeDualNormedSpace :
    NormedSpace ℝ (LorentzianCoframe →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Multiply an arbitrary fixed coframe-coordinate direction by a genuine
compact scalar bump. -/
def scalarTimesCoframeVariation
    (direction : LorentzianCoframe)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation LorentzianCoframe where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesCoframeVariation_apply
    (direction : LorentzianCoframe)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesCoframeVariation direction variation point =
      variation point • direction :=
  rfl

/-- The actual C3e1 local stress evaluated on a fixed coframe-coordinate
direction along a holonomic configuration. -/
def coframeDirectionalStressCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzianCoframe)
    (point : BasePoint) : ℝ :=
  coframeLocalStressCovector source point
    (toContinuumPointField configuration point) direction

/-- Weak coframe equation after the integrated C3e2 derivative has been
identified with the integral of the actual C3e1 local stress. -/
def CanonicalCoframeWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzianCoframe,
    (∫ point : BasePoint,
      coframeLocalStressCovector source point
        (toContinuumPointField configuration point) (variation point)) = 0

/-- Pointwise coframe equation in every actual matrix-coordinate direction.
Because `LorentzianCoframe` is the complete finite coframe carrier, this is
equivalent to vanishing of the local stress covector. -/
def CanonicalCoframePointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    coframeLocalStressCovector source point
      (toContinuumPointField configuration point) = 0

theorem canonicalCoframeWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (weakEquation : CanonicalCoframeWeakEquation source configuration)
    (direction : LorentzianCoframe)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        coframeDirectionalStressCoefficient source configuration direction
          point) = 0 := by
  have weakDirection :=
    weakEquation (scalarTimesCoframeVariation direction variation)
  simpa [coframeDirectionalStressCoefficient] using weakDirection

/-- Extract the pointwise coframe equation once continuity of the actual
directional stress has been produced internally. -/
theorem canonicalCoframeWeakEquation_implies_pointwiseEquation_of_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (stressContinuous : ∀ direction : LorentzianCoframe,
      Continuous
        (coframeDirectionalStressCoefficient source configuration direction))
    (weakEquation : CanonicalCoframeWeakEquation source configuration) :
    CanonicalCoframePointwiseEquation source configuration := by
  intro point
  apply ContinuousLinearMap.ext
  intro direction
  have directionZero :
      coframeDirectionalStressCoefficient source configuration direction = 0 := by
    apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
      (coframeDirectionalStressCoefficient source configuration direction)
      (stressContinuous direction)
    intro variation
    exact canonicalCoframeWeakEquation_direction_integral source configuration
      weakEquation direction variation
  simpa [coframeDirectionalStressCoefficient] using congrFun directionZero point

end

end SaturationMonoid.PhysicsCore.StageNineCoframePointwiseEquation

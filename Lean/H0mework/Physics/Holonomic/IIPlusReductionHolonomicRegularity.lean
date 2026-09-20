import H0mework.Physics.Exterior.IIPlusReductionLocalVariation
import H0mework.Physics.Holonomic.CoframeFormRegularity

/-!
# Joint regularity of the form-native nonlinear `II+` reduction

This module treats the coframe as the primitive family variable and computes

`B := II+(e)`

inside the active form-native candidate.  The reduced density is the actual
constraint-free readout of that computed point field, not a frozen-`B`
surrogate and not a supplied simplicity shell.

The terminal theorem derives joint `C¹` regularity from a primitive smooth
holonomic configuration at every nondegenerate candidate coframe.  No
derivative, gravity-auxiliary equation, stationarity, dominator, fixed actual,
target field, or root-action receipt enters its mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeIIPlusReductionHolonomicRegularity

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeHolonomicRegularity
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeIIPlusReductionLocalVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! ## The computed point-field and density families -/

/-- Replace the selected coframe and then compute the gravity bivector from
that same selected coframe.  All other primitive fields retain the same
configuration/point provenance. -/
def holonomicFormNativeIIPlusReducedPointFieldFamily
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (withCoframe
      (toContinuumPointField configuration joint.1) joint.2)

/-- Gravity BF/constitutive block evaluated on the computed `II+` bivector. -/
def holonomicFormNativeIIPlusReducedGravityBFDensityFamily
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedFormNativeGravityBFDensity
    (holonomicFormNativeIIPlusReducedPointFieldFamily configuration joint)

/-- Constraint-free active density evaluated on the computed nonlinear
point-field family. -/
def holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe) : ℝ :=
  generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary source
    (sourceGeneratedUnifiedCouplings source) 0 point
    (holonomicFormNativeIIPlusReducedPointFieldFamily configuration
      (point, candidate))

theorem holonomicFormNativeIIPlusReducedPointFieldFamily_affine_eq_jointPath
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) :
    holonomicFormNativeIIPlusReducedPointFieldFamily configuration
        (point, configuration.coframe point + parameter • variation point) =
      formNativeIIPlusJointLocalPathField
        (toContinuumPointField configuration point) (variation point)
          parameter := by
  apply StageNineContinuumPointField.ext <;>
    rfl

theorem
    holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily_affine_eq_reducedPath
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) :
    holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily source
        configuration point
        (configuration.coframe point + parameter • variation point) =
      formNativeIIPlusReducedLocalDensityPath source point
        (toContinuumPointField configuration point) (variation point)
          parameter := by
  unfold holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily
    formNativeIIPlusReducedLocalDensityPath
  rw [holonomicFormNativeIIPlusReducedPointFieldFamily_affine_eq_jointPath]

/-! ## Form-native gravity block with `B := II+(e)` -/

theorem
    holonomicFormNativeIIPlusReducedGravityBFDensityFamily_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint) :
    ContDiffAt ℝ ∞
      (holonomicFormNativeIIPlusReducedGravityBFDensityFamily configuration)
      center := by
  let auxiliary := fun joint : CoframeJoint =>
    physicalIIPlusBivector joint.2
  have auxiliaryFullSmooth : ContDiffAt ℝ ∞ auxiliary center := by
    exact StageNineIIPlusRestriction.physicalIIPlusBivector_contDiff.contDiffAt
      |>.comp center contDiffAt_snd
  have auxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞
        (fun joint : CoframeJoint => auxiliary joint internal spacetime)
        center :=
    fun internal spacetime =>
      contDiffAt_pi.mp (contDiffAt_pi.mp auxiliaryFullSmooth internal)
        spacetime
  have curvatureSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        holonomicGravityCurvature configuration joint.1
          internal spacetime) center :=
    fun internal spacetime =>
      (holonomicGravityCurvature_component_contDiff configuration smooth
        internal spacetime).contDiffAt.comp center contDiffAt_fst
  have dualAuxiliaryFullSmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint =>
        gravityInternalDualEquiv (auxiliary joint)) center := by
    change ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      gravityInternalDualLinear (auxiliary joint)) center
    rw [show (fun joint : CoframeJoint =>
        gravityInternalDualLinear (auxiliary joint)) =
      gravityInternalDualLinear.toContinuousLinearMap ∘ auxiliary by
      funext joint
      rfl]
    exact gravityInternalDualLinear.toContinuousLinearMap.contDiff.contDiffAt
      |>.comp center auxiliaryFullSmooth
  have dualAuxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        gravityInternalDualEquiv (auxiliary joint) internal spacetime)
        center :=
    fun internal spacetime =>
      contDiffAt_pi.mp
        (contDiffAt_pi.mp dualAuxiliaryFullSmooth internal) spacetime
  have bfSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      gravityTopologicalBFCoefficient (auxiliary joint)
        (holonomicGravityCurvature configuration joint.1)) center := by
    rw [show (fun joint : CoframeJoint =>
        gravityTopologicalBFCoefficient (auxiliary joint)
          (holonomicGravityCurvature configuration joint.1)) =
      fun joint => gravityTopologicalMixedWedgeCoefficient
        (auxiliary joint)
        (holonomicGravityCurvature configuration joint.1) by
      funext joint
      exact gravityTopologicalBFCoefficient_eq_mixed _ _]
    exact gravityTopologicalMixedWedgeCoefficient_joint_contDiffAt center
      auxiliary
      (fun joint => holonomicGravityCurvature configuration joint.1)
      auxiliarySmooth curvatureSmooth
  have constitutiveSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      gravityTopologicalWedgeCoefficient (auxiliary joint)
        (gravityInternalDualEquiv (auxiliary joint))) center :=
    gravityTopologicalWedgeCoefficient_joint_contDiffAt center auxiliary
      (fun joint => gravityInternalDualEquiv (auxiliary joint))
      auxiliarySmooth dualAuxiliarySmooth
  have scaledConstitutiveSmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint => (1 / 2 : ℝ) *
        gravityTopologicalWedgeCoefficient (auxiliary joint)
          (gravityInternalDualEquiv (auxiliary joint))) center :=
    contDiffAt_const.mul constitutiveSmooth
  have actual := bfSmooth.sub scaledConstitutiveSmooth
  change ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
    gravityTopologicalBFCoefficient (physicalIIPlusBivector joint.2)
        (holonomicGravityCurvature configuration joint.1) -
      (1 / 2 : ℝ) *
        gravityTopologicalWedgeCoefficient (physicalIIPlusBivector joint.2)
          (gravityInternalDualEquiv
            (physicalIIPlusBivector joint.2))) center
  simpa [auxiliary] using actual

/-! ## Reduced active density assembly -/

/-- The reduced gravity BF block plus the unchanged active gauge block. -/
def holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  holonomicFormNativeIIPlusReducedGravityBFDensityFamily configuration joint +
    generatedFormNativeGaugeDensityAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2)

theorem
    holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily source
        configuration) (point, candidate) := by
  have gravitySmooth :=
    holonomicFormNativeIIPlusReducedGravityBFDensityFamily_joint_contDiffAt
      configuration smooth (point, candidate)
  have gaugeSmooth :=
    generatedFormNativeGaugeDensityAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings source) configuration smooth
      (point, candidate) nondegenerate
  unfold holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily
  exact (gravitySmooth.add gaugeSmooth).of_le (by norm_num)

theorem
    holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily_eq_sector_sum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) :
    Function.uncurry
        (holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily source
          configuration) joint =
      holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily source
          configuration joint +
        holonomicFormNativeCoframeMatterDensity source configuration
          joint := by
  unfold holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily
    generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily
    holonomicFormNativeIIPlusReducedGravityBFDensityFamily
    holonomicFormNativeIIPlusReducedPointFieldFamily
    holonomicFormNativeCoframeMatterDensity
  rfl

/-- A primitive smooth configuration produces joint `C¹` regularity of the
active constraint-free density after the actual nonlinear substitution
`B := II+(e)`. -/
theorem
    holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (Function.uncurry
        (holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily source
          configuration)) (point, candidate) := by
  rw [show Function.uncurry
      (holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily source
        configuration) =
      fun joint : CoframeJoint =>
        holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily source
            configuration joint +
          holonomicFormNativeCoframeMatterDensity source configuration
            joint by
    funext joint
    exact
      holonomicFormNativeIIPlusReducedCoframeLocalDensityFamily_eq_sector_sum
        source configuration joint]
  exact
    (holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily_joint_contDiffAt
      source configuration smooth point candidate nondegenerate).add
    (holonomicFormNativeCoframeMatterDensity_joint_contDiffAt source
      configuration smooth point candidate nondegenerate)

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeIIPlusReductionHolonomicRegularity

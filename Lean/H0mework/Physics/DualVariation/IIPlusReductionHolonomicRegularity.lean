import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity
import H0mework.Physics.DualVariation.IIPlusReductionLocalVariation
import H0mework.Physics.Holonomic.IIPlusReductionHolonomicRegularity

/-!
# Joint regularity of the Dirac-dual nonlinear `II+` reduction

The coframe is the primitive family variable and the gravity bivector is
recomputed as `B := II+(e)` at the same point.  The gravity and gauge blocks
reuse their formulation-neutral joint regularity, while the scalar and
Dirac-dual matter block is evaluated directly in the repaired root.

The terminal theorem is analytic regularity only.  It consumes no old total
density derivative, action equation, stationarity receipt, fixed actual, or
target response.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusReductionHolonomicRegularity

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusReductionHolonomicRegularity
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! ## Repaired reduced family -/

/-- Constraint-free repaired density evaluated on the computed nonlinear
`II+` point-field family. -/
def holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe) : ℝ :=
  generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    source (sourceGeneratedUnifiedCouplings source) 0 point
    (holonomicFormNativeIIPlusReducedPointFieldFamily configuration
      (point, candidate))

theorem
    holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily_affine_eq_reducedPath
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) :
    holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily source
        configuration point
        (configuration.coframe point + parameter • variation point) =
      diracDualFormNativeIIPlusReducedLocalDensityPath source point
        (toContinuumPointField configuration point) (variation point)
          parameter := by
  unfold holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
    diracDualFormNativeIIPlusReducedLocalDensityPath
    holonomicFormNativeIIPlusReducedPointFieldFamily
    diracDualFormNativeIIPlusJointLocalPathField
  rfl

theorem
    holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily_eq_sector_sum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) :
    Function.uncurry
        (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration) joint =
      holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily source
          configuration joint +
        holonomicDiracDualFormNativeCoframeMatterDensity source configuration
          joint := by
  unfold
    holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
    generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily
    holonomicFormNativeIIPlusReducedGravityBFDensityFamily
    holonomicFormNativeIIPlusReducedPointFieldFamily
    holonomicDiracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rfl

/-- A primitive smooth configuration produces joint `C¹` regularity of the
repaired constraint-free density after the actual nonlinear substitution
`B := II+(e)`. -/
theorem
    holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (Function.uncurry
        (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
          source configuration)) (point, candidate) := by
  rw [show Function.uncurry
      (holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily
        source configuration) =
      fun joint : CoframeJoint =>
        holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily source
            configuration joint +
          holonomicDiracDualFormNativeCoframeMatterDensity source
            configuration joint by
    funext joint
    exact
      holonomicDiracDualFormNativeIIPlusReducedCoframeLocalDensityFamily_eq_sector_sum
        source configuration joint]
  exact
    (holonomicFormNativeIIPlusReducedGravityGaugeDensityFamily_joint_contDiffAt
      source configuration smooth point candidate nondegenerate).add
    (holonomicDiracDualFormNativeCoframeMatterDensity_joint_contDiffAt source
      configuration smooth point candidate nondegenerate)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusReductionHolonomicRegularity

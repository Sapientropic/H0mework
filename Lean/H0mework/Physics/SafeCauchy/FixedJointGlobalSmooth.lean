import H0mework.Physics.Coframe.CoframeNativeConjugateMatterGlobalRadialRegularity
import H0mework.Physics.SafeCauchy.FixedJointGlobalECJetRegularity

/-!
# Fixed P506/L0 Cauchy-safe joint-global smoothness

The post-EC current is already a smooth, nondegenerate source-generated
configuration.  Generic coframe-native primal/adjoint radial regularity now
propagates that exact current through the matter-dual writer, after which the
live gravity reaction is recomputed.  No field equation, endpoint, response,
or completed regularity certificate enters either writer.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalSmooth

open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeConjugateMatterGlobalRadialRegularity
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineRadialCurveIntegralSmoothRegularity
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev ECPath : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECPathCurrent Source Current

private abbrev Primal : StageNineHolonomicConfiguration :=
  actionGeneratedGlobalFrameTimeMatterActual ECPath

private abbrev MatterDual : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalMatterDualCurrent Source Current

private theorem ecPath_smooth : ECPath.Smooth :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalECPathCurrent_smooth

private theorem ecPath_nondegenerate : ECPath.Nondegenerate := by
  intro point
  change Matrix.det (Prepared.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

/-- The exact post-EC current generates a globally smooth adjoint response
one-form. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECPath_conjugateMatterResponseOneForm_contDiff :
    ContDiff ℝ ∞
      (coframeNativeGlobalConjugateMatterResponseOneForm ECPath) :=
  coframeNativeGlobalConjugateMatterResponseOneForm_contDiff ECPath
    ecPath_smooth ecPath_nondegenerate

private theorem primal_smooth : Primal.Smooth :=
  actionGeneratedGlobalFrameTimeMatterActual_smooth ECPath ecPath_smooth
    ecPath_nondegenerate

private theorem primal_nondegenerate : Primal.Nondegenerate :=
  actionGeneratedGlobalFrameTimeMatterActual_nondegenerate ECPath
    ecPath_nondegenerate

/-- The source-anchored adjoint radial compiler is globally smooth on the
actual post-primal current. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalPrimal_conjugateMatterRadialIncrement_contDiff :
    ContDiff ℝ ∞
      (coframeNativeGlobalConjugateMatterRadialIncrement Primal) :=
  radialCurveIntegral_contDiff_infty_of_contDiff
    (coframeNativeGlobalConjugateMatterResponseOneForm Primal)
    (coframeNativeGlobalConjugateMatterResponseOneForm_contDiff Primal
      primal_smooth primal_nondegenerate)

/-- The ordered global primal/adjoint material write preserves whole-field
smoothness. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalMatterDual_smooth :
    MatterDual.Smooth :=
  actionGeneratedGlobalFrameMatterDualActual_smooth ECPath ecPath_smooth
    ecPath_nondegenerate

/-- The complete fixed Cauchy-safe joint occurrence is globally smooth after
the final source-generated gravity reaction write. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_smooth :
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual.Smooth := by
  change (installFormNativeGravityReaction MatterDual).Smooth
  exact installFormNativeGravityReaction_smooth MatterDual
    fixedP506L0CartanECConstraintCauchySafeJointGlobalMatterDual_smooth

#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalECPath_conjugateMatterResponseOneForm_contDiff
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalPrimal_conjugateMatterRadialIncrement_contDiff
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalMatterDual_smooth
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_smooth

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalSmooth
end PhysicsCore
end SaturationMonoid

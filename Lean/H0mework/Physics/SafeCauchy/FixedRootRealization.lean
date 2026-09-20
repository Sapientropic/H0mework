import H0mework.Physics.ActionGeneration.SameHessianCauchySafeRealization
import H0mework.Physics.SafeCauchy.FixedGlobalRegularity
import H0mework.Physics.ConstrainedCauchy.FixedDirectPrefixQuadraticCoframeBoundary

/-!
# Fixed P506 same-Hessian Cauchy-safe root realization

The fixed quadratic prepared current and the fixed Cauchy-safe prepared
current are the two material stages of one source/Cartan-base-indexed
occurrence.  Both stages use the same source-generated coframe Hessian; no
target configuration, Hessian, branch, regularity proof, or obstruction
certificate is supplied to the writer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeRootRealization

open ProofFreeRicherAnholonomicSource
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineSourceActionGeneratedSameHessianCauchySafeRealization

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

/-- The fixed realization occurrence is generated only from the authoritative
source and the exact Cartan base that already generated the quadratic
Hessian. -/
def fixedP506L0CartanECConstraintCauchySafeRootRealizationOccurrence :
    SameHessianCauchySafeRealizationOccurrence Source CartanBase :=
  sourceActionGeneratedSameHessianCauchySafeRealizationOccurrence
    Source CartanBase

private abbrev Occurrence :=
  fixedP506L0CartanECConstraintCauchySafeRootRealizationOccurrence

/-- The occurrence's input is the existing quadratic prepared current,
definitionally generated from the same source/base Hessian. -/
@[simp] theorem
    fixedP506L0CartanECConstraintCauchySafeRootRealization_before_eq_quadraticPrepared :
    Occurrence.before = fixedP506L0CartanECConstraintPreparedActual :=
  rfl

/-- The occurrence's output is the existing fixed Cauchy-safe prepared
actual, not a separately supplied target. -/
@[simp] theorem
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_eq_safePrepared :
    Occurrence.after = fixedP506L0CartanECConstraintCauchySafePreparedActual :=
  rfl

/-- Both material stages use the exact fixed source-generated Hessian. -/
@[simp] theorem
    fixedP506L0CartanECConstraintCauchySafeRootRealization_hessian_eq_fixed :
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        Source CartanBase =
      fixedP506L0CartanECConstraintCauchySafeCoframeHessian :=
  rfl

/-- The generated Cauchy-safe output is globally smooth. -/
theorem fixedP506L0CartanECConstraintCauchySafeRootRealization_after_smooth :
    Occurrence.after.Smooth := by
  rw [
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_eq_safePrepared]
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth

/-- The generated Cauchy-safe output is globally nondegenerate. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_nondegenerate :
    Occurrence.after.Nondegenerate := by
  rw [
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_eq_safePrepared]
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate

/-- The generated Cauchy-safe output is noncharacteristic at every actual
spacetime point. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_noncharacteristic
    (point : BasePoint) :
    coframeTemporalPrincipalScalar (Occurrence.after.coframe point) ≠ 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_eq_safePrepared]
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
      point

/-- At the source-generated `sqrt 6` obstruction point, the safe material
strictly changes the old quadratic prepared current: the output determinant
is nonzero while the input determinant is zero. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_ne_before :
    Occurrence.after ≠ Occurrence.before := by
  intro equality
  let point :=
    fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
  have determinantEquality := congrArg
    (fun configuration : StageNineHolonomicConfiguration =>
      Matrix.det (configuration.coframe point)) equality
  exact
    (fixedP506L0CartanECConstraintCauchySafeRootRealization_after_nondegenerate
      point)
      (determinantEquality.trans
        fixedP506L0CartanECConstraintPreparedActual_determinant_zero)

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeRootRealization
end PhysicsCore
end SaturationMonoid

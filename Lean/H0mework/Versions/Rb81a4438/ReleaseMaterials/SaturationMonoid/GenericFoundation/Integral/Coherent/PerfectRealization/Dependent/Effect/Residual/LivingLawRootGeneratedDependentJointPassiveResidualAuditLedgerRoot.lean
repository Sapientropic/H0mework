import H0mework.Versions.Rb81a4438.Realization.JointEffect.ResidualCoface
import H0mework.Versions.R2.Realization.Audit.LedgerRoot

/-!
# Audit ledger root of an exact passive residual

The exact passive residual's indexed low-universe token specializes the
generic residual audit root.  Its one generated finite-patch row is the same
row already exposed by the free residual world and extended U7 calculus.  Old
rows remain the identity remainder.  The audit target has an exact readback to
the compiler successor carried by the original passive residual.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open RootGeneratedResidualAdmission
open RootGeneratedResidualAuditLedger
open RootLawDependentJointStateController

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {step : StepAt recognition visit}

abbrev PassiveResidualAuditLedgerRootAt
    (residual : RootedPassiveResidualAt step) :=
  auditLedgerRoot N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)

def passiveResidualAuditLedgerRoot
    (residual : RootedPassiveResidualAt step) :
    SourceNativeLedgerRootClosure (ResidualWorldAt residual) AuditV :=
  auditLedgerRoot N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)

def passiveResidualGeneratedRow
    (residual : RootedPassiveResidualAt step) :=
  residualGeneratedRow N residual.support (ResidualCoordinateAt residual)
    (residualCoordinate residual)

theorem passiveResidualGeneratedRow_commutes
    (residual : RootedPassiveResidualAt step) :
    (passiveResidualGeneratedRow residual).CommutesWithWorld :=
  residualGeneratedRow_commutes_with_world N residual.support
    (ResidualCoordinateAt residual) (residualCoordinate residual)

theorem inheritedEntry_is_identity_remainder
    (residual : RootedPassiveResidualAt step)
    (entry : OpenResponsibilityAt N residual.support) :
    sourceNativeFiniteLedgerPatchGeneratedEntry?
      (auditSource N residual.support (ResidualCoordinateAt residual))
      (auditCompiler N residual.support (ResidualCoordinateAt residual)
        (residualCoordinate residual)).ExactTransitionAt
      (auditCompiler N residual.support (ResidualCoordinateAt residual)
        (residualCoordinate residual)).writeRowSource
      (auditCompiler N residual.support (ResidualCoordinateAt residual)
        (residualCoordinate residual)).terminalRowSource
      ((auditCompiler N residual.support (ResidualCoordinateAt residual)
        (residualCoordinate residual)).compile
          (initialOccurrence N residual.support
            (ResidualCoordinateAt residual)))
      ((auditCompiler N residual.support (ResidualCoordinateAt residual)
        (residualCoordinate residual)).compilePatch
          (initialOccurrence N residual.support
            (ResidualCoordinateAt residual)))
      (oldEntry entry) = none :=
  oldEntry_is_identity_remainder N residual.support
    (ResidualCoordinateAt residual) (residualCoordinate residual) entry

/-- Read the two audit charts back into the original root current language.
The target chart is the exact compiler successor stored by the residual. -/
def passiveAuditResumeCurrent
    (residual : RootedPassiveResidualAt step) : AuditV.Current → V.Current
  | ⟨false⟩ => visit.current
  | ⟨true⟩ => residual.successor.targetCurrent

@[simp] theorem passiveAuditResumeCurrent_initial
    (residual : RootedPassiveResidualAt step) :
    passiveAuditResumeCurrent residual (ULift.up false) = visit.current :=
  rfl

@[simp] theorem passiveAuditResumeCurrent_target
    (residual : RootedPassiveResidualAt step) :
    passiveAuditResumeCurrent residual (ULift.up true) =
      residual.successor.targetCurrent :=
  rfl

theorem audit_next_reads_original_successor
    (residual : RootedPassiveResidualAt step) :
    ((passiveResidualAuditLedgerRoot residual).toRoot.evolutionAt
        (ULift.up false)).nextCurrent? = some (ULift.up true) ∧
      passiveAuditResumeCurrent residual (ULift.up true) =
        residual.successor.targetCurrent ∧
      RootLawDependentJointTransition.stepSuccessor? step =
        some residual.successor :=
  ⟨rfl, rfl, residual.successor_exact⟩

theorem passiveResidualAuditLedgerMouth
    (residual : RootedPassiveResidualAt step) :
    HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit ∧
      (passiveResidualGeneratedRow residual).CommutesWithWorld ∧
      ((passiveResidualAuditLedgerRoot residual).toRoot.evolutionAt
        (ULift.up false)).nextCurrent? = some (ULift.up true) ∧
      passiveAuditResumeCurrent residual (ULift.up true) =
        residual.successor.targetCurrent :=
  ⟨residual.wholeLedger_rooted, residual.next_rooted,
    passiveResidualGeneratedRow_commutes residual, rfl, rfl⟩

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

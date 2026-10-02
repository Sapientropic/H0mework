import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Projection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation

open SourceOperationEffects SourceOperationNative SourceOperationExecution
open DebtActivationWorld DebtActivationLedger
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

namespace New
export RootGeneratedDebtActivationJointSource.Native
  (Current World JointV source native ledgerRoot targetCurrent emitted patch rows rows_size
    mathSource mathRowEvolution projectionLaw original_projection_outcome)
end New

noncomputable section
variable (runtime : LivingRuntimeState process) (depth : Nat)

def program : RootGeneratedDebtActivationJointSource.Native.Program (lower runtime) where
  emit current := (RootGeneratedDebtActivationJointSource.Native.read? (lower runtime) current).get (by rfl)

theorem original_rows (oldCurrent : Joint.Current (SourcePhysicalCalculationAdmission.registered runtime)) :
    ((program runtime).emit oldCurrent).rows.size = 2 := rfl

theorem original_image (oldCurrent : Joint.Current (SourcePhysicalCalculationAdmission.registered runtime)) :
    ((program runtime).emit oldCurrent).evolution =
      (RootGeneratedDebtActivationJointSource.Unit.patch
        (SourcePhysicalCalculationAdmission.registered runtime) oldCurrent).toLedgerWriteEvolution := rfl

def native : RootGeneratedDebtActivationJointSource.NativeAt (initialEvent runtime depth) :=
  (RootGeneratedDebtActivationJointSource.compileNative? (initialEvent runtime depth)).get (by rfl)

theorem native_generated : RootGeneratedDebtActivationJointSource.compileNative? (initialEvent runtime depth) =
    some (native runtime depth) := rfl

theorem native_next : (Joint.JointV (SourcePhysicalCalculationAdmission.registered runtime)).nativeTarget
    (native runtime depth).write = mathCurrent runtime (depth + 1) := rfl

theorem native_original_receipt : (native runtime depth).baseLedger =
    (Consumer.canonicalSuccessor runtime depth).ledgerEvolution := rfl

theorem native_next_state : (native runtime depth).nextEvent.state = (firstStep runtime depth).1 := by
  exact (native runtime depth).next_state.trans (by
    unfold RootGeneratedDebtActivationJointSource.mathTarget
    rw [firstStep_generated])

theorem native_next_budget : remaining (native runtime depth).nextEvent.state.1 = 9 := by
  rw [native_next_state]
  exact firstStep_budget runtime depth

theorem native_next_owner : (native runtime depth).nextEvent.owner =
    mathEntry runtime (depth + 1) := by
  change ((Consumer.canonicalSuccessor runtime depth).ledgerEvolution.destination (mathEntry runtime depth)).1 = _
  change RootGeneratedDebtActivationJointSource.Unit.targetRow
    (SourcePhysicalCalculationAdmission.registered runtime) (mathCurrent runtime depth)
    ((RootGeneratedDebtActivationJointSource.Unit.rowInventory
      (SourcePhysicalCalculationAdmission.registered runtime) (mathCurrent runtime depth)).backward
      ((RootGeneratedDebtActivationJointSource.Unit.rowInventory
        (SourcePhysicalCalculationAdmission.registered runtime) (mathCurrent runtime depth)).forward 1)) = _
  rw [(RootGeneratedDebtActivationJointSource.Unit.rowInventory
    (SourcePhysicalCalculationAdmission.registered runtime) (mathCurrent runtime depth)).backward_forward]
  exact RootGeneratedDebtActivationJointSource.Unit.targetRow_inventory
    (SourcePhysicalCalculationAdmission.registered runtime) (mathCurrent runtime depth) 1

def worldLaw : DebtActivationLaw := RootGeneratedDebtActivationJointSource.Idle.law
  (registered runtime depth).input.environment (registered runtime depth).input.expression

def payer : LedgerWriteEvolutionAt (ExtendedNetwork (NewN runtime) (worldLaw runtime depth))
    (activeLedger ((lower runtime).source.source.toRootSource.account.supportOf (occurrence runtime depth))
      (initialEvent runtime depth).state)
    (activeLedger ((lower runtime).source.source.toRootSource.account.supportOf
      (native runtime depth).targetOccurrence) (firstStep runtime depth).1) := by
  have paid := RootGeneratedDebtActivationJointSource.payment (native runtime depth)
  unfold RootGeneratedDebtActivationJointSource.PaymentAt at paid
  rw [firstStep_generated] at paid
  exact paid

theorem payer_generated : payer runtime depth = jointStepLedgerEvolution
    (law := worldLaw runtime depth) (native runtime depth).baseLedger
    (initialEvent runtime depth).owner (firstStep runtime depth).2 := rfl

theorem payer_old_receipt (entry : OpenResponsibilityAt (NewN runtime)
    ((lower runtime).source.source.toRootSource.account.supportOf (occurrence runtime depth))) :
    HEq ((payer runtime depth).destination
      (oldEntry (law := worldLaw runtime depth) (state? := some (initialEvent runtime depth).state) entry)).2
      (jointOldEvolution (law := worldLaw runtime depth) (firstStep runtime depth).2
        ((native runtime depth).baseLedger.destination entry).2) := by
  rw [payer_generated]
  exact jointStepLedgerEvolution_destination_old_evolution _ _ _ entry

theorem payer_math_strict :
    ((payer runtime depth).destination (debtEntry (N := NewN runtime) (law := worldLaw runtime depth)
      ((lower runtime).source.source.toRootSource.account.supportOf (occurrence runtime depth))
      (initialEvent runtime depth).state)).1.progressBudget <
      (debtEntry (N := NewN runtime) (law := worldLaw runtime depth)
        ((lower runtime).source.source.toRootSource.account.supportOf (occurrence runtime depth))
        (initialEvent runtime depth).state).progressBudget := by
  rw [payer_generated]
  exact jointStepLedgerEvolution_debt_strict _ _ _

def jointRoot := New.ledgerRoot (program runtime) (registered runtime depth)
def jointInitial : New.Current (registered runtime depth) := (New.source (program runtime) (registered runtime depth)).initial
def jointOccurrence := (jointRoot runtime depth).emitted (jointInitial runtime depth)
def jointPatch := New.patch (program runtime) (registered runtime depth) (jointInitial runtime depth)

theorem joint_rows : (New.rows (program runtime) (registered runtime depth) (jointInitial runtime depth)).size = 3 := by
  exact (New.rows_size (program runtime) (registered runtime depth) (jointInitial runtime depth)).trans
    (congrArg (fun size => size + 1) (original_rows runtime (jointInitial runtime depth).1))

theorem joint_initial_old : (jointInitial runtime depth).1 = current runtime depth := rfl
theorem joint_initial_history : (jointInitial runtime depth).1.2.state = oldHistory runtime depth := rfl

theorem joint_native : New.native (program runtime) (registered runtime depth) (jointInitial runtime depth) =
    native runtime depth := rfl

def jointSuccessor : SourceNativeLedgerGeneratedSuccessorAt (jointOccurrence runtime depth)
    ((jointRoot runtime depth).generatedLedgerAt (jointInitial runtime depth)) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((jointRoot runtime depth).generatedLedgerAt (jointInitial runtime depth))).get (by rfl)

theorem joint_next_old : (jointSuccessor runtime depth).targetCurrent.1 = mathCurrent runtime (depth + 1) := rfl

theorem joint_next_state : (jointSuccessor runtime depth).targetCurrent.2.state = (firstStep runtime depth).1 :=
  native_next_state runtime depth

theorem joint_next_owner : (jointSuccessor runtime depth).targetCurrent.2.owner = mathEntry runtime (depth + 1) :=
  native_next_owner runtime depth

def jointMathEntry := New.mathSource (registered runtime depth) (jointInitial runtime depth)

theorem joint_math_receipt :
    HEq ((jointSuccessor runtime depth).ledgerEvolution.destination (jointMathEntry runtime depth)).2
      (New.mathRowEvolution (program runtime) (registered runtime depth) (jointInitial runtime depth)) := HEq.rfl

theorem joint_math_initial_budget : (jointMathEntry runtime depth).progressBudget = 10 := rfl

theorem joint_math_target_budget :
    ((jointSuccessor runtime depth).ledgerEvolution.destination (jointMathEntry runtime depth)).1.progressBudget = 9 :=
  native_next_budget runtime depth

def jointProjectionLaw := New.projectionLaw (program runtime) (registered runtime depth)
  (targetRoot runtime).source.base.projectionLaw

theorem joint_original_projection (projection : (targetRoot runtime).source.base.projectionLaw.Projection) :
    HEq ((jointProjectionLaw runtime depth).outcomeAt (.inl projection) (jointOccurrence runtime depth))
      ((targetRoot runtime).source.base.projectionLaw.outcomeAt projection (occurrence runtime depth)) :=
  New.original_projection_outcome (program runtime) (registered runtime depth)
    (targetRoot runtime).source.base.projectionLaw (jointOccurrence runtime depth) projection

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

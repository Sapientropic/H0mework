import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.ResidualSource
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Authority
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Birth
import H0mework.Foundation.Responsibility.JointSource.Progress

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.ResidualAdmission

open SourceOperationEffects SourceOperationExecution DebtActivationWorld RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section
variable (runtime : LivingRuntimeState process) (depth : Nat)

abbrev oldState := SourcePhysicalCalculationAdmission.Inquiry.mathState runtime depth
abbrev request := ResidualSource.registered runtime depth

def inputs (_query : (oldState runtime depth).Query) := request runtime depth

theorem owners (query : (oldState runtime depth).Query) :
    (inputs runtime depth query).input.owner = (oldState runtime depth).entryAt query := by
  cases query
  rfl

def birthState := RootGeneratedDebtActivationJointSource.Native.Request.birthState
  (oldState runtime depth) (program runtime) (inputs runtime depth) (identityScope runtime) (owners runtime depth)

private theorem notSettled (settled : SourceOperationExecutionDebt.Settlement
    (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.law (request runtime depth)).settlement_budget_zero settled
  have budget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget
    (ResidualSource.sourceMaterial runtime depth)
  change remaining (request runtime depth).input.expression = 0 at zero
  change remaining (request runtime depth).input.expression = _ at budget
  omega

def firstStep : GeneratedStepAt (RootGeneratedDebtActivationJointSource.law (request runtime depth))
    (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth)).state :=
  match RootGeneratedDebtActivationJointSource.mathAction
      (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth)) with
  | .inl settled => False.elim (notSettled runtime depth settled)
  | .inr paid => paid

theorem firstStep_generated : RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth)) = .inr (firstStep runtime depth) := by
  cases selected : RootGeneratedDebtActivationJointSource.mathAction
      (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth)) with
  | inl settled => exact False.elim (notSettled runtime depth settled)
  | inr paid => simp only [firstStep, selected]

def sourceEvent := (oldState runtime depth).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (oldState runtime depth).visit

def generated := (RootGeneratedDebtActivationJointSource.Native.Request.birthProgramAt
  (oldState runtime depth) (program runtime) (inputs runtime depth) (identityScope runtime)
  (owners runtime depth) PUnit.unit (firstStep runtime depth) (firstStep_generated runtime depth)).generate
    (sourceEvent runtime depth)

theorem birth_root : (birthState runtime depth).root = (oldState runtime depth).root := rfl
theorem birth_visit : (birthState runtime depth).visit = (oldState runtime depth).visit := rfl

theorem birth_compiles : (birthState runtime depth).compileInquiry PUnit.unit = .debtAdmission (generated runtime depth) := by
  exact RootGeneratedDebtActivationJointSource.Native.Request.birthState_compiles_paid
    (oldState runtime depth) (program runtime) (inputs runtime depth) (identityScope runtime)
    (owners runtime depth) PUnit.unit (firstStep runtime depth) rfl
    (firstStep_generated runtime depth)

theorem first_budget (zero : Consumer.budget runtime depth = 0) :
    remaining (firstStep runtime depth).1.1 = 11 := by
  have next : RootGeneratedDebtActivationJointSource.mathTarget
      (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth)) = (firstStep runtime depth).1 := by
    unfold RootGeneratedDebtActivationJointSource.mathTarget
    rw [firstStep_generated]
  have debit := RootGeneratedDebtActivationJointSource.mathTarget_budget
    (RootGeneratedDebtActivationJointSource.initialEvent (request runtime depth))
  rw [next] at debit
  change remaining (firstStep runtime depth).1.1 = remaining (request runtime depth).input.expression - 1 at debit
  rw [ResidualSource.completed_budget runtime depth zero] at debit
  exact debit

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation.ResidualAdmission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

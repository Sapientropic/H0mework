import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.ResidualAdmission
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Runtime
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Completion

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.ResidualRuntime

open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

namespace Admission
export ResidualAdmission (oldState request inputs owners firstStep firstStep_generated first_budget)
end Admission

noncomputable section
variable (runtime : LivingRuntimeState process) (depth : Nat)

local instance : Unique (Admission.oldState runtime depth).Query := (inferInstance : Unique PUnit)

def payments (query : (Admission.oldState runtime depth).Query) := by
  cases query
  exact Admission.firstStep runtime depth

theorem actions (query : (Admission.oldState runtime depth).Query) :
    RootGeneratedDebtActivationJointSource.mathAction
      (RootGeneratedDebtActivationJointSource.initialEvent (Admission.inputs runtime depth query)) =
        .inr (payments runtime depth query) := by
  cases query
  exact Admission.firstStep_generated runtime depth

theorem audits (query : (Admission.oldState runtime depth).Query) :
    ((Admission.oldState runtime depth).compileInquiry query).audit = .answered := by cases query; rfl

def inquiry := RootGeneratedDebtActivationJointSource.Native.Request.inquiryRuntime
  (Admission.oldState runtime depth) (program runtime) (Admission.inputs runtime depth) (identityScope runtime)
  (Admission.owners runtime depth) (payments runtime depth) (actions runtime depth) (audits runtime depth)

theorem initial_kind : (inquiry runtime depth |>.tickAt 0).resolutionKind = .debtAdmission :=
  RootGeneratedDebtActivationJointSource.Native.Request.initial_resolution_kind
    (Admission.oldState runtime depth) (program runtime) (Admission.inputs runtime depth) (identityScope runtime)
    (Admission.owners runtime depth) (payments runtime depth) (actions runtime depth) (audits runtime depth)

theorem actual_node (count : Nat) :
    ((inquiry runtime depth).stateAt (count + 1)).engine.node = .active
      (RootGeneratedDebtActivationJointSource.Native.Request.mathPresentation
        (Admission.oldState runtime depth) (program runtime) (Admission.request runtime depth)
        (identityScope runtime) count) :=
  RootGeneratedDebtActivationJointSource.Native.Request.stateAt_afterBirth_node
    (Admission.oldState runtime depth) (program runtime) (Admission.inputs runtime depth) (identityScope runtime)
    (Admission.owners runtime depth) (payments runtime depth) (actions runtime depth) (audits runtime depth) count

def completed := RootGeneratedDebtActivationJointSource.Native.Request.Completion.completed
  (Admission.oldState runtime depth) (program runtime) (Admission.request runtime depth) (identityScope runtime)

theorem completed_value (zero : Consumer.budget runtime depth = 0) :
    (completed runtime depth).1 = Consumer.physicalPair runtime depth -
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (RootGeneratedDebtActivationJointSource.Native.Request.Completion.completed_value
    (Admission.oldState runtime depth) (program runtime) (Admission.request runtime depth)
    (identityScope runtime)).trans (ResidualSource.completed_value runtime depth zero)

theorem completed_history_length (zero : Consumer.budget runtime depth = 0) :
    (RootGeneratedDebtActivationJointSource.Native.Request.Completion.completedEvent
      (Admission.oldState runtime depth) (program runtime) (Admission.request runtime depth)
      (identityScope runtime)).state.2.length = 12 :=
  (RootGeneratedDebtActivationJointSource.Native.Request.Completion.completed_history_length
    (Admission.oldState runtime depth) (program runtime) (Admission.request runtime depth)
    (identityScope runtime)).trans (ResidualSource.completed_budget runtime depth zero)

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation.ResidualRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

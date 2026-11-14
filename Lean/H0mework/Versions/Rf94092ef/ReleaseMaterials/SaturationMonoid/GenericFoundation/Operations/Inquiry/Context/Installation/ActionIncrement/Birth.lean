import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Installation.ActionIncrement
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Environment
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Installation

open SourceOperationEffects SourceOperationExecution
namespace Birth
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (nextBorn actualOccurrence actualVisit request)
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source (request_budget)
end Birth

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : C.Frame (Value := Value) (Var := Var) (sort := sort))
variable (configuration : Birth.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

/-- The first local action of the new registered request still has a primitive Step to execute. -/
theorem born_math_action_paid :
    let born := Birth.nextBorn frame configuration
    ∃ paid, born.action = Sum.inr paid := by
  let born := Birth.nextBorn frame configuration
  have budget := SourceRegisteredClaimClock.remainder_generated born
  change remaining born.event.state.1 = remaining (Birth.request frame).input.expression - 1 at budget
  have fromSource := Birth.request_budget frame.old frame.registered frame.packetAt frame.environment frame.depth
  change remaining (Birth.request frame).input.expression =
    remaining frame.rawRead.expression + remaining frame.paidRead.state.1 + 2 at fromSource
  have positive : 0 < remaining born.event.state.1 := by omega
  change ∃ paid, born.action = Sum.inr paid
  cases action : born.action with
  | inl settled =>
      have zero := (SourceOperationExecutionDebt.law born.registered.input.environment
        born.registered.input.expression).settlement_budget_zero settled
      change remaining born.event.state.1 = 0 at zero
      omega
  | inr paid => exact ⟨paid,rfl⟩

/-- The newborn request's first local action keeps its registered raw environment. -/
theorem born_local_increment_zero :
    let born := Birth.nextBorn frame configuration
    executedEnvironmentIncrement (Birth.epoch born) (Birth.actualOccurrence born) = 0 := by
  let born := Birth.nextBorn frame configuration
  obtain ⟨paid, actual⟩ := born_math_action_paid frame configuration
  change executedEnvironmentIncrement (Birth.epoch born) (Birth.actualOccurrence born) = 0
  have generated : RootGeneratedDebtActivationJointSource.mathAction (Birth.actualVisit born).current.2 =
      Sum.inr paid := actual
  simp only [executedEnvironmentIncrement, generated]

end SourceOperationInquiry.Context.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

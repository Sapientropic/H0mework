import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source
import H0mework.Realization.Operations.Execution.Relations.History.Events
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects SourceOperationExecution
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N₁ N₂ : WorldRelationNetwork.{u}} {V₁ V₂ : Vocabulary.{u}}
variable (left : SourceNativeAuthoritativeRootClosure N₁ V₁) (leftOrigin : V₁.Current)
variable (right : SourceNativeAuthoritativeRootClosure N₂ V₂) (rightOrigin : V₂.Current)
variable (input : Raw (Value:=Value) (Var:=Var) (sort:=sort))
def inputNext (state : SourceOperationExecutionDebt.State input.environment input.expression) :
    SourceOperationExecutionDebt.State input.environment input.expression :=
  match SourceOperationExecutionDebt.generate input.environment input.expression state with
  | .inl _ => state
  | .inr paid => paid.1

theorem nextState_input (state : SourceOperationExecutionDebt.State input.environment input.expression) :
    nextState left leftOrigin (fun _ => input) state = inputNext input state := by
  unfold nextState targetOf action raw inputNext
  generalize SourceOperationExecutionDebt.generate input.environment input.expression state = selected
  cases selected <;> rfl

theorem common_raw_state (count : Nat) :
    Completion.state left leftOrigin (fun _ => input) count =
      Completion.state right rightOrigin (fun _ => input) count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      rw [Completion.next_state,Completion.next_state]
      exact (nextState_input left leftOrigin input _).trans
        ((congrArg (inputNext input) previous).trans (nextState_input right rightOrigin input _).symm)

theorem common_raw_trace : HEq (Consumer.trace left leftOrigin (fun _ => input))
    (Consumer.trace right rightOrigin (fun _ => input)) := by
  have same : Consumer.targetState left leftOrigin (fun _ => input) =
      Consumer.targetState right rightOrigin (fun _ => input) :=
    (Calculation.target_state left leftOrigin (fun _ => input)).trans
      ((common_raw_state left leftOrigin right rightOrigin input (remaining input.expression)).trans
        (Calculation.target_state right rightOrigin (fun _ => input)).symm)
  unfold Consumer.trace
  rw [same]
  rfl

theorem common_raw_exposure :
    SourceOperationPaidRelations.exposure (Consumer.trace left leftOrigin (fun _ => input)) =
      SourceOperationPaidRelations.exposure (Consumer.trace right rightOrigin (fun _ => input)) := by
  have same : Consumer.targetState left leftOrigin (fun _ => input) =
      Consumer.targetState right rightOrigin (fun _ => input) :=
    (Calculation.target_state left leftOrigin (fun _ => input)).trans
      ((common_raw_state left leftOrigin right rightOrigin input (remaining input.expression)).trans
        (Calculation.target_state right rightOrigin (fun _ => input)).symm)
  exact congrArg (fun state : SourceOperationExecutionDebt.State input.environment input.expression =>
    SourceOperationPaidRelations.exposure state.2) same

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

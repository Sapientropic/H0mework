import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Foundation.Responsibility.JointSource.Progress

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion

open SourceOperationEffects SourceOperationExecution RootGeneratedDebtActivationJointSource RootInquiryCompletion

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (configuration : Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

theorem mathNext_state (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :
    frame.mathNext.event.state = mathTarget frame.event := rfl
theorem paid_decreases (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (paid : DebtActivationWorld.GeneratedStepAt
      (Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state)
    (selected : frame.action = .inr paid) :
    remaining (next frame configuration).event.state.1 < remaining frame.event.state.1 := by
  have same : next frame configuration = frame.mathNext := by unfold next; rw [selected]
  rw [same, mathNext_state]
  have positive : remaining paid.1.1 < remaining frame.event.state.1 :=
    (Idle.law frame.registered.input.environment frame.registered.input.expression).step_budget_lt paid.2
  have budget := mathTarget_budget frame.event
  omega
/-- The actual settlement and its paid-distance bound are retained in Type. -/
abbrev Receipt (initial : M.Frame (Value := Value) (Var := Var) (sort := sort)) (start : Nat) :=
  Σ distance : Nat,
    { settled : SourceOperationExecutionDebt.Settlement (frames initial configuration (start + distance)).event.state //
      distance ≤ remaining (frames initial configuration start).event.state.1 ∧
        (frames initial configuration (start + distance)).action = .inl settled }

/-- Recursion follows only actual paid steps; settlement is read from the source action. -/
def receipt (initial : M.Frame (Value := Value) (Var := Var) (sort := sort)) (start : Nat) :
    Receipt configuration initial start := by
  let rank (stage : Nat) := remaining (frames initial configuration stage).event.state.1
  have generate : ∀ bound : Nat, ∀ stage : Nat, rank stage = bound → Receipt configuration initial stage := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound smaller =>
        intro stage atBound
        let frame := frames initial configuration stage
        cases selected : frame.action with
        | inl settled =>
            refine ⟨0, ?_⟩
            simpa only [Nat.add_zero] using
              (show { settled : SourceOperationExecutionDebt.Settlement frame.event.state //
                  0 ≤ remaining frame.event.state.1 ∧ frame.action = .inl settled } from
                ⟨settled, Nat.zero_le _, selected⟩)
        | inr paid =>
            have less := paid_decreases configuration frame paid selected
            change rank (stage + 1) < rank stage at less
            rw [atBound] at less
            let later := smaller (rank (stage + 1)) less (stage + 1) rfl
            refine ⟨later.1 + 1, ?_⟩
            have indices : stage + (later.1 + 1) = (stage + 1) + later.1 := by omega
            rw [indices]
            refine ⟨later.2.1, ?_, later.2.2.2⟩
            have bounded := later.2.2.1
            change later.1 ≤ rank (stage + 1) at bounded
            change later.1 + 1 ≤ rank stage
            omega
  exact generate (rank start) start rfl

abbrev atReceipt (initial : M.Frame (Value := Value) (Var := Var) (sort := sort)) (start : Nat) :=
  frames initial configuration (start + (receipt configuration initial start).1)

/-- The receipt selects an actual canonical macro tick whose successor is the decoded birth. -/
theorem receipt_next (initial : M.Frame (Value := Value) (Var := Var) (sort := sort)) (start : Nat) :
    ((runtime initial configuration).tickAt (start + (receipt configuration initial start).1)).next.node =
      .active (presentation (nextBorn (atReceipt configuration initial start) configuration) configuration) := by
  let generated := receipt configuration initial start
  have actual := actual_next initial configuration (start + generated.1)
  have same : frames initial configuration ((start + generated.1) + 1) =
      nextBorn (atReceipt configuration initial start) configuration := by
    change next (frames initial configuration (start + generated.1)) configuration = _
    unfold next
    rw [generated.2.2.2]
  exact actual.trans (congrArg (fun frame => RootInquiryProcessNode.active (presentation frame configuration)) same)

/-- The same actual settlement selects the original debt-admission compiler branch. -/
theorem receipt_compiles (initial : M.Frame (Value := Value) (Var := Var) (sort := sort)) (start : Nat) : type_of%
    (compiles_settled (atReceipt configuration initial start) configuration
      (receipt configuration initial start).2.1 (receipt configuration initial start).2.2.2) :=
  compiles_settled (atReceipt configuration initial start) configuration
    (receipt configuration initial start).2.1 (receipt configuration initial start).2.2.2

end SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

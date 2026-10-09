import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Environment

/-! Actual paid-prefix witnesses and stable readouts of the existing receipt. -/

set_option autoImplicit false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix
open SourceOperationEffects SourceOperationExecution
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
end A
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active mathNext frames_constant)
end E
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (configuration : Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (initial : M.Frame (Value := Value) (Var := Var) (sort := sort))

theorem prefix_budget (start offset : Nat)
    (within : offset ≤ remaining (A.frames initial configuration start).event.state.1) :
    remaining (A.frames initial configuration (start + offset)).event.state.1 =
      remaining (A.frames initial configuration start).event.state.1 - offset := by
  induction offset with
  | zero => simp only [Nat.add_zero, Nat.sub_zero]
  | succ offset previous =>
      have prior := previous (by omega)
      let frame := A.frames initial configuration (start + offset)
      have positive : 0 < remaining frame.event.state.1 := by
        change 0 < remaining (A.frames initial configuration (start + offset)).event.state.1
        omega
      cases actual : frame.action with
      | inl settled =>
          have zero : remaining frame.event.state.1 = 0 := by rw [settled.2.down]; rfl
          omega
      | inr paid =>
          have indices : start + (offset + 1) = (start + offset) + 1 := by omega
          have same : A.frames initial configuration (start + (offset + 1)) = frame.mathNext := by
            rw [indices]
            change A.next frame configuration = frame.mathNext
            unfold A.next
            rw [actual]
          have next := congrArg (fun candidate : M.Frame
            (Value := Value) (Var := Var) (sort := sort) => remaining candidate.event.state.1) same
          have debit := (congrArg (fun state => remaining state.1) (mathNext_state frame)).trans
            (RootGeneratedDebtActivationJointSource.mathTarget_budget frame.event)
          have difference : remaining frame.event.state.1 - 1 =
              remaining (A.frames initial configuration start).event.state.1 - (offset + 1) := by
            change remaining (A.frames initial configuration (start + offset)).event.state.1 - 1 = _
            omega
          exact next.trans (debit.trans difference)

def paid_at_offset (start offset : Nat)
    (within : offset < remaining (A.frames initial configuration start).event.state.1) :
    Σ paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law (A.frames initial configuration (start + offset)).registered.input.environment
        (A.frames initial configuration (start + offset)).registered.input.expression)
      (A.frames initial configuration (start + offset)).event.state,
      PLift ((A.frames initial configuration (start + offset)).action = .inr paid) := by
  have budget := prefix_budget configuration initial start offset (Nat.le_of_lt within)
  have positive : 0 < remaining (A.frames initial configuration (start + offset)).event.state.1 := by omega
  cases actual : (A.frames initial configuration (start + offset)).action with
  | inr paid => exact ⟨paid, ⟨rfl⟩⟩
  | inl settled =>
      have zero : remaining (A.frames initial configuration (start + offset)).event.state.1 = 0 := by
        rw [settled.2.down]; rfl
      omega

theorem receipt_distance_exact (start : Nat) :
    (receipt configuration initial start).1 = remaining (A.frames initial configuration start).event.state.1 := by
  let actual := receipt configuration initial start
  have budget := prefix_budget configuration initial start actual.1 actual.2.2.1
  have zero : remaining (A.frames initial configuration (start + actual.1)).event.state.1 = 0 := by
    rw [actual.2.1.2.down]; rfl
  have bounded := actual.2.2.1
  change actual.1 = _
  omega

def receipt_paid_prefix (start : Nat) (offset : Fin (receipt configuration initial start).1) :=
  paid_at_offset configuration initial start offset.val
    (lt_of_lt_of_le offset.isLt (Nat.le_of_eq (receipt_distance_exact configuration initial start)))

theorem receipt_read {Read : Sort v} (read : Nat → Read)
    (stable : ∀ stage,
      (paid : DebtActivationWorld.GeneratedStepAt
        (RootGeneratedDebtActivationJointSource.Idle.law (A.frames initial configuration stage).registered.input.environment
          (A.frames initial configuration stage).registered.input.expression)
        (A.frames initial configuration stage).event.state) →
        (A.frames initial configuration stage).action = .inr paid → read (stage + 1) = read stage)
    (start : Nat) : read (start + (receipt configuration initial start).1) = read start := by
  have transport : ∀ offset, offset ≤ remaining (A.frames initial configuration start).event.state.1 →
      read (start + offset) = read start := by
    intro offset
    induction offset with
    | zero => intro _; rfl
    | succ offset previous =>
        intro within
        let paid := paid_at_offset configuration initial start offset (by omega)
        have step := stable (start + offset) paid.1 paid.2.down
        have prior := previous (by omega)
        have indices : start + (offset + 1) = (start + offset) + 1 := by omega
        exact (congrArg read indices).trans (step.trans prior)
  exact transport _ (receipt configuration initial start).2.2.1

theorem receipt_environment {env : Env Value Var} (same : E.At initial env) (start : Nat) :
    (A.frames initial configuration (start + (receipt configuration initial start).1)).activeEnvironment =
      (A.frames initial configuration start).activeEnvironment := by
  apply receipt_read configuration initial (fun stage => (A.frames initial configuration stage).activeEnvironment)
  intro stage paid actual
  have next : A.frames initial configuration (stage + 1) =
      (A.frames initial configuration stage).mathNext := by
    change A.next _ _ = _
    unfold A.next
    rw [actual]
  exact (congrArg (fun frame : M.Frame
    (Value := Value) (Var := Var) (sort := sort) => frame.activeEnvironment) next).trans
      (E.active (E.mathNext (E.frames_constant configuration same stage)))
end SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

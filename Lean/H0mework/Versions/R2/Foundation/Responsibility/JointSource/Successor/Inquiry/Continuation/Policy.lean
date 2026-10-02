import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Occurrence
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Policy

/-! Reuse the existing source-syntax and causal-depth ordinal. Birth increases
syntax through the actual residual; an ordinary action increases source depth. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open Native.Restructuring.Inquiry.Continuation (Before before_trans before_irrefl erasedDepth)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def rank : Nat × Nat := (remaining frame.rawRead.expression, frame.depth + 1)

private theorem finiteDepth (depth : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
      (Inquiry.finiteVisit frame.old frame.registered frame.packetAt depth).history = depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (Inquiry.finiteVisit frame.old frame.registered frame.packetAt depth).history + 1 = depth + 1
      exact congrArg (fun count => count + 1) prior

theorem rank_depth : erasedDepth frame.presentation.erase = frame.rank.2 := by
  rw [frame.presentation_erase]
  exact frame.finiteDepth (frame.depth + 1)

theorem born_rank : frame.born.rank =
    (frame.rank.1 + remaining frame.paidRead.state.1 + 2, 1) :=
  Prod.ext frame.request_budget rfl

theorem math_rank : frame.mathNext.rank = (frame.rank.1, frame.rank.2 + 1) := rfl

theorem next_progress : Before frame.rank frame.next.rank := by
  unfold next nextFrom
  cases frame.action with
  | inl settled =>
      rw [frame.born_rank]
      exact Or.inl (by omega)
  | inr paid =>
      rw [frame.math_rank]
      exact Or.inr ⟨rfl, Nat.lt_succ_self _⟩

end Frame

variable (initial : Frame (Value := Value) (Var := Var) (sort := sort))

private theorem sequence_forward {State : Type (u + 1)} (next : State → State)
    (rank : State → Nat × Nat) (states : Nat → State)
    (step : (count : Nat) → states (count + 1) = next (states count))
    (progress : (state : State) → Before (rank state) (rank (next state)))
    (first distance : Nat) : Before (rank (states first)) (rank (states (first + distance + 1))) := by
  induction distance with
  | zero => rw [step]; exact progress _
  | succ distance prior =>
      apply before_trans prior
      have index : first + (distance + 1) + 1 = (first + distance + 1) + 1 := by omega
      rw [index, step (first + distance + 1)]
      exact progress _

theorem frames_forward (first distance : Nat) :
    Before (frames initial first).rank (frames initial (first + distance + 1)).rank :=
  sequence_forward Frame.next Frame.rank (frames initial) (fun _ => rfl) Frame.next_progress first distance

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

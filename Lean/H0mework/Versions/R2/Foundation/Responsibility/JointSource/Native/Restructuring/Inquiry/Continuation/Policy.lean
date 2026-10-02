import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Occurrence

/-! Actual source syntax grows at residual birth. Within one root, only its
canonical causal depth grows. Old split/merge inventory sizes are irrelevant. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

def Before (first second : Nat × Nat) : Prop :=
  first.1 < second.1 ∨ first.1 = second.1 ∧ first.2 < second.2

theorem before_trans {first middle last : Nat × Nat}
    (prior : Before first middle) (later : Before middle last) : Before first last := by
  unfold Before at *
  rcases prior with prior | ⟨same, prior⟩ <;> rcases later with later | ⟨sameNext, later⟩ <;> omega

theorem before_irrefl (current : Nat × Nat) : ¬ Before current current := by
  unfold Before
  omega

def erasedDepth (current : AnyAuthoritativeRootCurrent.{u}) : Nat :=
  match current.current.visit.history with
  | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
  | .postCofinal _ => 0

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def rank : Nat × Nat := (remaining frame.rawRead.expression, frame.depth + 1)

private theorem finiteDepth (depth : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
      (Inquiry.finiteVisit frame.old frame.program frame.registered depth).history = depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (Inquiry.finiteVisit frame.old frame.program frame.registered depth).history + 1 = depth + 1
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

theorem frames_forward (first distance : Nat) :
    Before (frames initial first).rank (frames initial (first + distance + 1)).rank := by
  induction distance with
  | zero => exact (frames initial first).next_progress
  | succ distance prior =>
      exact before_trans prior (frames initial (first + distance + 1)).next_progress

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

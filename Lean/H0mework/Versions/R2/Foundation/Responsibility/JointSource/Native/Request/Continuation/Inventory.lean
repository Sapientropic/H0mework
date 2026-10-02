import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Continuation.Frame

/-! Registration injectivity consumes actual Entry growth across a birth and
the canonical causal history within the same root. Neither budget nor a frame
label identifies an occurrence. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Continuation

open SourceOperationEffects RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

def measure (current : AnyAuthoritativeRootCurrent.{u}) : Nat × Nat :=
  (Inventory.erasedEntryCard current, match current.current.visit.history with
    | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
    | .postCofinal _ => 0)

def Before (first second : Nat × Nat) : Prop :=
  first.1 < second.1 ∨ first.1 = second.1 ∧ first.2 < second.2

private theorem before_trans {first middle last : Nat × Nat}
    (prior : Before first middle) (later : Before middle last) : Before first last := by
  unfold Before at *
  rcases prior with prior | ⟨same, prior⟩ <;> rcases later with later | ⟨sameNext, later⟩ <;> omega

private theorem before_irrefl (current : Nat × Nat) : ¬ Before current current := by
  unfold Before
  omega

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def rank := measure frame.presentation.erase

private theorem finiteDepth (count : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
      (finiteVisit frame.old frame.program frame.registered frame.scope count).history = count := by
  induction count with
  | zero => rfl
  | succ count prior =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit frame.old frame.program frame.registered frame.scope count).history + 1 = count + 1
      rw [prior]

theorem rank_actual : frame.rank =
    (Inventory.entryCard frame.old.root.toAuthoritativeRoot.toLedgerRoot frame.old.visit.current + 1,
      frame.depth + 1) := by
  rw [rank, frame.presentation_erase]
  apply Prod.ext
  · exact Inventory.newfinite_card frame.old frame.program frame.registered frame.scope (frame.depth + 1)
  · exact finiteDepth frame (frame.depth + 1)

theorem born_rank : frame.born.rank = (frame.rank.1 + 1, 1) := by
  rw [rank_actual]
  have oldCard : Inventory.entryCard frame.currentState.root.toAuthoritativeRoot.toLedgerRoot
      frame.currentState.visit.current = frame.rank.1 := by
    rw [rank, frame.presentation_erase]
    rfl
  exact Prod.ext (congrArg (fun size => size + 1) oldCard) rfl

private theorem math_rank : frame.mathNext.rank = (frame.rank.1, frame.rank.2 + 1) := by
  rw [rank_actual, rank_actual]
  rfl

theorem next_progress : Before frame.rank frame.next.rank := by
  unfold next nextFrom
  cases frame.action with
  | inl settled =>
      rw [born_rank]
      exact Or.inl (Nat.lt_succ_self _)
  | inr paid =>
      rw [math_rank]
      exact Or.inr ⟨rfl, Nat.lt_succ_self _⟩

end Frame

variable (initial : Frame (Value := Value) (Var := Var) (sort := sort))

private theorem frames_forward (first distance : Nat) :
    Before (frames initial first).rank (frames initial (first + distance + 1)).rank := by
  induction distance with
  | zero => exact (frames initial first).next_progress
  | succ distance prior =>
      exact before_trans prior (frames initial (first + distance + 1)).next_progress

theorem frames_erase_injective : Function.Injective (fun count => (frames initial count).presentation.erase) := by
  intro first second same
  have ranks := congrArg measure same
  change (frames initial first).rank = (frames initial second).rank at ranks
  rcases lt_trichotomy first second with less | same | greater
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt less
    have progresses := frames_forward initial first distance
    rw [← next, ranks] at progresses
    exact False.elim (before_irrefl _ progresses)
  · exact same
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt greater
    have progresses := frames_forward initial second distance
    rw [← next, ranks] at progresses
    exact False.elim (before_irrefl _ progresses)

end
end RootGeneratedDebtActivationJointSource.Native.Request.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

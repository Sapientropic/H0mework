import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def measure (source : AnyAuthoritativeRootCurrent) : Nat × Nat :=
  (erasedEntryCard source, match source.current.visit.history with
    | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
    | .postCofinal _ => 0)

def Before (left right : Nat × Nat) : Prop :=
  left.1 < right.1 ∨ left.1 = right.1 ∧ left.2 < right.2

theorem before_trans {left middle right : Nat × Nat}
    (earlier : Before left middle) (later : Before middle right) : Before left right := by
  unfold Before at *
  rcases earlier with earlier | ⟨same, earlier⟩ <;>
    rcases later with later | ⟨sameNext, later⟩ <;> omega

theorem before_irrefl (point : Nat × Nat) : ¬ Before point point := by unfold Before; omega

namespace Frame
variable (frame : Frame input)

def rank := measure (frame.presentation input).erase

theorem rank_exact : frame.rank input =
    (entryCard frame.native.root.toAuthoritativeRoot.toLedgerRoot frame.visit.current,
      ProductiveFiniteRootHistoryAt.causalDepth frame.visit.history) := rfl

theorem ordinary_rank : (frame.ordinary input).rank input =
    ((frame.rank input).1, (frame.rank input).2 + 1) := by
  rw [rank_exact, rank_exact]
  apply Prod.ext
  · exact (native_entry_card input frame.native frame.visit.current).symm
  · rfl

theorem born_rank (registered : Registration input frame.native frame.visit.current) :
    (frame.born input registered).rank input = ((frame.rank input).1 + 1, 1) := by
  rw [rank_exact, rank_exact]
  apply Prod.ext
  · change entryCard (Admission.livingRoot input frame.native registered).toAuthoritativeRoot.toLedgerRoot
      (Admission.next input frame.native registered (Admission.initial input frame.native registered)) = _
    rw [admitted_entry_card]
    exact congrArg (fun size => size + 1) (native_entry_card input frame.native frame.visit.current).symm
  · rfl

theorem next_progress : Before (frame.rank input) ((frame.next input).rank input) := by
  unfold Frame.next
  split
  · rw [born_rank]
    exact Or.inl (Nat.lt_succ_self _)
  · rw [ordinary_rank]
    exact Or.inr ⟨rfl, Nat.lt_succ_self _⟩

end Frame

theorem frames_forward (depth first distance : Nat) :
    Before ((frames input depth first).rank input) ((frames input depth (first + distance + 1)).rank input) := by
  induction distance with
  | zero => exact (frames input depth first).next_progress input
  | succ distance prior =>
      exact before_trans prior (frames input depth (first + distance + 1)).next_progress

theorem initial_entry_lower (depth : Nat) : 2 ≤ ((initialFrame input depth).rank input).1 := by
  change 2 ≤ entryCard (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toLedgerRoot
    (Cursor.physicalVisit input (Cursor.next input (Ingress.start input depth))).current
  exact programme_entry_lower input _

theorem frames_entry_lower (depth count : Nat) : 2 ≤ ((frames input depth count).rank input).1 := by
  induction count with
  | zero => exact initial_entry_lower input depth
  | succ count prior =>
      have step := (frames input depth count).next_progress input
      change 2 ≤ (((frames input depth count).next input).rank input).1
      unfold Before at step
      rcases step with greater | ⟨same, _⟩ <;> omega

theorem frames_erase_injective (depth : Nat) :
    Function.Injective (fun count => (frames input depth count).presentation input |>.erase) := by
  intro left right same
  have ranks := congrArg measure same
  change (frames input depth left).rank input = (frames input depth right).rank input at ranks
  rcases lt_trichotomy left right with earlier | same | later
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt earlier
    have strict := frames_forward input depth left distance
    rw [← next, ranks] at strict
    exact False.elim (before_irrefl _ strict)
  · exact same
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt later
    have strict := frames_forward input depth right distance
    rw [← next, ranks] at strict
    exact False.elim (before_irrefl _ strict)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

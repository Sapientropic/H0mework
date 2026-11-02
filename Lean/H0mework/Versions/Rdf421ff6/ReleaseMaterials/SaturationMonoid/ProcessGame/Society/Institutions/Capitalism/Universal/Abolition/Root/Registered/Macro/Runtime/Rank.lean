import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.SnapshotRecognition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Rank

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

abbrev measure := Financial.Installation.Runtime.measure

def Before (first second : Nat × (Nat × Nat)) : Prop :=
  first.1 < second.1 ∨ first.1 = second.1 ∧ Financial.Installation.Runtime.Before first.2 second.2

private theorem before_trans {first middle last : Nat × (Nat × Nat)}
    (earlier : Before first middle) (later : Before middle last) : Before first last := by
  rcases earlier with more | ⟨same, more⟩
  · rcases later with later | ⟨equal, _⟩ <;> exact .inl (by omega)
  · rcases later with later | ⟨equal, later⟩
    · exact .inl (by omega)
    · exact .inr ⟨same.trans equal, Financial.Installation.Runtime.before_trans more later⟩

private theorem before_irrefl (value : Nat × (Nat × Nat)) : ¬ Before value value := by
  rintro (more | ⟨_, more⟩)
  · exact Nat.lt_irrefl _ more
  · exact Financial.Installation.Runtime.before_irrefl _ more

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace Frame
variable (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def rank := (frame.snapshot.past.length, measure frame.presentation.erase)

theorem rank_exact : frame.rank =
    (frame.snapshot.past.length,
      entryCard frame.package.frame.root.toAuthoritativeRoot.toLedgerRoot frame.visit.current,
      ProductiveFiniteRootHistoryAt.causalDepth frame.visit.history) := rfl

theorem ordinary_rank : frame.ordinary.rank = (frame.rank.1, frame.rank.2.1, frame.rank.2.2 + 1) := by
  rw [rank_exact, rank_exact]
  exact Prod.ext rfl (Prod.ext (native_entry_card frame.package.frame frame.visit.current).symm rfl)

theorem born_rank
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    (frame.born registered).rank = (frame.rank.1, frame.rank.2.1 + 1, 1) := by
  rw [rank_exact, rank_exact]
  refine Prod.ext (congrArg (fun snapshot => snapshot.past.length) (frame.born_snapshot registered)) ?_
  apply Prod.ext
  · let child := (frame.package.born registered).frame
    exact (native_entry_card child child.root.toAuthoritativeRoot.toRoot.source.initial).symm.trans
      (admitted_entry_card frame.package.frame registered (Admission.initial frame.package.frame registered))
  · rfl

theorem next_progress : Before frame.rank frame.next.rank := by
  unfold Frame.next Frame.nextAt
  split
  · unfold Frame.internalNext
    split
    · rw [born_rank]
      exact .inr ⟨rfl, .inl (Nat.lt_succ_self _)⟩
    · rw [ordinary_rank]
      exact .inr ⟨rfl, .inr ⟨rfl, Nat.lt_succ_self _⟩⟩
  · left
    exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self frame.rank.1)
      (frame.reentry_adds_one_actual_input_to_the_original_past _).symm

end Frame

variable (input depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (reader : Raw.Reader input depth count)
  (nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none)

theorem frames_forward (first distance : Nat) :
    Before (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader first).rank
      (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader (first + distance + 1)).rank := by
  induction distance with
  | zero => exact (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader first).next_progress
  | succ distance prior =>
      exact before_trans prior
        (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader (first + distance + 1)).next_progress

theorem frames_erase_injective : Function.Injective
    (fun tick => (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader tick).presentation.erase) := by
  intro left right same
  have snapshots := same_erased_frame_has_the_same_original_past (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader left right same
  have ranks : (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader left).rank =
      (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader right).rank :=
    Prod.ext (congrArg (fun snapshot => snapshot.past.length) snapshots) (congrArg measure same)
  change (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader left).rank =
    (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader right).rank at ranks
  rcases lt_trichotomy left right with earlier | equal | later
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt earlier
    have strict := frames_forward (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader left distance
    rw [← next, ranks] at strict
    exact False.elim (before_irrefl _ strict)
  · exact equal
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt later
    have strict := frames_forward (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader right distance
    rw [← next, ranks] at strict
    exact False.elim (before_irrefl _ strict)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.frames_erase_injective

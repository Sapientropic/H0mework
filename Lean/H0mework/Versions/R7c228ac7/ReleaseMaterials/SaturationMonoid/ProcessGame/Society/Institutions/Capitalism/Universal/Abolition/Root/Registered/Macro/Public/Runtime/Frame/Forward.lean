import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Inventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Snapshot
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Query
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Bound
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Rank

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}
  (frame : Frame origin admission)

def rank := (frame.snapshot.past.length, Financial.Installation.Runtime.measure frame.presentation.erase)

theorem rank_exact : frame.rank =
    (frame.snapshot.past.length, entryCard frame.full.root.toAuthoritativeRoot.toLedgerRoot frame.visit.current,
      ProductiveFiniteRootHistoryAt.causalDepth frame.visit.history) := rfl

theorem ordinary_rank (work : frame.HasWork)
    (noIssue : Accounting.registration? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual = none) :
    (frame.ordinary work noIssue).rank = (frame.rank.1, frame.rank.2.1, frame.rank.2.2 + 1) := by
  rw [rank_exact, rank_exact]
  exact Prod.ext (congrArg (fun snapshot => snapshot.past.length) (frame.ordinary_snapshot work noIssue))
    (Prod.ext (native_entry_card frame.full frame.visit.current).symm rfl)

theorem born_rank
    (registered : Accounting.Registration input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual) :
    (frame.born registered).rank = (frame.rank.1, frame.rank.2.1 + 1, 1) := by
  rw [rank_exact, rank_exact]
  refine Prod.ext (congrArg (fun snapshot => snapshot.past.length) (frame.born_snapshot registered)) ?_
  apply Prod.ext
  · let child := frame.born registered
    exact (native_entry_card child.full child.full.root.toAuthoritativeRoot.toRoot.source.initial).symm.trans
      (born_initial_entry_card frame.full (.finite frame.visit) frame.actual.actual frame.actual.aligned registered frame.reader)
  · rfl

theorem next_progress : Macro.Runtime.Before frame.rank frame.next.rank := by
  unfold next
  split
  · unfold internalNext
    split
    · rw [born_rank]
      exact .inr ⟨rfl, .inl (Nat.lt_succ_self _)⟩
    · rw [ordinary_rank]
      exact .inr ⟨rfl, .inr ⟨rfl, Nat.lt_succ_self _⟩⟩
  · rename_i complete
    left
    exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self frame.rank.1)
      (frame.reentry_adds_one_actual_input complete).symm

private theorem before_trans {first middle last : Nat × (Nat × Nat)}
    (earlier : Macro.Runtime.Before first middle) (later : Macro.Runtime.Before middle last) :
    Macro.Runtime.Before first last := by
  unfold Macro.Runtime.Before Financial.Installation.Runtime.Before at *
  omega

theorem visits_forward (first distance : Nat) :
    Macro.Runtime.Before (frame.visits first).rank (frame.visits (first + distance + 1)).rank := by
  induction distance with
  | zero => simpa only [visits, Function.iterate_succ_apply'] using (frame.visits first).next_progress
  | succ distance prior =>
    have step := (frame.visits (first + distance + 1)).next_progress
    apply before_trans prior
    simpa only [visits, Function.iterate_succ_apply', Nat.add_succ] using step

#print axioms rank_exact
#print axioms born_rank
#print axioms next_progress
#print axioms visits_forward

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Progress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- Completion of this finite review reports either its original typed
residual or the actually paid material tail. Neither constructor supplies
native service discharge or a completed-world authority. -/
inductive BoundaryAt : Type
  | unavailable (located : Located input depth count prefixLimit renewalLimit)
      (original : recovered input depth count prefixLimit renewalLimit current = some located)
      (issue : PreparationIssue input depth count prefixLimit renewalLimit located)
      (generated : prepare input depth count prefixLimit renewalLimit located = .stopped issue)
  | stopped (located : Located input depth count prefixLimit renewalLimit)
      (original : recovered input depth count prefixLimit renewalLimit current = some located)
      (prepared : Prepared input depth count prefixLimit renewalLimit located)
      (generated : prepare input depth count prefixLimit renewalLimit located = .ready prepared)
      (reason : Stop input depth count prefixLimit renewalLimit located prepared)
      (actual : (atCursor input depth count prefixLimit renewalLimit located prepared current).2 = .stopped reason)
  | materialPaid (located : Located input depth count prefixLimit renewalLimit)
      (original : recovered input depth count prefixLimit renewalLimit current = some located)
      (prepared : Prepared input depth count prefixLimit renewalLimit located)
      (generated : prepare input depth count prefixLimit renewalLimit located = .ready prepared)
      {start before : Physical.Cursor Party Good Port Technology Instrument}
      (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start before)
      (occurred : candidate.tailTarget.past <+: current.past)
      (source : ∃ sourcePast, (atCursor input depth count prefixLimit renewalLimit located prepared current).2 =
        .materialPaid candidate sourcePast)

def boundary? : Option (BoundaryAt input depth count prefixLimit renewalLimit current) :=
  match original : recovered input depth count prefixLimit renewalLimit current with
  | none => none
  | some located =>
      match generated : prepare input depth count prefixLimit renewalLimit located with
      | .stopped issue => some (.unavailable located original issue generated)
      | .ready prepared =>
          match actual : (atCursor input depth count prefixLimit renewalLimit located prepared current).2 with
          | .stopped reason => some (.stopped located original prepared generated reason actual)
          | .materialPaid candidate occurred =>
              some (.materialPaid located original prepared generated candidate (by
                rw [← recovered_phase_reads_the_same_actual_past input depth count prefixLimit renewalLimit
                  located prepared current original]
                exact occurred) ⟨occurred, actual⟩)
          | _ => none

theorem zero_registered_rank_has_an_original_boundary
    (located : Located input depth count prefixLimit renewalLimit)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (zero : reviewRank input depth count prefixLimit renewalLimit current = 0) :
    (boundary? input depth count prefixLimit renewalLimit current).isSome = true := by
  unfold boundary?
  split
  next absent => cases absent.symm.trans original
  next originalLocated source =>
    have same := Option.some.inj (source.symm.trans original)
    subst originalLocated
    split
    next issue generated => rfl
    next prepared generated =>
      have rankEq := source_phase_rank_is_the_actual_registered_rank input depth count prefixLimit renewalLimit
        located prepared current original generated
      rw [rankEq] at zero
      split
      next reason actual => rfl
      next start before candidate occurred actual => rfl
      next absentStop absentPaid =>
        cases actual : (atCursor input depth count prefixLimit renewalLimit located prepared current).2 with
        | priming due atRegistration => simp only [economicRank, actual] at zero; omega
        | pending pending => simp only [economicRank, actual, PendingAt.economicRank] at zero; omega
        | materialCandidate candidate => simp only [economicRank, actual] at zero; omega
        | frontExecuted candidate actualFront => simp only [economicRank, actual, Nat.one_ne_zero] at zero
        | materialPaid candidate occurred => exact (absentPaid _ _ candidate occurred actual).elim
        | stopped reason => exact (absentStop reason actual).elim

#print axioms boundary?
#print axioms zero_registered_rank_has_an_original_boundary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

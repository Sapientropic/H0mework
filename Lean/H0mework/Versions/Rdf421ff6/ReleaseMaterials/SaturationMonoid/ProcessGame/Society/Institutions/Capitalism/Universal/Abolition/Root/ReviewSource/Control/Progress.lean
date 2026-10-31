import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  {located : Located input depth count prefixLimit renewalLimit}
  (prepared : Prepared input depth count prefixLimit renewalLimit located)

def Prepared.budget (start : Physical.Cursor Party Good Port Technology Instrument) : Nat :=
  min (Review.physicalBudget prepared.fee.request prepared.fee.scope
    (Material.rawAt input depth count prefixLimit renewalLimit start)) prepared.candidates.length

namespace PendingAt
variable {input depth count prefixLimit renewalLimit prepared}
  {start current : Physical.Cursor Party Good Port Technology Instrument}
  (pending : PendingAt input depth count prefixLimit renewalLimit located prepared start current)

def economicRank : Nat := prepared.budget input depth count prefixLimit renewalLimit start - pending.paidCount + 3

theorem actual_paid_count_is_bounded : pending.paidCount ≤
    prepared.budget input depth count prefixLimit renewalLimit start := pending.rejected.actual_payment_bound

end PendingAt

variable (located)

/-- This major counts remaining genuinely payable reviews plus the
material front/tail phases. The actual financial-item minor is separate. -/
def economicRank (view : View input depth count prefixLimit renewalLimit located prepared) : Nat :=
  match view.2 with
  | .priming _ _ => prepared.budget input depth count prefixLimit renewalLimit
      (Physical.next (Physical.receive view.1 .advance)) + 4
  | .pending pending => pending.economicRank
  | .materialCandidate _ => 2
  | .frontExecuted .. => 1
  | .materialPaid .. | .stopped _ => 0

theorem every_generated_review_advance_decreases_its_economic_rank
    (view : View input depth count prefixLimit renewalLimit located prepared)
    (positive : 0 < economicRank input depth count prefixLimit renewalLimit located prepared view) :
    economicRank input depth count prefixLimit renewalLimit located prepared
        (advance input depth count prefixLimit renewalLimit located prepared view) <
      economicRank input depth count prefixLimit renewalLimit located prepared view := by
  rcases view with ⟨current, phase⟩
  cases phase with
  | priming due atRegistration =>
      simp only [advance, economicRank, initialPending, PendingAt.economicRank, Nat.sub_zero]
      omega
  | pending pending =>
      dsimp only [advance]
      split
      next empty =>
        change 0 < pending.economicRank
        unfold PendingAt.economicRank
        omega
      next pair remaining head =>
        split
        next candidate produced =>
          change 2 < pending.economicRank
          unfold PendingAt.economicRank
          omega
        next payment issue observed after exactAfter produced =>
          have paid := after.actual_paid_count_is_bounded
          change after.economicRank < pending.economicRank
          rw [exactAfter] at paid ⊢
          dsimp only [PendingAt.afterRejected, PendingAt.economicRank] at paid ⊢
          omega
        next obstruction attempted produced =>
          change 0 < pending.economicRank
          unfold PendingAt.economicRank
          omega
  | materialCandidate candidate => exact Nat.lt_succ_self 1
  | frontExecuted candidate actual => exact Nat.zero_lt_one
  | materialPaid candidate occurred => cases positive
  | stopped reason => cases positive

def reviewRank (current : Physical.Cursor Party Good Port Technology Instrument) : Nat :=
  match recovered input depth count prefixLimit renewalLimit current with
  | none => 0
  | some located =>
      match prepare input depth count prefixLimit renewalLimit located with
      | .stopped _ => 0
      | .ready prepared => economicRank input depth count prefixLimit renewalLimit located prepared
          (atCursor input depth count prefixLimit renewalLimit located prepared current)

theorem source_phase_rank_is_the_actual_registered_rank
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (generated : prepare input depth count prefixLimit renewalLimit located = .ready prepared) :
    reviewRank input depth count prefixLimit renewalLimit current =
      economicRank input depth count prefixLimit renewalLimit located prepared
        (atCursor input depth count prefixLimit renewalLimit located prepared current) := by
  simp only [reviewRank, original, generated]

theorem every_actual_pending_opcode_decreases_the_same_source_economic_rank
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument)
    (positive : 0 < reviewRank input depth count prefixLimit renewalLimit current) :
    reviewRank input depth count prefixLimit renewalLimit
        (Physical.next (Mandatory.executionCursor input depth count prefixLimit renewalLimit current proposal)) <
      reviewRank input depth count prefixLimit renewalLimit current := by
  cases original : recovered input depth count prefixLimit renewalLimit current with
  | none => simp only [reviewRank, original, Nat.lt_irrefl] at positive
  | some located =>
      cases generated : prepare input depth count prefixLimit renewalLimit located with
      | stopped issue => simp only [reviewRank, original, generated, Nat.lt_irrefl] at positive
      | ready prepared =>
          let phase := atCursor input depth count prefixLimit renewalLimit located prepared current
          have beforeRank := source_phase_rank_is_the_actual_registered_rank input depth count prefixLimit renewalLimit
            located prepared current original generated
          rw [beforeRank] at positive ⊢
          have forced : Mandatory.executionRaw input depth count prefixLimit renewalLimit current proposal =
              expectedRaw input depth count prefixLimit renewalLimit located prepared phase := by
            apply (Mandatory.every_proposal_consumes_the_same_registered_opcode
              input depth count prefixLimit renewalLimit current proposal _ ?_).1
            dsimp only [action]
            simp only [original, generated]
            change phaseAction input depth count prefixLimit renewalLimit located prepared phase = _
            have positivePhase : 0 < economicRank input depth count prefixLimit renewalLimit located prepared phase := positive
            rcases phase with ⟨sourceCurrent, mode⟩
            cases mode <;> first | rfl | simp only [economicRank, Nat.lt_irrefl] at positivePhase
          have nextPhase := every_generated_pending_step_eliminates_the_code_comparison
            input depth count prefixLimit renewalLimit located prepared current original
          dsimp only at nextPhase
          have afterRank : reviewRank input depth count prefixLimit renewalLimit
              (Physical.next (Mandatory.executionCursor input depth count prefixLimit renewalLimit current proposal)) =
              economicRank input depth count prefixLimit renewalLimit located prepared
                (advance input depth count prefixLimit renewalLimit located prepared phase) := by
            simp only [Mandatory.executionCursor, forced, phase, reviewRank, nextPhase.1, generated, nextPhase.2]
          rw [afterRank]
          exact every_generated_review_advance_decreases_its_economic_rank input depth count prefixLimit renewalLimit
            located prepared phase positive

#print axioms every_generated_review_advance_decreases_its_economic_rank
#print axioms every_actual_pending_opcode_decreases_the_same_source_economic_rank

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

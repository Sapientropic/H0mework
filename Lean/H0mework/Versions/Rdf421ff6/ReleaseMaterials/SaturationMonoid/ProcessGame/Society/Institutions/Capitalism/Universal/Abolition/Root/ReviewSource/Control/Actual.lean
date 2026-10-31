import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Inheritance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.Source

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
  (proposal : Compile.RawInput Party Good Port Technology Instrument)

/-- Source-only: the branch and all its witnesses are read from this
registered past. Every active compulsory step is the generated advance,
so the arbitrary-history equality recognizer contributes no choice. -/
theorem every_actual_pending_review_is_the_original_generated_step :
    match report input depth count prefixLimit renewalLimit current with
    | .inspected located _ prepared _ phase _ =>
        match phase.2 with
        | .stopped _ | .materialPaid .. => True
        | _ =>
            let after := Physical.next (Mandatory.executionCursor input depth count prefixLimit renewalLimit current proposal)
            recovered input depth count prefixLimit renewalLimit after = some located ∧
              atCursor input depth count prefixLimit renewalLimit located prepared after =
                advance input depth count prefixLimit renewalLimit located prepared phase
    | _ => True := by
  cases generatedReport : report input depth count prefixLimit renewalLimit current with
  | unregistered missing => trivial
  | unavailable located original issue generated => trivial
  | inspected located original prepared generated phase exactPhase =>
      have normalized (selected : ReportAt.action input depth count prefixLimit renewalLimit current
          (.inspected located original prepared generated phase exactPhase) =
            .execute (expectedRaw input depth count prefixLimit renewalLimit located prepared phase)) :
          let after := Physical.next (Mandatory.executionCursor input depth count prefixLimit renewalLimit current proposal)
          recovered input depth count prefixLimit renewalLimit after = some located ∧
            atCursor input depth count prefixLimit renewalLimit located prepared after =
              advance input depth count prefixLimit renewalLimit located prepared phase := by
        have actionEq := (report_and_opcode_are_one_source_computation input depth count prefixLimit renewalLimit current).symm
        rw [generatedReport, selected] at actionEq
        have forced := (Mandatory.every_proposal_consumes_the_same_registered_opcode
          input depth count prefixLimit renewalLimit current proposal _ actionEq).1
        have source := every_generated_pending_step_eliminates_the_code_comparison
          input depth count prefixLimit renewalLimit located prepared current original
        dsimp only at source
        rw [← exactPhase] at source
        simpa only [Mandatory.executionCursor, forced] using source
      rcases phase with ⟨sourceCurrent, actualPhase⟩
      cases actualPhase <;> first | trivial | exact normalized rfl

theorem actual_readout_preserves_the_registered_proposal_and_whole_past :
    (Mandatory.executionCursor input depth count prefixLimit renewalLimit current proposal).past = current.past ∧
      (Mandatory.produce input depth count prefixLimit renewalLimit current proposal).originalProposal = proposal ∧
      (Mandatory.produce input depth count prefixLimit renewalLimit current proposal).implicitReport =
        report input depth count prefixLimit renewalLimit current :=
  ⟨rfl, rfl, rfl⟩

theorem original_unavailable_task_is_a_true_no_write_answer
    (located : Located input depth count prefixLimit renewalLimit)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (issue : PreparationIssue input depth count prefixLimit renewalLimit located)
    (unavailable : prepare input depth count prefixLimit renewalLimit located = .stopped issue) :
    Mandatory.executionRaw input depth count prefixLimit renewalLimit current .advance = .stopReview ∧
      Physical.stateAt input depth count prefixLimit renewalLimit
        (Physical.next (Mandatory.executionCursor input depth count prefixLimit renewalLimit current .advance)).past =
          Physical.stateAt input depth count prefixLimit renewalLimit current.past := by
  have stopped : action input depth count prefixLimit renewalLimit current = .obstructed := by
    simp only [action, original, unavailable]
  have forced := Mandatory.the_original_stop_cannot_fall_back_to_automatic_power
    input depth count prefixLimit renewalLimit current stopped
  refine ⟨forced, ?_⟩
  rw [Physical.consumed_input_generates_its_own_after]
  simpa only [Mandatory.executionCursor, Physical.receive, forced] using
    (Compile.stopped_review_is_a_typed_no_write_answer input depth count prefixLimit renewalLimit
      (Physical.stateAt input depth count prefixLimit renewalLimit current.past)).1

#print axioms every_actual_pending_review_is_the_original_generated_step
#print axioms original_unavailable_task_is_a_true_no_write_answer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

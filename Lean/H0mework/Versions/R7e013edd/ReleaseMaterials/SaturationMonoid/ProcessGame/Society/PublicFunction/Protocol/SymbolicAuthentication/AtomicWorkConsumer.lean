import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
section WholeWord
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (batch : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (saved : Cursor old) (submit : Bool) (rival : Opponent (AtomicWorkSource.code old batch))

-- All instructions of a source batch occupy its one actual financial visit,
-- even after arbitrary subsequent callbacks.
theorem the_final_ledger_consumes_the_original_batch
    (future : List (EventHistory.Stage (code := AtomicWorkSource.code old batch))) :
    let start := AtomicWorkSource.cursor old batch saved
    let stages := (AtomicWorkSource.protocol old batch submit,rival) :: future
    let row := AtomicWorkSource.row old batch saved submit rival
    (Financial.inventoryAt (EventHistory.execute start stages).source.input
      (ProgrammeHistory.visitAt (EventHistory.execute start stages).source.input
        (EventStep.boundary row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (EventHistory.execute start stages).source.input) =
        StageTrace.items row :=
  StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ (List.mem_cons_self)

-- A native consumer checks the actual interpreter result, rather than accepting
-- a caller-supplied post-state or treating the material readout as a decision.
theorem executed_batch_has_one_raw_occurrence
    (success : AtomicWorkSource.assess old batch saved submit rival = .executed) :
    ProgrammeSource.rawEvent (AtomicWorkSource.next old batch saved submit rival).source.input
      (ProgrammeHistory.visitAt (AtomicWorkSource.next old batch saved submit rival).source.input
        (EventStep.boundary (AtomicWorkSource.cursor old batch saved))).current = batch := by
  rw [EventStep.actual_next_word]
  rw [← (StageTrace.material_is_the_actual_step (AtomicWorkSource.cursor old batch saved)
    (AtomicWorkSource.protocol old batch submit) rival).2]
  exact (AtomicWorkSource.executed_uses_the_original_whole_word old batch saved submit rival success).2.1

end WholeWord

section Reproduction
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
variable (old : Code Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
  (Mandate.State Delegation.Funded.Party Bool) Unit)
  (saved : Cursor old)
abbrev batch := DonorRegenerationLaw.word
abbrev code := AtomicWorkSource.code old batch
abbrev current := (EventStep.seed (AtomicWorkSource.cursor old batch saved)).current

def select (submit : Bool) : DonorRegenerationSource.Selection :=
  if WorkerInputSource.Needed (current old saved) then
    if submit then
      if DonorRegenerationLaw.Inputs (current old saved) then .produced else .unavailable
    else .withheld
  else .idle

abbrev offered (submit : Bool) := decide (select old saved submit = .produced)
abbrev production (submit : Bool) (rival : Opponent (code old)) :=
  AtomicWorkSource.row old batch saved (offered old saved submit) rival
abbrev next (submit : Bool) (rival : Opponent (code old)) :=
  AtomicWorkSource.next old batch saved (offered old saved submit) rival
abbrev assess (submit : Bool) (rival : Opponent (code old)) :=
  AtomicWorkSource.assess old batch saved (offered old saved submit) rival

theorem actual_reproduction_and_original_primitive_debits (submit : Bool)
    (rival : Opponent (code old)) (same : old.law = DonorRegenerationLaw.law)
    (success : assess old saved submit rival = .executed) :
    (production old saved submit rival).submitted = batch ∧
      (EventStep.seed (next old saved submit rival)).current = DonorRegenerationLaw.successor (current old saved) ∧
      UpstreamFeedLaw.Resources (EventStep.seed (next old saved submit rival)).current ∧
      WorkerInputSource.Needed (EventStep.seed (next old saved submit rival)).current ∧
      ¬ WorkerInputLaw.Inputs (EventStep.seed (next old saved submit rival)).current := by
  have actual := AtomicWorkSource.executed_uses_the_original_whole_word old batch saved
    (offered old saved submit) rival success
  have selected : select old saved submit = .produced := of_decide_eq_true actual.1
  have needed : WorkerInputSource.Needed (current old saved) := by
    by_contra absent
    simp only [select,if_neg absent] at selected
    contradiction
  have inputs : DonorRegenerationLaw.Inputs (current old saved) := by
    by_contra absent
    simp only [select,if_pos needed,if_neg absent] at selected
    split at selected <;> contradiction
  have endpoint := actual.2.2.1
  change (EventStep.seed (next old saved submit rival)).current = old.law.next (current old saved) batch at endpoint
  rw [same] at endpoint
  have regenerated := endpoint.trans (DonorRegenerationLaw.actual_next _ inputs).1
  refine ⟨actual.2.1,regenerated,?_,?_,?_⟩
  all_goals rw [regenerated]
  · exact DonorRegenerationLaw.new_fuel_has_original_paid_inputs _ inputs
  · exact (DonorRegenerationLaw.new_fuel_leaves_the_worker_deficit_visible _ inputs needed).1
  · exact (DonorRegenerationLaw.new_fuel_leaves_the_worker_deficit_visible _ inputs needed).2.1
end Reproduction
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkConsumer

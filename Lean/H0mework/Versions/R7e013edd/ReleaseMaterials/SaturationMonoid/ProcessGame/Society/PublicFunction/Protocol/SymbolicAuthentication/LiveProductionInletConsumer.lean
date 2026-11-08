import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletConsumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveProductionInletSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (saved : Cursor (code old instructions)) (protocol : Rule (code old instructions))
  (enabled : Bool) (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument)

theorem actual_external_word (chosen : Choice (code old instructions))
    (call : (row old instructions saved protocol enabled instruction).call = .external (some chosen))
    (found : request old instructions instruction = some chosen) :
    (row old instructions saved protocol enabled instruction).submitted = [instruction] := by
  have live := (StageTrace.external_callback_is_retained_before_admission saved protocol
    (rival old instructions enabled instruction) (some chosen) call).1
  have event := admitted_request_is_the_source_instruction old instructions instruction chosen found
  have admitted : ControlExecution.admitted (code old instructions)
      (row old instructions saved protocol enabled instruction).call = some chosen := by
    simp only [call,ControlExecution.admitted,Distributed.Recall.Information.Agency.externalChoice,event]
  change Feedback.word (code old instructions) (some protocol.work.val)
    ⟨fun _ _ _ => ControlExecution.admitted (code old instructions)
      (row old instructions saved protocol enabled instruction).call,saved.entry.budget⟩
    (EventStep.seed saved) = _
  simp only [Feedback.word,Feedback.decision,if_neg live,admitted,Feedback.stepLocal,event,Code.step,List.nil_append]

theorem executed_keeps_the_actual_input_and_next
    (success : assess old instructions saved protocol enabled instruction = .executed) :
    enabled = true ∧
      (row old instructions saved protocol enabled instruction).submitted = [instruction] ∧
      (EventStep.seed (next old instructions saved protocol enabled instruction)).current =
        old.law.next (EventStep.seed saved).current [instruction] ∧
      (∀ item ∈ StageTrace.items (row old instructions saved protocol enabled instruction),
        old.law.Valid item.before item.request) := by
  cases call : (row old instructions saved protocol enabled instruction).call with
  | external attempt =>
    cases attempt with
    | none =>
      simp only [assess,call] at success
      split at success <;> contradiction
    | some chosen =>
      have paid : ∀ item ∈ StageTrace.items (row old instructions saved protocol enabled instruction),
          old.law.Valid item.before item.request := by
        by_contra unpaid
        simp only [assess,call,if_neg unpaid] at success
        contradiction
      have callback := (StageTrace.external_callback_is_retained_before_admission saved protocol
        (rival old instructions enabled instruction) (some chosen) call).2.2
      change (if enabled then request old instructions instruction else none) = some chosen at callback
      have on : enabled = true := by cases enabled <;> simp_all
      rw [on] at callback
      change request old instructions instruction = some chosen at callback
      have word := actual_external_word old instructions saved protocol enabled instruction chosen call callback
      refine ⟨on,word,?_,paid⟩
      rw [← (StageTrace.material_is_the_actual_step saved protocol (rival old instructions enabled instruction)).1]
      change old.law.next (EventStep.seed saved).current
        (row old instructions saved protocol enabled instruction).submitted = _
      rw [word]
  | _ => simp only [assess,call] at success; contradiction

theorem the_run_is_its_source_generated_trace (initial : State old instructions)
    (controller : Controller old instructions) (count : Nat) :
    (LiveProductionInletSource.run old instructions initial controller count).cursor =
      EventHistory.execute initial.cursor (LiveProductionInletSource.trace old instructions initial controller count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (LiveProductionInletSource.step old instructions
      (LiveProductionInletSource.run old instructions initial controller count)
      (controller (LiveProductionInletSource.run old instructions initial controller count))).cursor =
        EventHistory.execute initial.cursor
          (LiveProductionInletSource.trace old instructions initial controller count ++
            [stage old instructions (LiveProductionInletSource.run old instructions initial controller count)
              (controller (LiveProductionInletSource.run old instructions initial controller count))])
    rw [OriginQueue.execute_append,← ih]
    rfl

theorem every_generated_record_is_in_the_final_native_financial_inventory
    (initial : State old instructions) (controller : Controller old instructions) (count : Nat)
    (record : StageTrace.Record (code := code old instructions))
    (inside : record ∈ StageTrace.records initial.cursor (LiveProductionInletSource.trace old instructions initial controller count)) :
    (Financial.inventoryAt (LiveProductionInletSource.run old instructions initial controller count).cursor.source.input
      (ProgrammeHistory.visitAt (LiveProductionInletSource.run old instructions initial controller count).cursor.source.input
        (EventStep.boundary record.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (LiveProductionInletSource.run old instructions initial controller count).cursor.source.input) =
        StageTrace.items record := by
  rw [the_run_is_its_source_generated_trace]
  exact StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ inside

abbrev financial (future : List (EventHistory.Stage (code := code old instructions))) :=
  StageTrace.final_financial_inventory_is_the_original_record_items saved
    ((protocol,rival old instructions enabled instruction)::future)
    (row old instructions saved protocol enabled instruction) (List.mem_cons_self)
abbrev occurrence (future : List (EventHistory.Stage (code := code old instructions))) :=
  StageTrace.every_record_is_a_completed_occurrence_of_the_final_source saved
    ((protocol,rival old instructions enabled instruction)::future)
    (row old instructions saved protocol enabled instruction) (List.mem_cons_self)

abbrev priorFinancial (origin : Cursor old) (original : origin.side = .original)
    (future : List (EventHistory.Stage (code := code old instructions))) :=
  CatalogueHandoffSource.completeFinancialPrefix old (catalogue old instructions) origin original future
abbrev native (future : List (EventHistory.Stage (code := code old instructions))) (ordinal : Nat) :=
  ProgrammeHistory.execution_face_shares_whole_ledger_and_next
    (EventHistory.execute saved ((protocol,rival old instructions enabled instruction)::future)).source.input ordinal
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletConsumer

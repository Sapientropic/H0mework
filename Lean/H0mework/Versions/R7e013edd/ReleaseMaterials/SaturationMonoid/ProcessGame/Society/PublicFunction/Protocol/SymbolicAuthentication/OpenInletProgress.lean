import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenInletSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenInletProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active State)
open InletOmissionSource (Controller Command Attempt after observe attempt)
open OpenInletSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "Cmd" => Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

private theorem block_queue (state : State old instructions) (command : Cmd) :
    retired old instructions state command ++ (after old instructions state command).pending =
      state.pending ++ command.incoming := by
  cases queue : state.pending ++ command.incoming with
  | nil =>
    simp [retired,observe,InletOmissionSource.after,LiveProductionInletSource.step,
      InletClockedSource.queued,InletOmissionSource.localCommand,queue]
  | cons head tail =>
    by_cases paid : LiveProductionInletSource.assess old instructions (InletClockedSource.prepared old instructions state)
      SilentWindow.quiet command.enabled head = .executed
    · simp [retired,observe,InletOmissionSource.after,LiveProductionInletSource.step,
        InletClockedSource.queued,InletOmissionSource.localCommand,queue,paid]
    · simp [retired,observe,InletOmissionSource.after,LiveProductionInletSource.step,
        InletClockedSource.queued,InletOmissionSource.localCommand,queue,paid]

private theorem block_budget (state : State old instructions) (command : Cmd) :
    (retired old instructions state command).length +
      isWithheld old instructions (attempt old instructions state command) +
      isGap old instructions (attempt old instructions state command) +
      isObstructed old instructions (attempt old instructions state command) = 1 := by
  unfold retired isWithheld isGap isObstructed attempt observe
  cases queue : state.pending ++ command.incoming with
  | nil => simp only [List.take_nil,reduceCtorEq,ite_false,ite_true,or_true,List.length_nil]
  | cons head tail =>
    cases actual : LiveProductionInletSource.assess old instructions (InletClockedSource.prepared old instructions state)
      SilentWindow.quiet command.enabled head <;> simp [actual]

theorem the_open_run_is_its_whole_original_execution (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) :
    (OpenInletSource.run old instructions initial control count).state.cursor =
      EventHistory.execute initial.cursor (OpenInletSource.run old instructions initial control count).stages := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (after old instructions _ _).cursor = EventHistory.execute initial.cursor
      ((OpenInletSource.run old instructions initial control count).stages ++ _)
    rw [OriginQueue.execute_append,← ih,InletOmissionSource.one_block_is_the_original_execution]
    rfl

theorem all_initial_and_new_input_is_retired_in_fifo_order_or_retained (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) :
    initial.pending ++ (OpenInletSource.run old instructions initial control count).arrivals =
      (OpenInletSource.run old instructions initial control count).retired ++
        (OpenInletSource.run old instructions initial control count).state.pending := by
  induction count with
  | zero => change initial.pending ++ [] = [] ++ initial.pending;simp only [List.append_nil,List.nil_append]
  | succ count ih =>
    let previous := OpenInletSource.run old instructions initial control count
    let command := control previous.state
    change initial.pending ++ (previous.arrivals ++ command.incoming) =
      (previous.retired ++ retired old instructions previous.state command) ++
        (after old instructions previous.state command).pending
    rw [← List.append_assoc,ih,List.append_assoc,List.append_assoc,block_queue]

theorem every_actual_attempt_is_accounted_once (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) :
    let result := OpenInletSource.run old instructions initial control count
    result.retired.length + omissions old instructions result + gaps old instructions result +
      obstructions old instructions result = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    let previous := OpenInletSource.run old instructions initial control count
    let command := control previous.state
    have one := block_budget old instructions previous.state command
    change (previous.retired ++ retired old instructions previous.state command).length +
      ((previous.attempts ++ [attempt old instructions previous.state command]).map (isWithheld old instructions)).sum +
      ((previous.attempts ++ [attempt old instructions previous.state command]).map (isGap old instructions)).sum +
      ((previous.attempts ++ [attempt old instructions previous.state command]).map (isObstructed old instructions)).sum = count+1
    simp only [List.length_append,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Nat.add_zero]
    change previous.retired.length + omissions old instructions previous + gaps old instructions previous +
      obstructions old instructions previous = count at ih
    dsimp only [omissions,gaps,obstructions] at ih
    omega

-- All quantities are computed from this actual run, including arrivals, empty offers and refusals.
theorem finite_actual_input_drains_under_its_actual_communication_and_admission_budget
    (initial : State old instructions) (control : Controller old instructions) (count : Nat)
    (admission : obstructions old instructions (OpenInletSource.run old instructions initial control count) = 0)
    (budget : initial.pending.length + (OpenInletSource.run old instructions initial control count).arrivals.length +
      omissions old instructions (OpenInletSource.run old instructions initial control count) +
      gaps old instructions (OpenInletSource.run old instructions initial control count) ≤ count) :
    (OpenInletSource.run old instructions initial control count).state.pending = [] ∧
      (OpenInletSource.run old instructions initial control count).retired =
        initial.pending ++ (OpenInletSource.run old instructions initial control count).arrivals := by
  have words := all_initial_and_new_input_is_retired_in_fifo_order_or_retained old instructions initial control count
  have lengths := congrArg List.length words
  simp only [List.length_append] at lengths
  have paid := every_actual_attempt_is_accounted_once old instructions initial control count
  dsimp only at paid
  have empty : (OpenInletSource.run old instructions initial control count).state.pending = [] := by
    apply List.length_eq_zero_iff.mp
    omega
  exact ⟨empty,by simpa only [empty,List.append_nil] using words.symm⟩

inductive Verdict (initial : State old instructions) (control : Controller old instructions) (count : Nat) where
  | drained (pending : (OpenInletSource.run old instructions initial control count).state.pending = [])
  | obstructed (pending : (OpenInletSource.run old instructions initial control count).state.pending ≠ [])
      (actual : 0 < obstructions old instructions (OpenInletSource.run old instructions initial control count))
  | continuing (pending : (OpenInletSource.run old instructions initial control count).state.pending ≠ [])
      (admission : obstructions old instructions (OpenInletSource.run old instructions initial control count) = 0)
      (deficit : count < initial.pending.length + (OpenInletSource.run old instructions initial control count).arrivals.length +
        omissions old instructions (OpenInletSource.run old instructions initial control count) +
        gaps old instructions (OpenInletSource.run old instructions initial control count))

def inspect (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    Verdict old instructions initial control count :=
  if empty : (OpenInletSource.run old instructions initial control count).state.pending = [] then .drained empty
  else if admission : obstructions old instructions (OpenInletSource.run old instructions initial control count) = 0 then
    .continuing empty admission (by
      by_contra enough
      exact empty (finite_actual_input_drains_under_its_actual_communication_and_admission_budget old instructions
        initial control count admission (by omega)).1)
  else .obstructed empty (by omega)

private theorem block_row (state : State old instructions) (command : Cmd) :
    (attempt old instructions state command).row ∈ StageTrace.records state.cursor
      (InletOmissionSource.stages old instructions state command) := by
  rw [InletOmissionSource.stages,OriginQueue.records_append,SilentWindow.execution_is_the_actual_cursor]
  exact List.mem_append_right _ List.mem_cons_self

theorem every_attempt_retains_its_context_observation_and_original_row (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) (entry : Attempt old instructions)
    (inside : entry ∈ (OpenInletSource.run old instructions initial control count).attempts) :
    entry.row = InletOmissionSource.row old instructions entry.state entry.command ∧
      entry.observation = observe old instructions entry.state entry.command ∧
      entry.row ∈ StageTrace.records initial.cursor (OpenInletSource.run old instructions initial control count).stages := by
  induction count with
  | zero => change entry ∈ [] at inside;contradiction
  | succ count ih =>
    change entry ∈ (OpenInletSource.run old instructions initial control count).attempts ++ [_] at inside
    rw [List.mem_append,List.mem_singleton] at inside
    change _ ∧ _ ∧ entry.row ∈ StageTrace.records initial.cursor
      ((OpenInletSource.run old instructions initial control count).stages ++ _)
    rw [OriginQueue.records_append,← the_open_run_is_its_whole_original_execution]
    rcases inside with prior | rfl
    · have oldEntry := ih prior
      exact ⟨oldEntry.1,oldEntry.2.1,List.mem_append_left _ oldEntry.2.2⟩
    · exact ⟨rfl,rfl,List.mem_append_right _ (block_row old instructions _ _)⟩

theorem every_retirement_consumes_its_actual_paid_original_request (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) (entry : Attempt old instructions)
    (inside : entry ∈ (OpenInletSource.run old instructions initial control count).attempts)
    (executed : entry.observation = some .executed) :
    entry.row.submitted = retired old instructions entry.state entry.command ∧
      ∀ item ∈ StageTrace.items entry.row, old.law.Valid item.before item.request := by
  have original := every_attempt_retains_its_context_observation_and_original_row old instructions initial control count entry inside
  have observation := original.2.1.symm.trans executed
  unfold observe at observation
  cases queue : entry.state.pending ++ entry.command.incoming with
  | nil => simp only [queue] at observation;contradiction
  | cons head tail =>
    simp only [queue] at observation
    have paid := LiveProductionInletConsumer.executed_keeps_the_actual_input_and_next old instructions
      (InletClockedSource.prepared old instructions entry.state) SilentWindow.quiet entry.command.enabled head
      (Option.some.inj observation)
    have row : InletOmissionSource.row old instructions entry.state entry.command =
        LiveProductionInletSource.row old instructions (InletClockedSource.prepared old instructions entry.state)
          SilentWindow.quiet entry.command.enabled head := by
      simp only [InletOmissionSource.row,InletOmissionSource.stage,LiveProductionInletSource.stage,
        InletClockedSource.queued,List.append_nil,queue]
    rw [original.1,row]
    refine ⟨?_,paid.2.2.2⟩
    rw [paid.2.1]
    simp only [retired,observe,queue,observation,ite_true,List.take_succ_cons,List.take_zero]

theorem every_reoffer_is_an_actual_admitted_unpaid_packet (cursor : Cursor (Active old instructions))
    (chosen : Choice (Active old instructions)) (selected : offer old instructions cursor = some chosen) :
    ∃ serial, chosen.val = .deliver serial ∧ serial ∈ NativeDeliveryJournal.pending cursor ∧
      serial < (EventStep.seed cursor).frame.sent.length ∧ serial ∉ NativeDeliveryJournal.settled cursor := by
  unfold offer at selected
  split at selected <;> try contradiction
  rename_i serial found
  split at selected <;> try contradiction
  cases Option.some.inj selected
  have member : serial ∈ NativeDeliveryJournal.pending cursor := List.mem_of_mem_head? found
  have physical := List.mem_filter.mp member
  exact ⟨serial,rfl,member,List.mem_range.mp physical.1,(of_decide_eq_true physical.2).2⟩

theorem commands_alone_replay_the_full_actual_endpoint (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) :
    InletOmissionProgress.replay old instructions initial (OpenInletSource.run old instructions initial control count).attempts =
      (OpenInletSource.run old instructions initial control count).state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change InletOmissionProgress.replay old instructions initial
      ((OpenInletSource.run old instructions initial control count).attempts ++ [_]) = _
    simp only [InletOmissionProgress.replay,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change after old instructions
      (InletOmissionProgress.replay old instructions initial (OpenInletSource.run old instructions initial control count).attempts) _ = _
    rw [ih];rfl

theorem the_next_uses_the_complete_endpoint_and_retains_all_pending_input (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) :
    (next old instructions initial control count).cursor =
        EventHistory.execute initial.cursor (joinedStages old instructions initial control count) ∧
      (next old instructions initial control count).pending = (OpenInletSource.run old instructions initial control count).state.pending := by
  refine ⟨?_,rfl⟩
  change EventHistory.execute (OpenInletSource.run old instructions initial control count).state.cursor _ = _
  rw [joinedStages,OriginQueue.execute_append,← the_open_run_is_its_whole_original_execution]

theorem every_joined_record_is_consumed_by_the_next_native_financial_inventory (initial : State old instructions)
    (control : Controller old instructions) (count : Nat) (record : StageTrace.Record (code := Active old instructions))
    (inside : record ∈ StageTrace.records initial.cursor (joinedStages old instructions initial control count)) :
    (Financial.inventoryAt (next old instructions initial control count).cursor.source.input
      (ProgrammeHistory.visitAt (next old instructions initial control count).cursor.source.input
        (EventStep.boundary record.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (next old instructions initial control count).cursor.source.input) =
        StageTrace.items record := by
  rw [(the_next_uses_the_complete_endpoint_and_retains_all_pending_input old instructions initial control count).1]
  exact StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenInletProgress

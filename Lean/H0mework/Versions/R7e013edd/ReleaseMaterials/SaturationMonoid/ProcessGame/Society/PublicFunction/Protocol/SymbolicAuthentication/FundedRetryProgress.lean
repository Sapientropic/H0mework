import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedRetrySource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedRetryProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
open FundedRetrySource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))

private theorem retry_retains (past : List (EventHistory.Stage (code := Active old instructions))) :
    past <+: TimedRetry.stages start past vocabulary encoding law := by
  cases made : TimedRetry.produce start past vocabulary encoding law with
  | idle => simp only [TimedRetry.stages,made];exact List.prefix_refl _
  | blocked reason => simp only [TimedRetry.stages,made];exact List.prefix_refl _
  | ready answer =>
    rw [TimedRetry.ready_appends_the_generated_schedule start past vocabulary encoding law answer made]
    exact TimedRetry.the_original_history_is_preserved start past vocabulary encoding law answer

theorem preparation_is_the_complete_actual_inlet_endpoint (state : FundedRetrySource.State old instructions)
    (command : Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    EventHistory.execute start (prepared old instructions start state command) = (supplied old instructions start state command).cursor := by
  rw [prepared,OriginQueue.execute_append]
  exact (OpenInletProgress.the_next_uses_the_complete_endpoint_and_retains_all_pending_input old instructions
    (inlet old instructions start state) (fun _ => command) 1).1.symm

theorem every_step_keeps_the_whole_actual_history (state : FundedRetrySource.State old instructions)
    (command : Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    state.history <+: (after old instructions start vocabulary encoding law state command).history :=
  (List.prefix_append _ _).trans (retry_retains old instructions start vocabulary encoding law _)

private theorem step_fifo (state : FundedRetrySource.State old instructions)
    (command : Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    state.pending ++ (feed old instructions start state command).arrivals =
      (feed old instructions start state command).retired ++
        (after old instructions start vocabulary encoding law state command).pending :=
  OpenInletProgress.all_initial_and_new_input_is_retired_in_fifo_order_or_retained old instructions
    (inlet old instructions start state) (fun _ => command) 1

theorem every_step_pays_for_its_new_confirmed_content (entry : Attempt old instructions) :
    confirmations old instructions start vocabulary encoding law entry.state +
      (if kind old instructions start vocabulary encoding law entry = .ready then 1 else 0) ≤
      confirmations old instructions start vocabulary encoding law
        (after old instructions start vocabulary encoding law entry.state entry.command) := by
  have kept := Finset.card_le_card (DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law
    entry.state.history (prepared old instructions start entry.state entry.command) (List.prefix_append _ _))
  have allKept := Finset.card_le_card (DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law
    entry.state.history (after old instructions start vocabulary encoding law entry.state entry.command).history
    (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _))
  cases made : plan old instructions start vocabulary encoding law entry.state entry.command with
  | idle => simpa only [kind,made,reduceCtorEq,if_false,Nat.add_zero] using allKept
  | blocked reason => simpa only [kind,made,reduceCtorEq,if_false,Nat.add_zero] using allKept
  | ready answer =>
    have gained := RetryProgress.every_actual_ready_retry_generates_strict_confirmation_progress encoding start vocabulary law
      (prepared old instructions start entry.state entry.command) answer
    change _ ≤ (DutyConfirmation.contents start vocabulary encoding law
      (TimedRetry.stages start (prepared old instructions start entry.state entry.command) vocabulary encoding law)).card
    rw [TimedRetry.ready_appends_the_generated_schedule start _ vocabulary encoding law answer made]
    simp only [kind,made,if_true]
    exact Nat.le_trans (Nat.add_le_add_right kept 1) gained

theorem all_new_input_is_retired_in_fifo_order_or_remains_live (initial : FundedRetrySource.State old instructions)
    (control : Controller old instructions) (count : Nat) :
    initial.pending ++ (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).arrivals =
      (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).retired ++
        (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).state.pending := by
  induction count generalizing initial with
  | zero => simp only [FundedRetrySource.run_zero,List.append_nil,List.nil_append]
  | succ count ih =>
    simp only [FundedRetrySource.run_succ]
    split
    · exact step_fifo old instructions start vocabulary encoding law _ _
    · rw [← List.append_assoc,step_fifo old instructions start vocabulary encoding law,List.append_assoc,ih,List.append_assoc]

theorem every_observation_keeps_the_entire_actual_prefix (initial : FundedRetrySource.State old instructions)
    (control : Controller old instructions) (count : Nat) :
    initial.history <+: (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).state.history := by
  induction count generalizing initial with
  | zero => exact List.prefix_refl _
  | succ count ih =>
    simp only [FundedRetrySource.run_succ]
    split
    · exact every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _
    · exact (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _).trans (ih _)

theorem every_funded_observation_pays_for_all_actual_retries (initial : FundedRetrySource.State old instructions)
    (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial +
      tally old instructions start vocabulary encoding law .ready (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).attempts ≤
      confirmations old instructions start vocabulary encoding law (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).state := by
  induction count generalizing initial with
  | zero => simp only [FundedRetrySource.run_zero,tally,List.map_nil,List.sum_nil,Nat.add_zero,Nat.le_refl]
  | succ count ih =>
    have grew := every_step_pays_for_its_new_confirmed_content old instructions start vocabulary encoding law
      (⟨initial,control initial⟩ : Attempt old instructions)
    dsimp only at grew
    simp only [FundedRetrySource.run_succ]
    split
    · rename_i idle
      simpa only [tally,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using grew
    · have tail := ih (after old instructions start vocabulary encoding law initial (control initial))
      simp only [tally,List.map_cons,List.sum_cons]
      change _ + ((if _ then 1 else 0) + tally old instructions start vocabulary encoding law .ready
        (FundedRetrySource.run old instructions start vocabulary encoding law control count _).attempts) ≤ _
      omega

theorem actual_retries_have_the_original_source_interface_capacity (initial : FundedRetrySource.State old instructions)
    (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial +
      tally old instructions start vocabulary encoding law .ready (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).attempts ≤
      RetryProgress.capacity (code := Active old instructions) :=
  (every_funded_observation_pays_for_all_actual_retries old instructions start vocabulary encoding law initial control count).trans
    (RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law _)

private theorem partition (entries : List (Attempt old instructions)) :
    tally old instructions start vocabulary encoding law .ready entries + tally old instructions start vocabulary encoding law .blocked entries +
      tally old instructions start vocabulary encoding law .idle entries = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    cases same : kind old instructions start vocabulary encoding law entry <;>
      simp only [tally,List.map_cons,List.sum_cons,same,reduceCtorEq,if_true,if_false,List.length_cons] at * <;> omega

private theorem limited (initial : FundedRetrySource.State old instructions) (control : Controller old instructions) (count : Nat)
    (limit : (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).status = .observationLimit) :
    (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).attempts.length = count ∧
      tally old instructions start vocabulary encoding law .idle (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).attempts = 0 := by
  induction count generalizing initial with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih =>
    simp only [FundedRetrySource.run_succ] at limit ⊢
    split at limit
    · contradiction
    · rename_i nonidle
      simp only [List.length_cons,tally,List.map_cons,List.sum_cons,if_neg nonidle,Nat.zero_add]
      exact ⟨congrArg Nat.succ (ih _ limit).1,(ih _ limit).2⟩

theorem the_actual_blocking_budget_generates_a_no_overdue_checkpoint
    (initial : FundedRetrySource.State old instructions) (control : Controller old instructions) (count allowance : Nat)
    (blocked : tally old instructions start vocabulary encoding law .blocked
      (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).attempts ≤ allowance)
    (opportunity : RetryProgress.capacity (code := Active old instructions) - confirmations old instructions start vocabulary encoding law initial + allowance < count) :
    (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).status = .noOverdue := by
  cases status : (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).status with
  | noOverdue => rfl
  | observationLimit =>
    have full := limited old instructions start vocabulary encoding law initial control count status
    have split := partition old instructions start vocabulary encoding law
      (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).attempts
    have paid := actual_retries_have_the_original_source_interface_capacity old instructions start vocabulary encoding law initial control count
    omega

private theorem idle_census (past : List (EventHistory.Stage (code := Active old instructions)))
    (idle : TimedRetry.produce start past vocabulary encoding law = .idle) :
    TimedDuty.observed start past vocabulary encoding law = [] := by
  unfold TimedRetry.produce at idle
  split at idle
  · rename_i empty
    exact List.head?_eq_none_iff.mp empty
  · repeat first | contradiction | split at idle

private theorem idle_after (entry : Attempt old instructions)
    (idle : kind old instructions start vocabulary encoding law entry = .idle) :
    TimedDuty.observed start (after old instructions start vocabulary encoding law entry.state entry.command).history vocabulary encoding law = [] := by
  have selected : plan old instructions start vocabulary encoding law entry.state entry.command = .idle := by
    cases made : plan old instructions start vocabulary encoding law entry.state entry.command <;> simp_all only [kind,reduceCtorEq]
  change TimedDuty.observed start (TimedRetry.stages start (prepared old instructions start entry.state entry.command) vocabulary encoding law) vocabulary encoding law = []
  rw [show TimedRetry.stages start (prepared old instructions start entry.state entry.command) vocabulary encoding law =
    prepared old instructions start entry.state entry.command by simp only [TimedRetry.stages,selected]]
  exact idle_census old instructions start vocabulary encoding law _ selected

private def noOverdueAt (state : FundedRetrySource.State old instructions) : Prop :=
  TimedDuty.observed start state.history vocabulary encoding law = []

theorem no_overdue_is_the_actual_final_census (initial : FundedRetrySource.State old instructions)
    (control : Controller old instructions) (count : Nat)
    (quiet : (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).status = .noOverdue) :
    TimedDuty.observed start (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).state.history vocabulary encoding law = [] := by
  change noOverdueAt old instructions start vocabulary encoding law
    (FundedRetrySource.run old instructions start vocabulary encoding law control count initial).state
  induction count generalizing initial with
  | zero => contradiction
  | succ count ih =>
    simp only [FundedRetrySource.run_succ] at quiet ⊢
    split at quiet
    · rename_i idle
      simp only [if_pos idle]
      exact idle_after old instructions start vocabulary encoding law (⟨initial,control initial⟩ : Attempt old instructions) idle
    · rename_i active
      simp only [if_neg active]
      exact ih (after old instructions start vocabulary encoding law initial (control initial)) quiet

abbrev native (state : FundedRetrySource.State old instructions) := ProgrammeHistory.execution_face_shares_whole_ledger_and_next
  (cursor old instructions start state).source.input (EventStep.boundary (cursor old instructions start state))

theorem every_actual_final_record_is_in_its_own_native_financial_inventory (state : FundedRetrySource.State old instructions)
    (record : StageTrace.Record (code := Active old instructions)) (inside : record ∈ StageTrace.records start state.history) :
    (Financial.inventoryAt (cursor old instructions start state).source.input
      (ProgrammeHistory.visitAt (cursor old instructions start state).source.input (EventStep.boundary record.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (cursor old instructions start state).source.input) = StageTrace.items record :=
  StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ inside
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedRetryProgress

import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointDrainProgress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenPrefixProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
open OpenDeliverySource (State Controller Attempt)
open JointDrainSource (gain gains stalls confirmations feed)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))

abbrev run := OpenDeliverySource.run old instructions start vocabulary encoding law

theorem every_observation_counts_its_entire_actual_confirmation_gain
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial +
      gains old instructions start vocabulary encoding law (run old instructions start vocabulary encoding law initial control count).attempts =
      confirmations old instructions start vocabulary encoding law (run old instructions start vocabulary encoding law initial control count).state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have step := JointDrainProgress.each_actual_step_conserves_its_full_confirmation_gain old instructions start vocabulary encoding law
      (⟨(run old instructions start vocabulary encoding law initial control count).state,
        control (run old instructions start vocabulary encoding law initial control count).state⟩ : Attempt old instructions)
    dsimp only at step
    dsimp only [run,gains,JointDrainSource.after] at ih step
    simp only [run,OpenDeliverySource.run_succ,gains,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    change _ + (_ + gain old instructions start vocabulary encoding law _) = _
    omega

theorem every_actual_observation_is_retirement_confirmation_or_stall
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    count ≤ (run old instructions start vocabulary encoding law initial control count).retired.length +
      gains old instructions start vocabulary encoding law (run old instructions start vocabulary encoding law initial control count).attempts +
      stalls old instructions start vocabulary encoding law (run old instructions start vocabulary encoding law initial control count).attempts := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    let entry : Attempt old instructions := ⟨(run old instructions start vocabulary encoding law initial control count).state,
      control (run old instructions start vocabulary encoding law initial control count).state⟩
    have paid : 1 ≤ (feed old instructions start entry).retired.length + gain old instructions start vocabulary encoding law entry +
        (if (feed old instructions start entry).retired.length + gain old instructions start vocabulary encoding law entry = 0 then 1 else 0) := by
      split <;> omega
    dsimp only [run,gains,stalls] at ih
    simp only [run,OpenDeliverySource.run_succ,gains,stalls,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_append]
    change count+1 ≤ _ + (feed old instructions start entry).retired.length +
      (_ + gain old instructions start vocabulary encoding law entry) +
      (_ + if (feed old instructions start entry).retired.length + gain old instructions start vocabulary encoding law entry = 0 then 1 else 0)
    omega

theorem actual_progress_pays_for_any_fixed_number_of_fifo_retirements
    (initial : State old instructions) (control : Controller old instructions) (count allowance size : Nat)
    (bounded : stalls old instructions start vocabulary encoding law
      (run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : size + (RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial) + allowance ≤ count) :
    size ≤ (run old instructions start vocabulary encoding law initial control count).retired.length := by
  have paid := every_actual_observation_is_retirement_confirmation_or_stall old instructions start vocabulary encoding law initial control count
  have exactGain := every_observation_counts_its_entire_actual_confirmation_gain old instructions start vocabulary encoding law initial control count
  have capacity := RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law
    (run old instructions start vocabulary encoding law initial control count).state.history
  change confirmations old instructions start vocabulary encoding law
    (run old instructions start vocabulary encoding law initial control count).state ≤ _ at capacity
  omega

theorem every_initial_prefix_is_retired_without_bounding_later_input
    (initial : State old instructions) (control : Controller old instructions) (count allowance size : Nat)
    (present : size ≤ initial.pending.length)
    (bounded : stalls old instructions start vocabulary encoding law
      (run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : size + (RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial) + allowance ≤ count) :
    initial.pending.take size <+: (run old instructions start vocabulary encoding law initial control count).retired := by
  have retired := actual_progress_pays_for_any_fixed_number_of_fifo_retirements old instructions start vocabulary encoding law initial control count allowance size bounded opportunity
  have fifo := OpenDeliveryProgress.all_new_input_is_retired_in_fifo_order_or_remains_live old instructions start vocabulary encoding law initial control count
  have original : initial.pending.take size <+:
      (run old instructions start vocabulary encoding law initial control count).retired ++
        (run old instructions start vocabulary encoding law initial control count).state.pending := by
    rw [← fifo]
    exact (List.take_prefix size initial.pending).trans (List.prefix_append _ _)
  exact List.prefix_of_prefix_length_le original (List.prefix_append _ _) (by simp only [List.length_take];omega)

-- The suffix starts at the actual endpoint, with its original history, queue and accounts.
theorem a_later_observation_resumes_the_actual_endpoint
    (initial : State old instructions) (control : Controller old instructions) (before count : Nat) :
    run old instructions start vocabulary encoding law initial control (before+count) =
      let earlier := run old instructions start vocabulary encoding law initial control before
      let later := run old instructions start vocabulary encoding law earlier.state control count
      ⟨later.state,earlier.attempts ++ later.attempts,earlier.arrivals ++ later.arrivals,earlier.retired ++ later.retired⟩ := by
  induction count with
  | zero => simp only [Nat.add_zero,run,OpenDeliverySource.run_zero,List.append_nil]
  | succ count ih => simp only [Nat.add_succ,run,OpenDeliverySource.run_succ,ih,List.append_assoc]

theorem every_actual_suffix_retires_its_existing_prefix
    (initial : State old instructions) (control : Controller old instructions) (before count allowance size : Nat)
    (present : size ≤ (run old instructions start vocabulary encoding law initial control before).state.pending.length)
    (bounded : stalls old instructions start vocabulary encoding law
      (run old instructions start vocabulary encoding law
        (run old instructions start vocabulary encoding law initial control before).state control count).attempts ≤ allowance)
    (opportunity : size + (RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law
        (run old instructions start vocabulary encoding law initial control before).state) + allowance ≤ count) :
    (run old instructions start vocabulary encoding law initial control before).retired ++
        (run old instructions start vocabulary encoding law initial control before).state.pending.take size <+:
      (run old instructions start vocabulary encoding law initial control (before+count)).retired := by
  have served := every_initial_prefix_is_retired_without_bounding_later_input old instructions start vocabulary encoding law
    (run old instructions start vocabulary encoding law initial control before).state control count allowance size present bounded opportunity
  rw [a_later_observation_resumes_the_actual_endpoint]
  obtain ⟨more,same⟩ := served
  exact ⟨more,by rw [List.append_assoc,same]⟩

theorem the_first_actual_arrival_keeps_its_place_before_all_later_input
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    (control initial).supply.incoming <+:
      (run old instructions start vocabulary encoding law initial control (count+1)).arrivals := by
  rw [show count+1 = 1+count by omega,a_later_observation_resumes_the_actual_endpoint]
  exact List.prefix_append _ _

theorem every_first_arrival_prefix_is_retired_without_bounding_later_input
    (initial : State old instructions) (control : Controller old instructions) (count allowance size : Nat)
    (present : size ≤ (initial.pending ++ (control initial).supply.incoming).length)
    (bounded : stalls old instructions start vocabulary encoding law
      (run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : size + (RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial) + allowance ≤ count) :
    (initial.pending ++ (control initial).supply.incoming).take size <+:
      (run old instructions start vocabulary encoding law initial control count).retired := by
  cases count with
  | zero =>
    have empty : size = 0 := by omega
    rw [empty,List.take_zero]
    exact List.nil_prefix
  | succ count =>
    have retired := actual_progress_pays_for_any_fixed_number_of_fifo_retirements old instructions start vocabulary encoding law initial control (count+1) allowance size bounded opportunity
    have fifo := OpenDeliveryProgress.all_new_input_is_retired_in_fifo_order_or_remains_live old instructions start vocabulary encoding law initial control (count+1)
    have incoming := the_first_actual_arrival_keeps_its_place_before_all_later_input old instructions start vocabulary encoding law initial control count
    have born : initial.pending ++ (control initial).supply.incoming <+:
        initial.pending ++ (run old instructions start vocabulary encoding law initial control (count+1)).arrivals := by
      obtain ⟨more,same⟩ := incoming
      exact ⟨more,by rw [List.append_assoc,same]⟩
    have whole := (List.take_prefix size (initial.pending ++ (control initial).supply.incoming)).trans born
    rw [fifo] at whole
    exact List.prefix_of_prefix_length_le whole (List.prefix_append _ _) (by simp only [List.length_take];omega)

theorem every_actual_arrival_has_its_own_retirement_position
    (initial : State old instructions) (control : Controller old instructions) (before count allowance position : Nat)
    (present : position < (control (run old instructions start vocabulary encoding law initial control before).state).supply.incoming.length)
    (bounded : stalls old instructions start vocabulary encoding law
      (run old instructions start vocabulary encoding law
        (run old instructions start vocabulary encoding law initial control before).state control count).attempts ≤ allowance)
    (opportunity : (run old instructions start vocabulary encoding law initial control before).state.pending.length + position+1 +
      (RetryProgress.capacity (code := Active old instructions) - confirmations old instructions start vocabulary encoding law
        (run old instructions start vocabulary encoding law initial control before).state) + allowance ≤ count) :
    (run old instructions start vocabulary encoding law initial control (before+count)).retired[
      (run old instructions start vocabulary encoding law initial control before).retired.length +
      (run old instructions start vocabulary encoding law initial control before).state.pending.length + position]? =
      some ((control (run old instructions start vocabulary encoding law initial control before).state).supply.incoming[position]) := by
  let earlier := run old instructions start vocabulary encoding law initial control before
  change position < (control earlier.state).supply.incoming.length at present
  have served := every_first_arrival_prefix_is_retired_without_bounding_later_input old instructions start vocabulary encoding law
    earlier.state control count allowance (earlier.state.pending.length+position+1)
    (by simp only [List.length_append];omega) bounded opportunity
  rw [a_later_observation_resumes_the_actual_endpoint]
  change (earlier.retired ++ (run old instructions start vocabulary encoding law earlier.state control count).retired)[
    earlier.retired.length + earlier.state.pending.length+position]? = _
  rw [List.getElem?_append_right (by omega),show earlier.retired.length + earlier.state.pending.length+position - earlier.retired.length = earlier.state.pending.length+position by omega]
  obtain ⟨more,same⟩ := served
  have index : earlier.state.pending.length+position <
      ((earlier.state.pending ++ (control earlier.state).supply.incoming).take (earlier.state.pending.length+position+1)).length := by
    simp only [List.length_take,List.length_append]
    omega
  rw [← same,List.getElem?_append_left index,List.getElem?_take_of_succ,
    List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_eq_getElem present]

theorem every_retirement_position_retains_the_original_arrival_ordinal
    (initial : State old instructions) (control : Controller old instructions) (before position : Nat) :
    (run old instructions start vocabulary encoding law initial control before).retired.length +
        (run old instructions start vocabulary encoding law initial control before).state.pending.length + position =
      initial.pending.length + (run old instructions start vocabulary encoding law initial control before).arrivals.length + position := by
  have fifo := congrArg List.length (OpenDeliveryProgress.all_new_input_is_retired_in_fifo_order_or_remains_live old instructions start vocabulary encoding law initial control before)
  simp only [List.length_append] at fifo
  dsimp only [run]
  omega

theorem an_actual_arrival_retains_both_its_source_ordinal_and_retired_value
    (initial : State old instructions) (control : Controller old instructions) (before count allowance position : Nat)
    (present : position < (control (run old instructions start vocabulary encoding law initial control before).state).supply.incoming.length)
    (bounded : stalls old instructions start vocabulary encoding law
      (run old instructions start vocabulary encoding law
        (run old instructions start vocabulary encoding law initial control before).state control count).attempts ≤ allowance)
    (opportunity : (run old instructions start vocabulary encoding law initial control before).state.pending.length + position+1 +
      (RetryProgress.capacity (code := Active old instructions) - confirmations old instructions start vocabulary encoding law
        (run old instructions start vocabulary encoding law initial control before).state) + allowance ≤ count) :
    ((run old instructions start vocabulary encoding law initial control before).retired.length +
        (run old instructions start vocabulary encoding law initial control before).state.pending.length + position,
      (run old instructions start vocabulary encoding law initial control (before+count)).retired[
        (run old instructions start vocabulary encoding law initial control before).retired.length +
        (run old instructions start vocabulary encoding law initial control before).state.pending.length + position]?) =
      (initial.pending.length + (run old instructions start vocabulary encoding law initial control before).arrivals.length + position,
        some ((control (run old instructions start vocabulary encoding law initial control before).state).supply.incoming[position])) := by
  exact Prod.ext (every_retirement_position_retains_the_original_arrival_ordinal old instructions start vocabulary encoding law initial control before position)
    (every_actual_arrival_has_its_own_retirement_position old instructions start vocabulary encoding law initial control before count allowance position present bounded opportunity)

abbrev inputAttempt (entry : Attempt old instructions) :=
  InletOmissionSource.attempt old instructions (FundedRetrySource.inlet old instructions start entry.state) entry.command.supply

theorem every_actual_retirement_consumes_the_original_valid_execution
    (entry : Attempt old instructions) (retired : (feed old instructions start entry).retired ≠ []) :
    (inputAttempt old instructions start entry).row.submitted = (feed old instructions start entry).retired ∧
      ∀ item ∈ StageTrace.items (inputAttempt old instructions start entry).row,old.law.Valid item.before item.request := by
  have actual : (inputAttempt old instructions start entry).observation = some .executed := by
    change OpenInletSource.retired old instructions (FundedRetrySource.inlet old instructions start entry.state) entry.command.supply ≠ [] at retired
    unfold OpenInletSource.retired at retired
    split at retired
    · assumption
    · contradiction
  exact OpenInletProgress.every_retirement_consumes_its_actual_paid_original_request old instructions
    (FundedRetrySource.inlet old instructions start entry.state) (fun _ => entry.command.supply) 1
    (inputAttempt old instructions start entry) (List.mem_singleton_self _) actual

theorem all_retirements_are_the_concatenated_actual_input_executions
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    (run old instructions start vocabulary encoding law initial control count).retired =
      (run old instructions start vocabulary encoding law initial control count).attempts.flatMap
        (fun entry => (feed old instructions start entry).retired) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [run,OpenDeliverySource.run_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact congrArg (fun earlier => earlier ++ _) ih

theorem every_retired_request_keeps_its_actual_source_execution
    (initial : State old instructions) (control : Controller old instructions) (count : Nat)
    (request : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (retired : request ∈ (run old instructions start vocabulary encoding law initial control count).retired) :
    ∃ entry ∈ (run old instructions start vocabulary encoding law initial control count).attempts,
      request ∈ (feed old instructions start entry).retired ∧
      (inputAttempt old instructions start entry).row.submitted = (feed old instructions start entry).retired ∧
      ∀ item ∈ StageTrace.items (inputAttempt old instructions start entry).row,old.law.Valid item.before item.request := by
  rw [all_retirements_are_the_concatenated_actual_input_executions,List.mem_flatMap] at retired
  obtain ⟨entry,inside,member⟩ := retired
  have live : (feed old instructions start entry).retired ≠ [] := by
    intro empty
    rw [empty] at member
    contradiction
  exact ⟨entry,inside,member,every_actual_retirement_consumes_the_original_valid_execution old instructions start entry live⟩

abbrev native (state : State old instructions) := OpenDeliveryProgress.native old instructions start state
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenPrefixProgress

import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenDeliverySource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenDeliveryProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
open OpenDeliverySource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))

theorem actual_delivery_keeps_the_paid_send_prefix
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : TimedRetry.Ready start past vocabulary encoding law) (network : Opponent (Active old instructions)) :
    TimedRetry.sent start past vocabulary encoding law answer.overdue answer.supported <+:
      schedule old instructions start vocabulary encoding law past answer network := List.prefix_append _ _

theorem actual_delivery_keeps_the_entire_original_history
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : TimedRetry.Ready start past vocabulary encoding law) (network : Opponent (Active old instructions)) :
    past <+: schedule old instructions start vocabulary encoding law past answer network :=
  (List.prefix_append _ _).trans ((List.prefix_append _ _).trans (List.prefix_append _ _))

theorem withholding_cannot_erase_the_actual_authenticated_send
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : TimedRetry.Ready start past vocabulary encoding law) (network : Opponent (Active old instructions)) :
    StageTransport.verify vocabulary encoding start
      (schedule old instructions start vocabulary encoding law past answer network) answer.wire = true := by
  apply decide_eq_true
  apply List.mem_filterMap.mpr
  refine ⟨(TimedRetry.aligned start past vocabulary encoding law answer.overdue).length, ?_, ?_⟩
  · simp only [schedule, TimedRetry.sent, List.mem_range, List.length_append, List.length_singleton]
    omega
  · exact (StagePrefix.issued_at start
      (TimedRetry.sent start past vocabulary encoding law answer.overdue answer.supported)
      [(SilentWindow.quiet, network)] vocabulary encoding _
      (by simp only [TimedRetry.sent, List.length_append, List.length_singleton]; omega)).trans answer.issued

theorem every_step_keeps_the_whole_actual_history (state : State old instructions) (command : Command old instructions) :
    state.history <+: (after old instructions start vocabulary encoding law state command).history := by
  have preparedPrefix : state.history <+: prepared old instructions start state command := List.prefix_append _ _
  cases selected : plan old instructions start vocabulary encoding law state command with
  | idle => simpa only [after,selected] using preparedPrefix
  | blocked reason => simpa only [after,selected] using preparedPrefix
  | ready answer =>
    simpa only [after,selected] using preparedPrefix.trans
      (actual_delivery_keeps_the_entire_original_history old instructions start vocabulary encoding law _ answer command.network)

private theorem gains
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : TimedRetry.Ready start past vocabulary encoding law) (network : Opponent (Active old instructions))
    (received : TimedDuty.Confirmed start (schedule old instructions start vocabulary encoding law past answer network)
      vocabulary encoding law answer.overdue.emission) :
    (DutyConfirmation.contents start vocabulary encoding law past).card + 1 ≤
      (DutyConfirmation.contents start vocabulary encoding law (schedule old instructions start vocabulary encoding law past answer network)).card := by
  have ordered := actual_delivery_keeps_the_entire_original_history old instructions start vocabulary encoding law past answer network
  have kept := DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law _ _ ordered
  obtain ⟨more, same⟩ := ordered
  have original : answer.overdue.emission ∈ StageDuty.origins start vocabulary encoding
      (schedule old instructions start vocabulary encoding law past answer network) := by
    rw [← same]
    exact DutyConfirmation.the_original_emission_survives_actual_extension start vocabulary encoding past more
      answer.overdue.emission answer.overdue.actual
  have gained := (DutyConfirmation.mem_contents start vocabulary encoding law _ _).mpr ⟨answer.overdue.emission,original,received,rfl⟩
  have included := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨gained,kept⟩)
  rw [Finset.card_insert_of_notMem (RetryProgress.the_original_overdue_content_is_not_already_confirmed encoding start vocabulary law past answer)] at included
  exact included

theorem only_actual_confirmation_pays_for_progress (entry : Attempt old instructions) :
    confirmations old instructions start vocabulary encoding law entry.state +
      (if kind old instructions start vocabulary encoding law entry = .confirmed then 1 else 0) ≤
      confirmations old instructions start vocabulary encoding law
        (after old instructions start vocabulary encoding law entry.state entry.command) := by
  have kept := Finset.card_le_card (DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law
    entry.state.history (prepared old instructions start entry.state entry.command) (List.prefix_append _ _))
  have allKept := Finset.card_le_card (DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law
    entry.state.history (after old instructions start vocabulary encoding law entry.state entry.command).history
    (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _))
  cases selected : plan old instructions start vocabulary encoding law entry.state entry.command with
  | idle => simpa only [kind,selected,reduceCtorEq,if_false,Nat.add_zero] using allKept
  | blocked reason => simpa only [kind,selected,reduceCtorEq,if_false,Nat.add_zero] using allKept
  | ready answer =>
    simp only [kind,selected,confirmationKind]
    split
    · rename_i received
      simp only [if_true]
      simp only [after,selected]
      change _ ≤ (DutyConfirmation.contents start vocabulary encoding law
        (schedule old instructions start vocabulary encoding law _ answer entry.command.network)).card
      exact (Nat.add_le_add_right kept 1).trans (gains old instructions start vocabulary encoding law _ answer _ received)
    · simpa only [reduceCtorEq,if_false,Nat.add_zero] using allKept

private theorem step_fifo (state : State old instructions) (command : Command old instructions) :
    state.pending ++ (FundedRetrySource.feed old instructions start state command.supply).arrivals =
      (FundedRetrySource.feed old instructions start state command.supply).retired ++
        (after old instructions start vocabulary encoding law state command).pending :=
  OpenInletProgress.all_initial_and_new_input_is_retired_in_fifo_order_or_retained old instructions
    (FundedRetrySource.inlet old instructions start state) (fun _ => command.supply) 1

theorem all_new_input_is_retired_in_fifo_order_or_remains_live
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    initial.pending ++ (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).arrivals =
      (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).retired ++
        (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).state.pending := by
  induction count with
  | zero => simp only [OpenDeliverySource.run_zero,List.append_nil,List.nil_append]
  | succ count ih =>
    simp only [OpenDeliverySource.run_succ]
    rw [← List.append_assoc,ih,List.append_assoc,step_fifo old instructions start vocabulary encoding law,List.append_assoc]

theorem every_observation_keeps_the_entire_actual_prefix
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    initial.history <+: (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).state.history := by
  induction count with
  | zero => exact List.prefix_refl _
  | succ count ih => exact ih.trans (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _)

theorem idle_never_suppresses_the_next_actual_observation
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).attempts.length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [OpenDeliverySource.run_succ,List.length_append,List.length_singleton] using congrArg Nat.succ ih

theorem all_counted_confirmations_are_paid_by_actual_distinct_content
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial + confirmedCount old instructions start vocabulary encoding law
      (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).attempts ≤
      confirmations old instructions start vocabulary encoding law
        (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).state := by
  induction count with
  | zero => simp only [OpenDeliverySource.run_zero,confirmedCount,List.map_nil,List.sum_nil,Nat.add_zero,Nat.le_refl]
  | succ count ih =>
    have grew := only_actual_confirmation_pays_for_progress old instructions start vocabulary encoding law
      (⟨(OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).state,
        control (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).state⟩ : Attempt old instructions)
    dsimp only at grew
    simp only [OpenDeliverySource.run_succ,confirmedCount,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at ih ⊢
    omega

theorem confirmations_have_the_original_source_interface_capacity
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial + confirmedCount old instructions start vocabulary encoding law
      (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).attempts ≤ RetryProgress.capacity (code := Active old instructions) :=
  (all_counted_confirmations_are_paid_by_actual_distinct_content old instructions start vocabulary encoding law initial control count).trans
    (RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law _)

def obstructionCount (entries : List (Attempt old instructions)) : Nat :=
  (entries.map fun entry => if kind old instructions start vocabulary encoding law entry = .blocked ∨
    kind old instructions start vocabulary encoding law entry = .unconfirmed then 1 else 0).sum

private theorem no_idle_partition (entries : List (Attempt old instructions))
    (active : ∀ entry ∈ entries, kind old instructions start vocabulary encoding law entry ≠ .idle) :
    confirmedCount old instructions start vocabulary encoding law entries +
      obstructionCount old instructions start vocabulary encoding law entries = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have tail := ih (fun element inside => active element (List.mem_cons_of_mem _ inside))
    have first := active entry (List.mem_cons_self)
    have front : (if kind old instructions start vocabulary encoding law entry = .confirmed then 1 else 0) +
        (if kind old instructions start vocabulary encoding law entry = .blocked ∨
          kind old instructions start vocabulary encoding law entry = .unconfirmed then 1 else 0) = 1 := by
      cases classified : kind old instructions start vocabulary encoding law entry <;> simp_all
    simp only [confirmedCount,obstructionCount,List.map_cons,List.sum_cons,List.length_cons] at tail ⊢
    omega

theorem an_actual_obstruction_budget_forces_an_idle_observation
    (initial : State old instructions) (control : Controller old instructions) (count allowance : Nat)
    (bounded : obstructionCount old instructions start vocabulary encoding law
      (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial + allowance < count) :
    ∃ entry ∈ (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).attempts,
      kind old instructions start vocabulary encoding law entry = .idle := by
  by_contra absent
  have active : ∀ entry ∈ (OpenDeliverySource.run old instructions start vocabulary encoding law initial control count).attempts,
      kind old instructions start vocabulary encoding law entry ≠ .idle := by simpa only [not_exists,not_and] using absent
  have partition := no_idle_partition old instructions start vocabulary encoding law _ active
  have size := idle_never_suppresses_the_next_actual_observation old instructions start vocabulary encoding law initial control count
  have capacity := confirmations_have_the_original_source_interface_capacity old instructions start vocabulary encoding law initial control count
  omega

private theorem idle_census (past : List (EventHistory.Stage (code := Active old instructions)))
    (idle : TimedRetry.produce start past vocabulary encoding law = .idle) :
    TimedDuty.observed start past vocabulary encoding law = [] := by
  unfold TimedRetry.produce at idle
  split at idle
  · rename_i empty
    exact List.head?_eq_none_iff.mp empty
  · repeat first | contradiction | split at idle

private def noOverdueAt (past : List (EventHistory.Stage (code := Active old instructions))) : Prop :=
  TimedDuty.observed start past vocabulary encoding law = []

theorem idle_is_the_actual_no_overdue_census (entry : Attempt old instructions)
    (idle : kind old instructions start vocabulary encoding law entry = .idle) :
    TimedDuty.observed start (after old instructions start vocabulary encoding law entry.state entry.command).history
      vocabulary encoding law = [] := by
  have selected : plan old instructions start vocabulary encoding law entry.state entry.command = .idle := by
    cases made : plan old instructions start vocabulary encoding law entry.state entry.command with
    | idle => rfl
    | blocked reason => simp only [kind,made,reduceCtorEq] at idle
    | ready answer => simp only [kind,made,confirmationKind] at idle; split at idle <;> contradiction
  change noOverdueAt old instructions start vocabulary encoding law
    (after old instructions start vocabulary encoding law entry.state entry.command).history
  simp only [after,selected]
  exact idle_census old instructions start vocabulary encoding law _ selected

abbrev native (state : State old instructions) := FundedRetryProgress.native old instructions start state
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenDeliveryProgress

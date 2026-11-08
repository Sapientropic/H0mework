import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRetrySource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRetryProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
open OpenDeliverySource (State Command Controller Attempt confirmationKind)
open DemandRetrySource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))

abbrev staged (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : Ready old instructions start vocabulary encoding law past) (network : Opponent (Active old instructions)) :=
  DemandRetrySource.schedule old instructions start vocabulary encoding law past answer.candidate answer.supported network

theorem candidate_content_is_not_already_confirmed
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (candidate : Candidate old instructions start vocabulary encoding law past) :
    DutyConfirmation.key start vocabulary encoding candidate.val ∉ DutyConfirmation.contents start vocabulary encoding law past := by
  intro member
  obtain ⟨emission,_,confirmed,same⟩ := (DutyConfirmation.mem_contents start vocabulary encoding law past _).mp member
  exact (candidate_is_actual_and_unconfirmed old instructions start vocabulary encoding law past candidate).2
    ((DutyConfirmation.confirmation_depends_on_the_original_content start vocabulary encoding law past emission candidate.val same).mp confirmed)

theorem actual_delivery_keeps_the_paid_send_prefix
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : Ready old instructions start vocabulary encoding law past) (network : Opponent (Active old instructions)) :
    sent old instructions start vocabulary encoding law past answer.candidate answer.supported <+:
      staged old instructions start vocabulary encoding law past answer network := List.prefix_append _ _

theorem actual_delivery_keeps_the_entire_original_history
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : Ready old instructions start vocabulary encoding law past) (network : Opponent (Active old instructions)) :
    past <+: staged old instructions start vocabulary encoding law past answer network :=
  (List.prefix_append _ _).trans ((List.prefix_append _ _).trans (List.prefix_append _ _))

theorem withholding_cannot_erase_the_actual_authenticated_send
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : Ready old instructions start vocabulary encoding law past) (network : Opponent (Active old instructions)) :
    StageTransport.verify vocabulary encoding start
      (staged old instructions start vocabulary encoding law past answer network) answer.wire = true := by
  apply decide_eq_true
  apply List.mem_filterMap.mpr
  refine ⟨(aligned old instructions start vocabulary encoding law past answer.candidate).length, ?_, ?_⟩
  · simp only [staged, sent, List.mem_range, List.length_append, List.length_singleton]
    omega
  · exact (StagePrefix.issued_at start
      (sent old instructions start vocabulary encoding law past answer.candidate answer.supported)
      [(SilentWindow.quiet, network)] vocabulary encoding _
      (by simp only [sent, List.length_append, List.length_singleton]; omega)).trans answer.issued

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
    (answer : Ready old instructions start vocabulary encoding law past) (network : Opponent (Active old instructions))
    (received : TimedDuty.Confirmed start (staged old instructions start vocabulary encoding law past answer network)
      vocabulary encoding law answer.candidate.val) :
    (DutyConfirmation.contents start vocabulary encoding law past).card + 1 ≤
      (DutyConfirmation.contents start vocabulary encoding law (staged old instructions start vocabulary encoding law past answer network)).card := by
  have ordered := actual_delivery_keeps_the_entire_original_history old instructions start vocabulary encoding law past answer network
  have kept := DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law _ _ ordered
  obtain ⟨more, same⟩ := ordered
  have original : answer.candidate.val ∈ StageDuty.origins start vocabulary encoding
      (staged old instructions start vocabulary encoding law past answer network) := by
    rw [← same]
    exact DutyConfirmation.the_original_emission_survives_actual_extension start vocabulary encoding past more
      answer.candidate.val (candidate_is_actual_and_unconfirmed old instructions start vocabulary encoding law past answer.candidate).1
  have gained := (DutyConfirmation.mem_contents start vocabulary encoding law _ _).mpr ⟨answer.candidate.val,original,received,rfl⟩
  have included := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨gained,kept⟩)
  rw [Finset.card_insert_of_notMem (candidate_content_is_not_already_confirmed old instructions start vocabulary encoding law past answer.candidate)] at included
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
        (staged old instructions start vocabulary encoding law _ answer entry.command.network)).card
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
    initial.pending ++ (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).arrivals =
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).retired ++
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.pending := by
  induction count with
  | zero => simp only [DemandRetrySource.run_zero,List.append_nil,List.nil_append]
  | succ count ih =>
    simp only [DemandRetrySource.run_succ]
    rw [← List.append_assoc,ih,List.append_assoc,step_fifo old instructions start vocabulary encoding law,List.append_assoc]

theorem every_observation_keeps_the_entire_actual_prefix
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    initial.history <+: (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history := by
  induction count with
  | zero => exact List.prefix_refl _
  | succ count ih => exact ih.trans (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _)

theorem idle_never_suppresses_the_next_actual_observation
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts.length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [DemandRetrySource.run_succ,List.length_append,List.length_singleton] using congrArg Nat.succ ih

theorem all_counted_confirmations_are_paid_by_actual_distinct_content
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial + confirmedCount old instructions start vocabulary encoding law
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts ≤
      confirmations old instructions start vocabulary encoding law
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state := by
  induction count with
  | zero => simp only [DemandRetrySource.run_zero,confirmedCount,List.map_nil,List.sum_nil,Nat.add_zero,Nat.le_refl]
  | succ count ih =>
    have grew := only_actual_confirmation_pays_for_progress old instructions start vocabulary encoding law
      (⟨(DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state,
        control (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state⟩ : Attempt old instructions)
    dsimp only at grew
    simp only [DemandRetrySource.run_succ,confirmedCount,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at ih ⊢
    omega

theorem confirmations_have_the_original_source_interface_capacity
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial + confirmedCount old instructions start vocabulary encoding law
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts ≤ RetryProgress.capacity (code := Active old instructions) :=
  (all_counted_confirmations_are_paid_by_actual_distinct_content old instructions start vocabulary encoding law initial control count).trans
    (RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law _)

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
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial + allowance < count) :
    ∃ entry ∈ (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts,
      kind old instructions start vocabulary encoding law entry = .idle := by
  by_contra absent
  have active : ∀ entry ∈ (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts,
      kind old instructions start vocabulary encoding law entry ≠ .idle := by simpa only [not_exists,not_and] using absent
  have partition := no_idle_partition old instructions start vocabulary encoding law _ active
  have size := idle_never_suppresses_the_next_actual_observation old instructions start vocabulary encoding law initial control count
  have capacity := confirmations_have_the_original_source_interface_capacity old instructions start vocabulary encoding law initial control count
  omega


private theorem idle_clears_the_actual_duty_census
    (past : List (EventHistory.Stage (code := Active old instructions)))
    (idle : produce old instructions start vocabulary encoding law past = .idle) :
    duties old instructions start vocabulary encoding law past = [] := by
  have empty : (duties old instructions start vocabulary encoding law past).attach = [] := by
    unfold produce at idle
    split at idle
    · rename_i none
      exact List.head?_eq_none_iff.mp none
    · repeat first | contradiction | split at idle
  have size := congrArg List.length empty
  simp only [List.length_attach,List.length_nil] at size
  exact List.length_eq_zero_iff.mp size

theorem idle_means_every_actual_original_duty_has_a_receipt
    (entry : Attempt old instructions)
    (idle : kind old instructions start vocabulary encoding law entry = .idle) :
    ∀ emission ∈ StageDuty.origins start vocabulary encoding
      (after old instructions start vocabulary encoding law entry.state entry.command).history,
      TimedDuty.Confirmed start (after old instructions start vocabulary encoding law entry.state entry.command).history
        vocabulary encoding law emission := by
  have selected : plan old instructions start vocabulary encoding law entry.state entry.command = .idle := by
    cases made : plan old instructions start vocabulary encoding law entry.state entry.command with
    | idle => rfl
    | blocked reason => simp only [kind,made,reduceCtorEq] at idle
    | ready answer => simp only [kind,made,confirmationKind] at idle; split at idle <;> contradiction
  have empty := idle_clears_the_actual_duty_census old instructions start vocabulary encoding law
    (prepared old instructions start entry.state entry.command) selected
  have complete : ∀ emission ∈ StageDuty.origins start vocabulary encoding
      (prepared old instructions start entry.state entry.command),
      TimedDuty.Confirmed start (prepared old instructions start entry.state entry.command) vocabulary encoding law emission := by
    intro emission actual
    by_contra missing
    have member : emission ∈ duties old instructions start vocabulary encoding law
        (prepared old instructions start entry.state entry.command) := List.mem_filter.mpr ⟨actual,decide_eq_true missing⟩
    rw [empty] at member
    contradiction
  simpa only [after,selected] using complete

theorem every_actual_attempt_retains_both_source_prefixes
    (initial : State old instructions) (control : Controller old instructions) (count : Nat)
    (entry : Attempt old instructions)
    (inside : entry ∈ (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts) :
    initial.history <+: entry.state.history ∧
      (after old instructions start vocabulary encoding law entry.state entry.command).history <+:
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history := by
  induction count with
  | zero => change entry ∈ [] at inside;contradiction
  | succ count ih =>
    change entry ∈ (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts ++ [_] at inside
    rcases List.mem_append.mp inside with earlier | last
    · have prior := ih earlier
      exact ⟨prior.1,prior.2.trans (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law _ _)⟩
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨every_observation_keeps_the_entire_actual_prefix old instructions start vocabulary encoding law initial control count,
        List.prefix_refl _⟩

theorem the_source_sized_actual_failure_budget_confirms_every_initial_duty
    (initial : State old instructions) (control : Controller old instructions) (count allowance : Nat)
    (bounded : obstructionCount old instructions start vocabulary encoding law
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial + allowance < count) :
    ∀ emission ∈ StageDuty.origins start vocabulary encoding initial.history,
      TimedDuty.Confirmed start (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history
        vocabulary encoding law emission := by
  obtain ⟨entry,inside,idle⟩ := an_actual_obstruction_budget_forces_an_idle_observation old instructions start vocabulary encoding law initial control count allowance bounded opportunity
  have lineages := every_actual_attempt_retains_both_source_prefixes old instructions start vocabulary encoding law initial control count entry inside
  have complete := idle_means_every_actual_original_duty_has_a_receipt old instructions start vocabulary encoding law entry idle
  have initialPrefix := lineages.1.trans (every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law entry.state entry.command)
  intro emission actual
  have original : emission ∈ StageDuty.origins start vocabulary encoding
      (after old instructions start vocabulary encoding law entry.state entry.command).history := by
    obtain ⟨more,same⟩ := initialPrefix
    rw [← same]
    exact DutyConfirmation.the_original_emission_survives_actual_extension start vocabulary encoding _ more emission actual
  have received := complete emission original
  obtain ⟨more,same⟩ := lineages.2
  rw [← same]
  exact DutyConfirmation.the_actual_confirmation_survives_extension start vocabulary encoding law _ more emission received

theorem the_same_actual_completion_terminates_each_initial_native_row
    (initial : State old instructions) (control : Controller old instructions) (count allowance : Nat)
    (bounded : obstructionCount old instructions start vocabulary encoding law
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).attempts ≤ allowance)
    (opportunity : RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law initial + allowance < count)
    (emission : StageDuty.Emission start vocabulary encoding)
    (actual : emission ∈ StageDuty.origins start vocabulary encoding initial.history) :
    ∃ row ∈ StageDuty.histories start vocabulary encoding law
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history,
      row.1 = emission ∧ row.2.2.state.TerminalAt 0 := by
  have confirmed := the_source_sized_actual_failure_budget_confirms_every_initial_duty old instructions start vocabulary encoding law initial control count allowance bounded opportunity emission actual
  have original : emission ∈ StageDuty.origins start vocabulary encoding
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history := by
    obtain ⟨more,same⟩ := every_observation_keeps_the_entire_actual_prefix old instructions start vocabulary encoding law initial control count
    rw [← same]
    exact DutyConfirmation.the_original_emission_survives_actual_extension start vocabulary encoding _ more emission actual
  let row : Sigma (StageDuty.History start vocabulary encoding law) :=
    ⟨emission,StageDuty.through start vocabulary encoding law emission
      ((DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history.drop emission.birthStages.length)⟩
  have member : row ∈ StageDuty.histories start vocabulary encoding law
      (DemandRetrySource.run old instructions start vocabulary encoding law initial control count).state.history := List.mem_map.mpr ⟨emission,original,rfl⟩
  exact ⟨row,member,rfl,(StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law _ row member).mpr confirmed⟩

theorem every_suffix_resumes_the_same_actual_endpoint
    (initial : State old instructions) (control : Controller old instructions) (before count : Nat) :
    DemandRetrySource.run old instructions start vocabulary encoding law initial control (before+count) =
      let earlier := DemandRetrySource.run old instructions start vocabulary encoding law initial control before
      let later := DemandRetrySource.run old instructions start vocabulary encoding law earlier.state control count
      ⟨later.state,earlier.attempts ++ later.attempts,earlier.arrivals ++ later.arrivals,earlier.retired ++ later.retired⟩ := by
  induction count with
  | zero => simp only [Nat.add_zero,DemandRetrySource.run_zero,List.append_nil]
  | succ count ih => simp only [Nat.add_succ,DemandRetrySource.run_succ,ih,List.append_assoc]

theorem every_later_duty_can_consume_its_own_actual_completion_budget
    (initial : State old instructions) (control : Controller old instructions) (before count allowance : Nat)
    (bounded : obstructionCount old instructions start vocabulary encoding law
      (DemandRetrySource.run old instructions start vocabulary encoding law
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control before).state control count).attempts ≤ allowance)
    (opportunity : RetryProgress.capacity (code := Active old instructions) -
      confirmations old instructions start vocabulary encoding law
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control before).state + allowance < count) :
    ∀ emission ∈ StageDuty.origins start vocabulary encoding
        (DemandRetrySource.run old instructions start vocabulary encoding law initial control before).state.history,
      TimedDuty.Confirmed start (DemandRetrySource.run old instructions start vocabulary encoding law initial control (before+count)).state.history
        vocabulary encoding law emission := by
  rw [every_suffix_resumes_the_same_actual_endpoint]
  exact the_source_sized_actual_failure_budget_confirms_every_initial_duty old instructions start vocabulary encoding law _ control count allowance bounded opportunity

abbrev native (state : State old instructions) := OpenDeliveryProgress.native old instructions start state
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRetryProgress

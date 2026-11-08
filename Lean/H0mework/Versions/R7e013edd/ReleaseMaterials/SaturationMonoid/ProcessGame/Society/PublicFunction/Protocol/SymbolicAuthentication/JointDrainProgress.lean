import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointDrainSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointDrainProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
open OpenDeliverySource (State Command Controller Attempt)
open JointDrainSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))

theorem each_actual_step_conserves_its_full_confirmation_gain (entry : Attempt old instructions) :
    confirmations old instructions start vocabulary encoding law entry.state + gain old instructions start vocabulary encoding law entry =
      confirmations old instructions start vocabulary encoding law (after old instructions start vocabulary encoding law entry) := by
  have ordered := OpenDeliveryProgress.every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law entry.state entry.command
  have kept := Finset.card_le_card (DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law _ _ ordered)
  change confirmations old instructions start vocabulary encoding law entry.state ≤
    confirmations old instructions start vocabulary encoding law (after old instructions start vocabulary encoding law entry) at kept
  unfold gain
  change _ + (_ - _) = _
  omega

theorem all_actual_input_is_retired_in_fifo_order_or_remains_live
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    initial.pending ++ (JointDrainSource.run old instructions start vocabulary encoding law control count initial).arrivals =
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).retired ++
        (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state.pending := by
  induction count generalizing initial with
  | zero => simp only [run_zero,List.append_nil,List.nil_append]
  | succ count ih =>
    have step := OpenInletProgress.all_initial_and_new_input_is_retired_in_fifo_order_or_retained old instructions
      (FundedRetrySource.inlet old instructions start initial) (fun _ => (control initial).supply) 1
    change initial.pending ++ (feed old instructions start (⟨initial,control initial⟩ : Attempt old instructions)).arrivals =
      (feed old instructions start (⟨initial,control initial⟩ : Attempt old instructions)).retired ++
        (after old instructions start vocabulary encoding law (⟨initial,control initial⟩ : Attempt old instructions)).pending at step
    simp only [run_succ]
    split
    · exact step
    · rw [← List.append_assoc,step,List.append_assoc,ih,List.append_assoc]

theorem every_observation_keeps_the_entire_actual_history
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    initial.history <+: (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state.history := by
  induction count generalizing initial with
  | zero => exact List.prefix_refl _
  | succ count ih =>
    have step := OpenDeliveryProgress.every_step_keeps_the_whole_actual_history old instructions start vocabulary encoding law initial (control initial)
    simp only [run_succ]
    split
    · exact step
    · exact step.trans (ih _)

theorem every_observation_counts_all_actual_recovery_and_retry_confirmations
    (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    confirmations old instructions start vocabulary encoding law initial +
      gains old instructions start vocabulary encoding law (JointDrainSource.run old instructions start vocabulary encoding law control count initial).attempts =
      confirmations old instructions start vocabulary encoding law
        (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state := by
  induction count generalizing initial with
  | zero => simp only [run_zero,gains,List.map_nil,List.sum_nil,Nat.add_zero]
  | succ count ih =>
    have step := each_actual_step_conserves_its_full_confirmation_gain old instructions start vocabulary encoding law
      (⟨initial,control initial⟩ : Attempt old instructions)
    dsimp only at step
    simp only [run_succ]
    split
    · simpa only [gains,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using step
    · have tail := ih (after old instructions start vocabulary encoding law (⟨initial,control initial⟩ : Attempt old instructions))
      simp only [gains,List.map_cons,List.sum_cons]
      change _ + (_ + gains old instructions start vocabulary encoding law
        (JointDrainSource.run old instructions start vocabulary encoding law control count _).attempts) = _
      omega

def retiredSize (entries : List (Attempt old instructions)) : Nat :=
  (entries.map fun entry => (feed old instructions start entry).retired.length).sum

private theorem retirement_is_actual (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    retiredSize old instructions start (JointDrainSource.run old instructions start vocabulary encoding law control count initial).attempts =
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).retired.length := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
    simp only [run_succ]
    split
    · simp only [retiredSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    · simp only [retiredSize,List.map_cons,List.sum_cons,List.length_append]
      exact congrArg (Nat.add _) (ih _)

private theorem observations_are_paid (entries : List (Attempt old instructions)) :
    entries.length ≤ retiredSize old instructions start entries + gains old instructions start vocabulary encoding law entries +
      stalls old instructions start vocabulary encoding law entries := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons entry entries ih =>
    have paid : 1 ≤ (feed old instructions start entry).retired.length + gain old instructions start vocabulary encoding law entry +
        (if (feed old instructions start entry).retired.length + gain old instructions start vocabulary encoding law entry = 0 then 1 else 0) := by
      split <;> omega
    simp only [retiredSize,gains,stalls,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

private theorem a_cut_retains_every_actual_observation
    (initial : State old instructions) (control : Controller old instructions) (count : Nat)
    (cut : (JointDrainSource.run old instructions start vocabulary encoding law control count initial).status = .observationCut) :
    (JointDrainSource.run old instructions start vocabulary encoding law control count initial).attempts.length = count := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
    simp only [run_succ] at cut ⊢
    split at cut
    · contradiction
    · rename_i stillOpen
      simp only [if_neg stillOpen,List.length_cons]
      exact congrArg Nat.succ (ih _ cut)

theorem actual_input_and_stall_budgets_force_joint_completion
    (initial : State old instructions) (control : Controller old instructions) (count allowance : Nat)
    (bounded : stalls old instructions start vocabulary encoding law
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).attempts ≤ allowance)
    (opportunity : initial.pending.length +
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).arrivals.length +
      (RetryProgress.capacity (code := Active old instructions) - confirmations old instructions start vocabulary encoding law initial) + allowance < count) :
    (JointDrainSource.run old instructions start vocabulary encoding law control count initial).status = .drained := by
  cases status : (JointDrainSource.run old instructions start vocabulary encoding law control count initial).status with
  | drained => rfl
  | observationCut =>
    have countExact := a_cut_retains_every_actual_observation old instructions start vocabulary encoding law initial control count status
    have paid := observations_are_paid old instructions start vocabulary encoding law
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).attempts
    rw [retirement_is_actual old instructions start vocabulary encoding law initial control count] at paid
    have fifo := congrArg List.length (all_actual_input_is_retired_in_fifo_order_or_remains_live old instructions start vocabulary encoding law initial control count)
    simp only [List.length_append] at fifo
    have exactGain := every_observation_counts_all_actual_recovery_and_retry_confirmations old instructions start vocabulary encoding law initial control count
    have capacity := RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state.history
    change confirmations old instructions start vocabulary encoding law
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state ≤ _ at capacity
    omega

theorem completion_consumes_the_actual_empty_queue_and_all_original_receipts
    (initial : State old instructions) (control : Controller old instructions) (count : Nat)
    (done : (JointDrainSource.run old instructions start vocabulary encoding law control count initial).status = .drained) :
    Closed old instructions start vocabulary encoding law
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state := by
  induction count generalizing initial with
  | zero => contradiction
  | succ count ih =>
    simp only [run_succ] at done ⊢
    split at done
    · rename_i complete
      simpa only [if_pos complete] using complete
    · rename_i stillOpen
      simp only [if_neg stillOpen]
      exact ih _ done

theorem completion_terminates_every_original_native_delivery_row
    (initial : State old instructions) (control : Controller old instructions) (count : Nat)
    (done : (JointDrainSource.run old instructions start vocabulary encoding law control count initial).status = .drained)
    (row : Sigma (StageDuty.History start vocabulary encoding law))
    (inside : row ∈ StageDuty.histories start vocabulary encoding law
      (JointDrainSource.run old instructions start vocabulary encoding law control count initial).state.history) :
    row.2.2.state.TerminalAt 0 := by
  have complete := completion_consumes_the_actual_empty_queue_and_all_original_receipts old instructions start vocabulary encoding law initial control count done
  apply (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law _ row inside).mpr
  obtain ⟨emission,member,same⟩ := List.mem_map.mp inside
  subst row
  exact complete.2 emission member

abbrev native (state : State old instructions) := OpenDeliveryProgress.native old instructions start state
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointDrainProgress

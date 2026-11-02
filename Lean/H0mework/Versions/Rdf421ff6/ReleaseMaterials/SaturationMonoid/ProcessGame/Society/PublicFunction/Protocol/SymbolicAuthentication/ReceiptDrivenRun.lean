import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRule

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRun
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat)

abbrev Stages := LocalWindowRun.Stages model
abbrev Mailbox := FreshReception.Mailbox (code := model.source.code)

structure Observation where
  cut : Nat
  fresh : Mailbox model

structure Result where
  state : CompletionState.State model
  status : LocalWindowRun.Status
  inputs : List (InterferenceEnvelope.Input model.source.code)
  pending : Mailbox model
  observations : List (Observation model)

def empty (pending : Mailbox model) := (List.finRange model.source.code.sites).all fun site => (pending site).isEmpty
def sendsClosed (past : Stages model) := (StageTrace.records start past).all fun row =>
  match StageTransport.outgoing row with
  | none => true
  | some (_, recipient) =>
    (RequestReadback.produce vocabulary encoding law start past recipient past.length).receipts.any
      fun receipt => receipt.confirmation.wire.sendCut == row.cursor.cut

def finish (past : Stages model) (pending : Mailbox model) (programme : List (Rule model.source.code)) : Result model :=
  let state := LocalWindowRun.audit model past programme
  let complete := empty model pending = true ∧ sendsClosed model start vocabulary encoding law past = true ∧
    LocalWindowRun.Ready model start vocabulary encoding law state
  ⟨state, if complete then .jointComplete else if UnifiedResponse.fuel model start past = 0 then .exhausted else .observationCut,
    [], pending, []⟩

-- Polling is the original source's local receive interface. Only that site's
-- queued receipts and current signal enter its next action; Goal is a final audit.
def run : List (Rule model.source.code) → Stages model → Mailbox model → Opponent model.source.code → Result model
  | programme, past, pending, rival =>
    let incoming := FreshReception.poll vocabulary encoding law start past
    let queued := FreshReception.queue pending incoming
    let observed : Observation model := ⟨past.length, incoming⟩
    match programme with
    | [] =>
      let ended := finish model start vocabulary encoding law past queued []
      {ended with observations := [observed]}
    | base :: tail =>
      if UnifiedResponse.fuel model start past = 0 then
        let ended := finish model start vocabulary encoding law past queued (base :: tail)
        {ended with observations := [observed]}
      else
        let input := InterferenceEnvelope.observe start past allowance rival
        let rule := ReceiptDrivenRule.protocol base queued
        let row := StageTrace.material (EventHistory.execute start past) rule (EventStep.fixed input.admitted)
        let next := run tail (LocalWindowRun.after model past rule input.admitted) (ReceiptDrivenRule.consume queued row) rival
        {next with inputs := input :: next.inputs, observations := observed :: next.observations}

def template (programme : List (Rule model.source.code)) :=
  programme ++ List.replicate ((EventStep.seed start).remaining - programme.length) SilentWindow.quiet

def produce (programme : List (Rule model.source.code)) (rival : Opponent model.source.code) :=
  run model start vocabulary encoding law allowance (template model start programme) [] (fun _ => []) rival

private theorem finish_keeps_the_complete_goal (past : Stages model) (pending : Mailbox model)
    (programme : List (Rule model.source.code))
    (accepted : (finish model start vocabulary encoding law past pending programme).status = .jointComplete) :
    LocalWindowRun.Ready model start vocabulary encoding law
      (finish model start vocabulary encoding law past pending programme).state := by
  unfold finish at accepted ⊢
  dsimp only at accepted ⊢
  split_ifs at accepted with complete
  exact complete.2.2

theorem success_keeps_the_entire_original_goal
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : Mailbox model)
    (rival : Opponent model.source.code)
    (accepted : (run model start vocabulary encoding law allowance programme past pending rival).status = .jointComplete) :
    LocalWindowRun.Ready model start vocabulary encoding law
      (run model start vocabulary encoding law allowance programme past pending rival).state := by
  induction programme generalizing past pending with
  | nil => exact finish_keeps_the_complete_goal model start vocabulary encoding law _ _ [] accepted
  | cons base tail ih =>
    simp only [run] at accepted ⊢
    split_ifs at accepted ⊢ with stopped
    · exact finish_keeps_the_complete_goal model start vocabulary encoding law _ _ _ accepted
    · exact ih _ _ accepted

theorem execution_keeps_actual_history_and_the_slot_bound
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : Mailbox model)
    (rival : Opponent model.source.code) :
    past <+: (run model start vocabulary encoding law allowance programme past pending rival).state.past ∧
    (run model start vocabulary encoding law allowance programme past pending rival).state.past.length ≤ past.length + programme.length := by
  induction programme generalizing past pending with
  | nil => exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  | cons base tail ih =>
    simp only [run]
    split
    · exact ⟨List.prefix_refl _, by simp only [finish, LocalWindowRun.audit]; omega⟩
    · let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
      let rule := ReceiptDrivenRule.protocol base queued
      let move := (InterferenceEnvelope.observe start past allowance rival).admitted
      have rest := ih (LocalWindowRun.after model past rule move)
        (ReceiptDrivenRule.consume queued (StageTrace.material (EventHistory.execute start past) rule (EventStep.fixed move)))
      refine ⟨(List.prefix_append _ _).trans rest.1, ?_⟩
      have bound := rest.2
      simp only [LocalWindowRun.after, List.length_append, List.length_singleton] at bound
      simpa only [queued, rule, move, LocalWindowRun.after, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

theorem every_actual_snapshot_remains_registered
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : Mailbox model)
    (rival : Opponent model.source.code) :
    (run model start vocabulary encoding law allowance programme past pending rival).state.batches =
      LocalWindowRun.snapshots model (run model start vocabulary encoding law allowance programme past pending rival).state.past := by
  induction programme generalizing past pending with
  | nil => rfl
  | cons base tail ih =>
    simp only [run]
    split
    · rfl
    · exact ih _ _

theorem every_queued_receipt_retains_its_own_actual_birth_prefix
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : Mailbox model)
    (rival : Opponent model.source.code)
    (paid : FreshReception.Accounted vocabulary encoding law start past pending) :
    FreshReception.Accounted vocabulary encoding law start
      (run model start vocabulary encoding law allowance programme past pending rival).state.past
      (run model start vocabulary encoding law allowance programme past pending rival).pending := by
  induction programme generalizing past pending with
  | nil => exact FreshReception.queue_keeps_every_receipts_own_actual_source vocabulary encoding law start past pending paid
  | cons base tail ih =>
    have queued := FreshReception.queue_keeps_every_receipts_own_actual_source vocabulary encoding law start past pending paid
    simp only [run]
    split
    · exact queued
    · apply ih
      apply FreshReception.accountable_pending_survives_actual_extension
      intro site receipt inside
      exact queued site receipt (ReceiptDrivenRule.consumed_receipts_were_already_queued _ _ site receipt inside)

theorem every_fitting_template_slot_executes
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : Mailbox model)
    (rival : Opponent model.source.code) (fits : programme.length ≤ UnifiedResponse.fuel model start past) :
    (run model start vocabulary encoding law allowance programme past pending rival).state.past.length = past.length + programme.length := by
  induction programme generalizing past pending with
  | nil => rfl
  | cons base tail ih =>
    have live : UnifiedResponse.fuel model start past ≠ 0 := by simp only [List.length_cons] at fits; omega
    simp only [run, if_neg live]
    let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
    let rule := ReceiptDrivenRule.protocol base queued
    let move := (InterferenceEnvelope.observe start past allowance rival).admitted
    have nextFits : tail.length ≤ UnifiedResponse.fuel model start (LocalWindowRun.after model past rule move) := by
      simp only [LocalWindowRun.after, UnifiedResponse.fuel_after_actual_extension, List.length_singleton]
      simp only [List.length_cons] at fits
      omega
    rw [ih _ _ nextFits]
    simp only [LocalWindowRun.after, List.length_append, List.length_cons, List.length_nil]
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRun

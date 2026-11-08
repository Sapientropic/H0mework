import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BirthWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryBirthCost
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def sendCost (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :=
  ((List.finRange code.sites).flatMap fun sender => (List.finRange code.sites).map
    fun recipient => (code.sendCost sender recipient).length).sum
abbrev allowance (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :=
  sendCost code + QueueBirthSource.cost code

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_send_word_is_in_the_finite_source_envelope (sender recipient : Fin code.sites) :
    (code.sendCost sender recipient).length ≤ sendCost code := by
  apply List.single_le_sum (fun _ _ => Nat.zero_le _)
  exact List.mem_flatMap.mpr ⟨sender, List.mem_finRange _,
    List.mem_map.mpr ⟨recipient, List.mem_finRange _, rfl⟩⟩

theorem an_actual_send_stage_submits_at_most_its_source_cost (cursor : Cursor code)
    (sender recipient : Fin code.sites) (supported : Event.send sender recipient ∈ code.eventAlphabet) :
    (StageTrace.material cursor (TimedRetry.sending sender recipient supported) SilentWindow.environment).submitted.length ≤
      sendCost code := by
  rw [(StageTrace.material_is_the_actual_step cursor (TimedRetry.sending sender recipient supported) SilentWindow.environment).2]
  by_cases stopped : (EventStep.seed cursor).remaining = 0
  · simp only [word, decision, if_pos stopped, List.length_nil, Nat.zero_le]
  · cases own : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
    | none =>
      simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, SilentWindow.environment,
        Distributed.Recall.Information.Agency.externalChoice, List.length_nil, Nat.zero_le]
    | some site =>
      by_cases same : site = sender
      · subst site
        simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, localEvent,
          TimedRetry.sending, TimedRetry.localSend, stepLocal, Code.step, List.nil_append]
        exact every_send_word_is_in_the_finite_source_envelope sender recipient
      · simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, localEvent,
          TimedRetry.sending, dif_neg same, List.length_nil, Nat.zero_le]

theorem an_actual_fixed_delivery_submits_at_most_its_source_cost (cursor : Cursor code)
    (serial : Nat) (supported : Event.deliver serial ∈ code.eventAlphabet) :
    (StageTrace.material cursor SilentWindow.quiet (TimedRetry.delivery serial supported)).submitted.length ≤
      QueueBirthSource.cost code := by
  rw [(StageTrace.material_is_the_actual_step cursor SilentWindow.quiet (TimedRetry.delivery serial supported)).2]
  by_cases stopped : (EventStep.seed cursor).remaining = 0
  · simp only [word, decision, if_pos stopped, List.length_nil, Nat.zero_le]
  · cases own : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
    | some site =>
      simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, localEvent, SilentWindow.quiet,
        List.length_nil, Nat.zero_le]
    | none =>
      simp only [word, decision, if_neg stopped, Cursor.controller, driver, own, TimedRetry.delivery,
        Distributed.Recall.Information.Agency.externalChoice, stepLocal, Code.step]
      cases lookup : (EventStep.seed cursor).frame.sent[serial]? with
      | none => simp only [List.length_nil, Nat.zero_le]
      | some packet =>
        simp only [List.nil_append]
        exact QueueBirthSource.every_actual_recipient_cost_is_in_the_source_envelope (code := code) packet.recipient

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem an_actual_silent_window_has_no_births (cursor : Cursor model.source.code) (count : Nat) :
    BirthWindow.births model cursor (SilentWindow.stages count) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [SilentWindow.stages, BirthWindow.actual_append_has_exact_additive_births, ih, Nat.zero_add]
    apply BirthWindow.an_actual_empty_word_has_no_births
    rw [(StageTrace.material_is_the_actual_step _ SilentWindow.quiet SilentWindow.environment).2]
    simp only [word, SilentWindow.no_admitted_event]

variable (start : Cursor model.source.code) (past : JointResponse.Stages model)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev tail (answer : TimedRetry.Ready start past vocabulary encoding law) : JointResponse.Stages model :=
  SilentWindow.stages (TimedRetry.waiting start past vocabulary encoding law answer.overdue) ++
    [(TimedRetry.sending answer.overdue.emission.wire.ballot.key answer.overdue.emission.wire.recipient answer.supported,
      SilentWindow.environment)] ++ [(SilentWindow.quiet, TimedRetry.delivery answer.wire.serial answer.deliverable)]

theorem the_retry_tail_is_the_literal_actual_extension (answer : TimedRetry.Ready start past vocabulary encoding law) :
    past ++ tail model start past vocabulary encoding law answer = answer.stages := by
  simp only [tail, TimedRetry.Ready.stages, TimedRetry.completed, TimedRetry.sent, TimedRetry.aligned, List.append_assoc]

theorem every_actual_retry_funds_all_its_open_births_from_source_cost_words
    (answer : TimedRetry.Ready start past vocabulary encoding law) :
    BirthWindow.births model (EventHistory.execute start past) (tail model start past vocabulary encoding law answer) ≤
      allowance model.source.code := by
  rw [tail, BirthWindow.actual_append_has_exact_additive_births,
    BirthWindow.actual_append_has_exact_additive_births, an_actual_silent_window_has_no_births, Nat.zero_add]
  apply Nat.add_le_add
  · exact (BirthWindow.actual_single_visit_births_are_paid_by_its_original_word model _ _ _).trans
      (an_actual_send_stage_submits_at_most_its_source_cost _ answer.overdue.emission.wire.ballot.key
        answer.overdue.emission.wire.recipient answer.supported)
  · exact (BirthWindow.actual_single_visit_births_are_paid_by_its_original_word model _ _ _).trans
      (an_actual_fixed_delivery_submits_at_most_its_source_cost _ answer.wire.serial answer.deliverable)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryBirthCost

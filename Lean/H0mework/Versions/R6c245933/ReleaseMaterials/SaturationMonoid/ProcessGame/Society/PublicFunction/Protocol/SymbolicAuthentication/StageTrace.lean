import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistoryRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlResponsibility

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageTrace

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def capture (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (before : Feedback.State code) : ControlExecution.Call code :=
  if before.remaining = 0 then .stopped
  else match Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart before.history.length with
    | some site => .own site (localEvent code protocol site (before.frame.inbox site))
    | none => .external (rival before.history before.past before.frame)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem captured_admission_is_the_actual_decision (cursor : Cursor code) (protocol : Rule code)
    (rival : Opponent code) (before : Feedback.State code) :
    ControlExecution.admitted code (capture cursor protocol rival before) =
      decision code (EventStep.applied cursor protocol rival) before := by
  unfold capture
  split_ifs with stopped
  · simp only [ControlExecution.admitted, decision, stopped, if_true]
  · simp only [decision, if_neg stopped, Cursor.controller, driver]
    cases Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart before.history.length <;> rfl

structure Record where
  cursor : Cursor code
  protocol : Rule code
  before : Feedback.State code
  call : ControlExecution.Call code
  submitted : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  after : Feedback.State code

def material (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) : Record (code := code) :=
  let before := EventStep.seed cursor
  let call := capture cursor protocol rival before
  let selected : Input code := ⟨fun _ _ _ => ControlExecution.admitted code call, cursor.entry.budget⟩
  ⟨cursor, protocol, before, call, word code (some protocol.work.val) selected before,
    Reaction.Feedback.advance code (some protocol.work.val) selected before⟩

private theorem selected_decision (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) :
    decision code ⟨fun _ _ _ => ControlExecution.admitted code (capture cursor protocol rival (EventStep.seed cursor)), cursor.entry.budget⟩
        (EventStep.seed cursor) = decision code (EventStep.applied cursor protocol rival) (EventStep.seed cursor) := by
  by_cases stopped : (EventStep.seed cursor).remaining = 0
  · simp only [decision, stopped, if_true]
  · simpa only [decision, if_neg stopped] using captured_admission_is_the_actual_decision cursor protocol rival (EventStep.seed cursor)

theorem material_is_the_actual_step (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) :
    (material cursor protocol rival).after = EventStep.seed (cursor.after protocol rival) ∧
      (material cursor protocol rival).submitted = word code (some protocol.work.val)
        (EventStep.applied cursor protocol rival) (EventStep.seed cursor) := by
  rw [EventStep.actual_next_state]
  constructor <;> simp only [material, Reaction.Feedback.advance, word, selected_decision]

def records (cursor : Cursor code) : List (EventHistory.Stage (code := code)) → List (Record (code := code))
  | [] => []
  | (protocol, rival) :: tail => material cursor protocol rival :: records (cursor.after protocol rival) tail

theorem record_count (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    (records cursor stages).length = stages.length := by
  induction stages generalizing cursor with
  | nil => rfl
  | cons stage tail ih => simp only [records, List.length_cons, ih]

theorem no_occurrence_is_lost_or_duplicated (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    (records cursor stages).map (fun row => row.cursor.cut) = (List.range stages.length).map (cursor.cut + ·) := by
  induction stages generalizing cursor with
  | nil => rfl
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    simp only [records, List.map_cons, material, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro n _
    change cursor.cut + 1 + n = cursor.cut + (n + 1)
    omega

private theorem prior_currents (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (ordinal : Nat) (bounded : ordinal ≤ EventStep.boundary cursor) :
    (cursor.after protocol rival).source.currentAt ordinal = cursor.source.currentAt ordinal := by
  have same := Machine.actual_prefix_from_events cursor.source.input (Cursor.target cursor protocol rival).input
    rfl rfl (EventStep.boundary cursor)
    (Future.prior_raw_event cursor.source cursor.entry cursor.cut (Cursor.controller cursor protocol rival)
      (term cursor.source cursor.entry cursor.cut protocol).val rfl) ordinal bounded
  unfold Machine.currentAt
  change ProgrammeSource.rawCurrent (Cursor.target cursor protocol rival).input
    (ProgrammeHistory.visitAt (Cursor.target cursor protocol rival).input ordinal).current = _
  rw [same]
  rfl

private theorem prior_words (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (ordinal : Nat) (bounded : ordinal < EventStep.boundary cursor) :
    ProgrammeSource.rawEvent (cursor.after protocol rival).source.input
        (ProgrammeHistory.visitAt (cursor.after protocol rival).source.input ordinal).current =
      ProgrammeSource.rawEvent cursor.source.input (ProgrammeHistory.visitAt cursor.source.input ordinal).current :=
  (Native.Coupling.History.occurrences cursor.source.input (Cursor.target cursor protocol rival).input rfl rfl
    (EventStep.boundary cursor) (Future.prior_raw_event cursor.source cursor.entry cursor.cut
      (Cursor.controller cursor protocol rival) (term cursor.source cursor.entry cursor.cut protocol).val rfl) ordinal bounded).2

theorem final_preserves_the_complete_past (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    (∀ ordinal, ordinal ≤ EventStep.boundary cursor →
      (EventHistory.execute cursor stages).source.currentAt ordinal = cursor.source.currentAt ordinal) ∧
    (∀ ordinal, ordinal < EventStep.boundary cursor →
      ProgrammeSource.rawEvent (EventHistory.execute cursor stages).source.input
          (ProgrammeHistory.visitAt (EventHistory.execute cursor stages).source.input ordinal).current =
        ProgrammeSource.rawEvent cursor.source.input (ProgrammeHistory.visitAt cursor.source.input ordinal).current) := by
  induction stages generalizing cursor with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    obtain ⟨currents, words⟩ := ih (cursor.after protocol rival)
    have boundary : EventStep.boundary (cursor.after protocol rival) = EventStep.boundary cursor + 1 := by rfl
    refine ⟨?_, ?_⟩
    · intro ordinal bounded
      exact (currents ordinal (by rw [boundary]; omega)).trans (prior_currents cursor protocol rival ordinal bounded)
    · intro ordinal bounded
      exact (words ordinal (by rw [boundary]; omega)).trans (prior_words cursor protocol rival ordinal bounded)

theorem every_record_is_a_completed_occurrence_of_the_final_source
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (row : Record (code := code)) (inside : row ∈ records cursor stages) :
    row.before.current = (EventHistory.execute cursor stages).source.currentAt (EventStep.boundary row.cursor) ∧
      row.submitted = ProgrammeSource.rawEvent (EventHistory.execute cursor stages).source.input
        (ProgrammeHistory.visitAt (EventHistory.execute cursor stages).source.input (EventStep.boundary row.cursor)).current ∧
      row.after.current = (EventHistory.execute cursor stages).source.currentAt (EventStep.boundary row.cursor + 1) ∧
      row.after.current = code.law.next row.before.current row.submitted := by
  induction stages generalizing cursor with
  | nil => simp [records] at inside
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    rcases List.mem_cons.mp inside with same | later
    · subst row
      have origin := material_is_the_actual_step cursor protocol rival
      obtain ⟨currents, words⟩ := final_preserves_the_complete_past (cursor.after protocol rival) tail
      have boundary : EventStep.boundary (cursor.after protocol rival) = EventStep.boundary cursor + 1 := by rfl
      have before := (cursor.after protocol rival).source.feedback_current_is_actual
        (cursor.after protocol rival).entry rfl rfl cursor.cut
      change (Cursor.target cursor protocol rival).currentAt (EventStep.boundary cursor) =
        ((Cursor.target cursor protocol rival).feedbackState (Cursor.targetInput cursor protocol rival) cursor.cut).current at before
      rw [Future.complete_state_before _ _ _ _ _ cursor.cut (Nat.le_refl _)] at before
      have after := (cursor.after protocol rival).source.feedback_current_is_actual
        (cursor.after protocol rival).entry rfl rfl (cursor.cut + 1)
      change (cursor.after protocol rival).source.currentAt (EventStep.boundary cursor + 1) =
        (EventStep.seed (cursor.after protocol rival)).current at after
      refine ⟨?_, ?_, ?_, rfl⟩
      · exact before.symm.trans (currents (EventStep.boundary cursor) (by rw [boundary]; omega)).symm
      · exact origin.2.trans ((EventStep.actual_next_word cursor protocol rival).symm.trans
          (words _ (by rw [boundary]; omega)).symm)
      · exact (congrArg (fun state : Feedback.State code => state.current) origin.1).trans
          (after.symm.trans (currents (EventStep.boundary cursor + 1) (by rw [boundary])).symm)
    · exact ih (cursor.after protocol rival) later

def items (row : Record (code := code)) := code.law.rawItems row.before.current row.submitted
def audit (row : Record (code := code)) := (items row).map fun item => (item, decide (code.law.Valid item.before item.request))

omit [DecidableEq Port] [DecidableEq Technology] in
theorem audit_retains_every_request_and_its_actual_validity (row : Record (code := code)) :
    (audit row).map (fun entry => entry.1.request) = row.submitted ∧
      ∀ entry ∈ audit row, entry.2 = true ↔ code.law.Valid entry.1.before entry.1.request := by
  constructor
  · simpa only [audit, items, List.map_map, Function.comp_def, RawLaw.rawItems] using
      code.law.inventory_requests_exact row.before.current 0 row.submitted
  · intro entry inside
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp inside
    simp only [decide_eq_true_eq]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem rejected_request_has_no_material_or_financial_debit
    (row : Record (code := code)) (entry : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool)
    (inside : entry ∈ audit row) (rejected : entry.2 = false) :
    code.law.step entry.1.before entry.1.request = entry.1.before ∧
      code.law.actualDebit entry.1.before entry.1.request = [] ∧ code.law.actualCredit entry.1.before entry.1.request = [] := by
  have invalid : ¬ code.law.Valid entry.1.before entry.1.request := by
    intro valid
    have yes := ((audit_retains_every_request_and_its_actual_validity row).2 entry inside).mpr valid
    rw [rejected] at yes
    contradiction
  simp [RawLaw.step, RawLaw.actualDebit, RawLaw.actualCredit, invalid]

theorem suppressed_callback_cannot_create_work_or_packets
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (refused : ControlExecution.suppressed code (material cursor protocol rival).call = true) :
    (material cursor protocol rival).submitted = [] ∧
      (material cursor protocol rival).after.frame = (material cursor protocol rival).before.frame ∧
      (material cursor protocol rival).after.past = (material cursor protocol rival).before.past ∧
      (material cursor protocol rival).after.current = code.law.next (material cursor protocol rival).before.current [] := by
  have noAdmission : ControlExecution.admitted code (material cursor protocol rival).call = none := by
    generalize (material cursor protocol rival).call = call at refused ⊢
    cases call with
    | stopped => cases refused
    | inherited attempt => cases refused
    | own site attempt => cases refused
    | external attempt =>
      cases attempt with
      | none => cases refused
      | some event =>
        rcases event with ⟨event, supported⟩
        cases event <;> simp_all [ControlExecution.suppressed, ControlExecution.admitted, Distributed.Recall.Information.Agency.externalChoice]
  change ControlExecution.admitted code (capture cursor protocol rival (EventStep.seed cursor)) = none at noAdmission
  simp only [material, Reaction.Feedback.advance, word, decision, noAdmission, ite_self]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem every_record_retains_its_actual_stage
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (row : Record (code := code)) (inside : row ∈ records cursor stages) :
    ∃ pastStages protocol rival suffix, stages = pastStages ++ (protocol, rival) :: suffix ∧
      row = material (EventHistory.execute cursor pastStages) protocol rival := by
  induction stages generalizing cursor with
  | nil => simp [records] at inside
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    rcases List.mem_cons.mp inside with same | later
    · exact ⟨[], protocol, rival, tail, rfl, same⟩
    · obtain ⟨pastStages, next, other, suffix, shape, actual⟩ := ih (cursor.after protocol rival) later
      exact ⟨(protocol, rival) :: pastStages, next, other, suffix, by rw [shape]; rfl, actual⟩

theorem the_live_work_policy_is_installed_in_the_actual_source
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (live : (EventStep.seed cursor).remaining ≠ 0) :
    (cursor.after protocol rival).source.feedbackPolicy cursor.cut = some protocol.work.val := by
  change (Cursor.target cursor protocol rival).feedbackPolicy (cursor.cut + 0) = _
  rw [Execution.policy_at]
  have positive : 0 < (EventStep.seed cursor).remaining := by omega
  simp [Residual.scheduleAt, term, positive]

def activation (row : Record (code := code)) : Option (Fin code.sites) :=
  match row.call with
  | .own site (some event) => if event.val = .activate site then some site else none
  | _ => none

theorem an_owned_activation_submits_its_selected_work
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) (site : Fin code.sites)
    (owned : activation (material cursor protocol rival) = some site) :
    (material cursor protocol rival).before.remaining ≠ 0 ∧
      (material cursor protocol rival).submitted = code.action protocol.work.val site ((EventStep.seed cursor).frame.inbox site) := by
  change (match capture cursor protocol rival (EventStep.seed cursor) with
    | .own worker (some event) => if event.val = .activate worker then some worker else none
    | _ => none) = some site at owned
  by_cases live : (EventStep.seed cursor).remaining = 0
  · simp only [capture, if_pos live] at owned
    contradiction
  · simp only [capture, if_neg live] at owned
    cases owner : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
    | none => simp only [owner] at owned; contradiction
    | some worker =>
      simp only [owner] at owned
      cases chosen : localEvent code protocol worker ((EventStep.seed cursor).frame.inbox worker) with
      | none => simp only [chosen] at owned; contradiction
      | some event =>
        simp only [chosen] at owned
        split_ifs at owned with activated
        · have same := Option.some.inj owned
          subst site
          refine ⟨live, ?_⟩
          change word code (some protocol.work.val) _ (EventStep.seed cursor) = _
          simp only [word, decision, capture, ControlExecution.admitted, owner, chosen, if_neg live]
          rw [activated]
          rfl

theorem external_callback_is_retained_before_admission
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) (attempt : Move code)
    (external : (material cursor protocol rival).call = .external attempt) :
    (EventStep.seed cursor).remaining ≠ 0 ∧
      Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length = none ∧
      rival (EventStep.seed cursor).history (EventStep.seed cursor).past (EventStep.seed cursor).frame = attempt := by
  change capture cursor protocol rival (EventStep.seed cursor) = .external attempt at external
  unfold capture at external
  split at external <;> try contradiction
  rename_i live
  split at external <;> try contradiction
  rename_i owner
  exact ⟨live, owner, ControlExecution.CallData.external.inj external⟩

theorem final_financial_inventory_is_the_original_record_items
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (row : Record (code := code)) (inside : row ∈ records cursor stages) :
    (Financial.inventoryAt (EventHistory.execute cursor stages).source.input
      (ProgrammeHistory.visitAt (EventHistory.execute cursor stages).source.input (EventStep.boundary row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (EventHistory.execute cursor stages).source.input) = items row := by
  have same := every_record_is_a_completed_occurrence_of_the_final_source cursor stages row inside
  rw [show EventStep.boundary row.cursor = (row.cursor.source.history.length + 1 + row.cursor.cut) + 1 by
    dsimp [EventStep.boundary]; omega]
  rw [Native.both_consumers_use_the_same_actual_word]
  change code.law.rawItems
    ((EventHistory.execute cursor stages).source.currentAt ((row.cursor.source.history.length + 1 + row.cursor.cut) + 1))
    (ProgrammeSource.rawEvent (EventHistory.execute cursor stages).source.input
      (ProgrammeHistory.visitAt (EventHistory.execute cursor stages).source.input
        ((row.cursor.source.history.length + 1 + row.cursor.cut) + 1)).current) = _
  rw [show (row.cursor.source.history.length + 1 + row.cursor.cut) + 1 = EventStep.boundary row.cursor by
    dsimp [EventStep.boundary]; omega]
  rw [← same.1, ← same.2.1]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageTrace

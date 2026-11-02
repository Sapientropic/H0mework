import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Recovery

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def legal (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : Bool :=
  (List.range (Cut.horizon point.source point.entry point.cut)).all fun offset =>
    let actual := (point.target rule rival).actualExecution (depth point+offset)
    decide (Open.Legal code.law actual.before actual.submitted)

theorem legal_iff (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : legal point rule rival = true ↔
    ∀ offset < Cut.horizon point.source point.entry point.cut,
      let actual := (point.target rule rival).actualExecution (depth point+offset)
      Open.Legal code.law actual.before actual.submitted := by
  simp only [legal,List.all_eq_true,List.mem_range,decide_eq_true_eq]

private theorem finite_keeps_raw_execution (point : Cursor code)
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code) (ordinal : Nat) :
    let left := (point.target rule (finiteRival point rival)).actualExecution ordinal
    let right := (point.target rule rival).actualExecution ordinal
    left.before = right.before ∧ left.submitted = right.submitted := by
  have states := Machine.actual_prefix_from_events (point.target rule rival).input
    (point.target rule (finiteRival point rival)).input rfl rfl (ordinal+1)
    (fun index _ => one_external_table_preserves_every_raw_occurrence point rule rival index)
    (ordinal+1) (Nat.le_refl _)
  have current : (point.target rule (finiteRival point rival)).currentAt (ordinal+1) =
      (point.target rule rival).currentAt (ordinal+1) := by
    change ProgrammeSource.rawCurrent _ _ = ProgrammeSource.rawCurrent _ _
    rw [states]
    cases (ProgrammeHistory.visitAt (point.target rule rival).input (ordinal+1)).current <;> rfl
  constructor
  · exact current
  · rw [Machine.actual_word,Machine.actual_word,current]
    have words := one_external_table_preserves_every_raw_occurrence point rule rival (ordinal+1)
    cases actual : (ProgrammeHistory.visitAt (point.target rule rival).input (ordinal+1)).current with
    | bootstrap =>
        have rounds := ProgrammeHistory.visit_round (point.target rule rival).input (ordinal+1)
        rw [actual] at rounds
        change code.initial.round = code.initial.round+(ordinal+1) at rounds
        omega
    | running raw history =>
        rw [actual] at words
        change (point.target rule (finiteRival point rival)).body raw = (point.target rule rival).body raw at words
        simpa only [Machine.currentAt,actual,ProgrammeSource.rawCurrent] using words

theorem one_common_external_table_preserves_all_new_raw_legality
    (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : legal point rule (finiteRival point rival) = legal point rule rival := by
  apply List.all_congr rfl
  intro offset
  have raw := finite_keeps_raw_execution point rule rival (depth point+offset)
  dsimp only
  rw [raw.1,raw.2]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (rival : Opponent model.source.code)

/-- The immutable old execution supplies every responsibility field. Only the
legality of the newly submitted window is read from its own raw law checks. -/
def evaluate : Evaluation model.source.code :=
  {Replanning.actualEvaluation model point rule rival with legal := legal point rule rival}

theorem all_other_original_responsibility_fields_are_unchanged :
    (evaluate model point rule rival).complete = (Replanning.actualEvaluation model point rule rival).complete ∧
    (evaluate model point rule rival).profile = (Replanning.actualEvaluation model point rule rival).profile ∧
    (evaluate model point rule rival).native = (Replanning.actualEvaluation model point rule rival).native ∧
    (evaluate model point rule rival).value = (Replanning.actualEvaluation model point rule rival).value :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem a_shared_table_preserves_the_entire_window_evaluation :
    evaluate model point rule (finiteRival point rival) = evaluate model point rule rival := by
  have original : Replanning.actualEvaluation model point rule (finiteRival point rival) =
      Replanning.actualEvaluation model point rule rival :=
    (Replanning.table_evaluation_is_its_own_actual_protocol model point rule (externalTable point rival)).symm.trans
      (Replanning.one_external_table_preserves_every_actual_full_responsibility model point rule rival)
  unfold evaluate
  rw [original,one_common_external_table_preserves_all_new_raw_legality]

theorem a_source_proved_quiet_domain_has_one_actual_full_evaluation
    (quiet : PublicDomain.quiet (code := model.source.code) = true) :
    evaluate model point rule rival = evaluate model point rule PublicDomain.silent := by
  have same := PublicDomain.quiet_controllers_are_identical quiet point rule rival
  unfold evaluate legal Replanning.actualEvaluation Cursor.target
  rw [same]

variable {rule rival}

theorem finite_relation_iff_the_same_full_adaptive_opponent
    (relation : Evaluation model.source.code → Evaluation model.source.code → Prop)
    (new old : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    (∀ table ∈ Cut.tables point.source point.entry point.cut,
      relation (evaluate model point new (Cut.opponent point.source point.entry point.cut table))
        (evaluate model point old (Cut.opponent point.source point.entry point.cut table))) ↔
    ∀ rival : Opponent model.source.code, relation (evaluate model point new rival) (evaluate model point old rival) := by
  constructor
  · intro finite rival
    have checked := finite (externalTable point rival) (Residual.restriction_is_generated _ _ _ rival)
    rw [show Cut.opponent point.source point.entry point.cut (externalTable point rival) = finiteRival point rival from rfl,
      a_shared_table_preserves_the_entire_window_evaluation,a_shared_table_preserves_the_entire_window_evaluation] at checked
    exact checked
  · intro all table _
    exact all _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Complete

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev Program := @Continuation.Whole.Program
abbrev programs := @Continuation.Whole.programs
abbrev baseline := @Continuation.Whole.baseline
abbrev controller := @Continuation.Whole.controller
abbrev schedule := @Continuation.Whole.schedule
abbrev source := @Continuation.Whole.source
abbrev entry := @Continuation.Whole.entry
abbrev clip := @Continuation.Whole.Complete.clip
abbrev horizon := @Continuation.Whole.Complete.horizon
abbrev every_bounded_program_is_source_generated := @Continuation.Whole.every_bounded_program_is_source_generated

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel otherFuel : Nat}

def rawLegal (point : Cursor code) (driver : Opponent code)
    (term : Cut.Term point.source point.entry point.cut) : Bool :=
  (List.range (Cut.horizon point.source point.entry point.cut)).all fun offset =>
    let actual := (Future.target point.source point.entry point.cut driver term.val).actualExecution (depth point+offset)
    decide (Open.Legal code.law actual.before actual.submitted)

theorem rawLegal_iff (point : Cursor code) (driver : Opponent code)
    (term : Cut.Term point.source point.entry point.cut) : rawLegal point driver term = true ↔
    ∀ offset < Cut.horizon point.source point.entry point.cut,
      let actual := (Future.target point.source point.entry point.cut driver term.val).actualExecution (depth point+offset)
      Open.Legal code.law actual.before actual.submitted := by
  simp only [rawLegal,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem joint_keeps_raw_legality (point : Cursor code) (driver : Opponent code)
    (term : Cut.Term point.source point.entry point.cut) :
    rawLegal point (Future.jointOpponent point.source point.entry point.cut driver) term = rawLegal point driver term := by
  apply Bool.eq_iff_iff.mpr
  simp only [rawLegal,List.all_eq_true,List.mem_range]
  apply forall_congr'
  intro offset
  apply forall_congr'
  intro inside
  have bounded : depth point+offset+1 < point.source.history.length+2+point.cut+(Residual.seed point.source point.entry point.cut).remaining := by
    change offset < (Residual.seed point.source point.entry point.cut).remaining at inside
    dsimp only [depth]
    omega
  have current := Future.joint_current point.source point.entry point.cut driver term.val rfl rfl term.property
    (depth point+offset+1) (Nat.le_of_lt bounded)
  have occurrences := Future.joint_occurrences point.source point.entry point.cut driver term.val rfl rfl term.property
    (depth point+offset+1) bounded
  have words := occurrences.2
  rw [occurrences.1] at words
  have before : ((Future.target point.source point.entry point.cut (Future.jointOpponent point.source point.entry point.cut driver) term.val).actualExecution (depth point+offset)).before =
      ((Future.target point.source point.entry point.cut driver term.val).actualExecution (depth point+offset)).before := current
  have submitted : ((Future.target point.source point.entry point.cut (Future.jointOpponent point.source point.entry point.cut driver) term.val).actualExecution (depth point+offset)).submitted =
      ((Future.target point.source point.entry point.cut driver term.val).actualExecution (depth point+offset)).submitted := by
    rw [Machine.actual_word,Machine.actual_word,current]
    cases view : (ProgrammeHistory.visitAt (Future.target point.source point.entry point.cut driver term.val).input (depth point+offset+1)).current with
    | bootstrap =>
        have rounds := ProgrammeHistory.visit_round (Future.target point.source point.entry point.cut driver term.val).input (depth point+offset+1)
        rw [view] at rounds
        change code.initial.round = code.initial.round+(depth point+offset+1) at rounds
        omega
    | running raw past =>
        rw [view] at words
        change (Future.target point.source point.entry point.cut (Future.jointOpponent point.source point.entry point.cut driver) term.val).body raw =
          (Future.target point.source point.entry point.cut driver term.val).body raw at words
        simpa only [Machine.currentAt,view,ProgrammeSource.rawCurrent] using words
  rw [before,submitted]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code)

def evaluate (driver : Opponent model.source.code) (term : Cut.Term point.source point.entry point.cut) : Evaluation model.source.code :=
  { Distributed.Recall.Information.Agency.Protocol.evaluate (Replanning.native model point) point.entry point.cut rfl driver term with legal := rawLegal point driver term }

theorem evaluate_joint (driver : Opponent model.source.code) (term : Cut.Term point.source point.entry point.cut) :
    evaluate model point (Future.jointOpponent point.source point.entry point.cut driver) term = evaluate model point driver term := by
  unfold evaluate
  rw [Distributed.Recall.Information.Agency.Protocol.evaluate_joint (Replanning.native model point) point.entry point.cut rfl rfl,
    joint_keeps_raw_legality]

variable (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (program : Program model.source.code fuel)

abbrev actualEvaluation (rival : Opponent model.source.code) :=
  evaluate model point (controller point original program rival) (schedule point original program)

abbrev tableEvaluation (table : Cut.Table point.source point.entry point.cut) :=
  actualEvaluation model point original program (Cut.opponent point.source point.entry point.cut table)

theorem every_original_responsibility_field_is_preserved (rival : Opponent model.source.code) :
    (actualEvaluation model point original program rival).complete = (Continuation.Whole.actualEvaluation model point original program rival).complete ∧
    (actualEvaluation model point original program rival).profile = (Continuation.Whole.actualEvaluation model point original program rival).profile ∧
    (actualEvaluation model point original program rival).native = (Continuation.Whole.actualEvaluation model point original program rival).native ∧
    (actualEvaluation model point original program rival).value = (Continuation.Whole.actualEvaluation model point original program rival).value := ⟨rfl,rfl,rfl,rfl⟩

theorem quiet_controllers (quiet : PublicDomain.quiet (code := model.source.code) = true)
    (rival : Opponent model.source.code) :
    controller point original program rival = controller point original program PublicDomain.silent := by
  funext history past frame
  exact congrFun (congrFun (congrFun (PublicDomain.quiet_controllers_are_identical quiet point
    (program.at original (history.length-(point.history.length+1+point.cut))) rival) history) past) frame

theorem quiet_evaluation (quiet : PublicDomain.quiet (code := model.source.code) = true)
    (rival : Opponent model.source.code) :
    actualEvaluation model point original program rival = actualEvaluation model point original program PublicDomain.silent := by
  unfold actualEvaluation
  rw [quiet_controllers model point original program quiet rival]

theorem one_common_table_preserves_the_entire_actual_evaluation (rival : Opponent model.source.code) :
    tableEvaluation model point original program (externalTable point rival) = actualEvaluation model point original program rival := by
  change evaluate model point (controller point original program (finiteRival point rival)) (schedule point original program) =
    evaluate model point (controller point original program rival) (schedule point original program)
  calc
    _ = evaluate model point (Continuation.Whole.tableController model point original program (externalTable point rival)) (schedule point original program) :=
      (evaluate_joint model point (controller point original program (finiteRival point rival)) _).symm
    _ = evaluate model point (Future.jointOpponent point.source point.entry point.cut (controller point original program rival)) (schedule point original program) :=
      congrArg (fun driver => evaluate model point driver (schedule point original program))
        (Continuation.Whole.one_external_restriction_controls_the_entire_program model point original program rival)
    _ = _ := evaluate_joint model point (controller point original program rival) _

theorem finite_relation_iff_the_same_full_adaptive_opponent
    (relation : Evaluation model.source.code → Evaluation model.source.code → Prop)
    (new old : Program model.source.code fuel) :
    (∀ table ∈ Cut.tables point.source point.entry point.cut,
      relation (tableEvaluation model point original new table) (tableEvaluation model point original old table)) ↔
      ∀ rival : Opponent model.source.code,
        relation (actualEvaluation model point original new rival) (actualEvaluation model point original old rival) := by
  constructor
  · intro finite rival
    have checked := finite (externalTable point rival) (Residual.restriction_is_generated _ _ _ rival)
    rw [one_common_table_preserves_the_entire_actual_evaluation,one_common_table_preserves_the_entire_actual_evaluation] at checked
    exact checked
  · intro all table _
    exact all _

theorem stages_generate_the_same_complete_evaluation (second : Program model.source.code otherFuel)
    (stages : ∀ ordinal < Cut.horizon point.source point.entry point.cut,
      program.at original ordinal = second.at original ordinal) (rival : Opponent model.source.code) :
    actualEvaluation model point original program rival = actualEvaluation model point original second rival := by
  have terms : (schedule point original program).val = (schedule point original second).val := by
    apply List.map_congr_left
    intro ordinal inside
    rw [stages ordinal (List.mem_range.mp inside)]
  have tables : Continuation.Whole.tableController model point original program (externalTable point rival) =
      Continuation.Whole.tableController model point original second (externalTable point rival) := by
    funext history past frame
    change (if member : (history,past,frame) ∈ Residual.keys model.source.code
        (Residual.seed point.source point.entry point.cut) (Residual.schedules point.source point.entry point.cut)
      then controller point original program (finiteRival point rival) history past frame else none) = _
    by_cases member : (history,past,frame) ∈ Residual.keys model.source.code
        (Residual.seed point.source point.entry point.cut) (Residual.schedules point.source point.entry point.cut)
    · simp only [Continuation.Whole.tableController,Future.jointOpponent,Residual.respond,Residual.restrict,dif_pos member,controller,
        Continuation.Whole.controller,stages _ (Continuation.Whole.Complete.every_registered_decision_has_a_consumed_stage point _ member)]
    · simp only [Continuation.Whole.tableController,Future.jointOpponent,Residual.respond,dif_neg member]
  calc
    actualEvaluation model point original program rival =
        evaluate model point (Continuation.Whole.tableController model point original program (externalTable point rival))
          (schedule point original program) := by
      exact ((evaluate_joint model point (controller point original program (finiteRival point rival)) _).trans
        (one_common_table_preserves_the_entire_actual_evaluation model point original program rival)).symm
    _ = evaluate model point (Continuation.Whole.tableController model point original second (externalTable point rival))
          (schedule point original second) := by
      rw [tables,show schedule point original program = schedule point original second from Subtype.ext terms]
    _ = actualEvaluation model point original second rival :=
      (evaluate_joint model point (controller point original second (finiteRival point rival)) _).trans
        (one_common_table_preserves_the_entire_actual_evaluation model point original second rival)

theorem clipping_preserves_the_whole_table_evaluation (domain : List (Cursor model.source.code))
    (inside : point ∈ domain) (enough : horizon domain ≤ otherFuel)
    (table : Cut.Table point.source point.entry point.cut) :
    tableEvaluation model point original (clip otherFuel program) table = tableEvaluation model point original program table := by
  apply stages_generate_the_same_complete_evaluation
  intro ordinal consumed
  exact Continuation.Whole.Complete.clipping_keeps_each_consumed_stage otherFuel program original ordinal
    (consumed.trans_le ((Continuation.Whole.Complete.each_remaining_horizon_is_generated domain point inside).trans enough))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

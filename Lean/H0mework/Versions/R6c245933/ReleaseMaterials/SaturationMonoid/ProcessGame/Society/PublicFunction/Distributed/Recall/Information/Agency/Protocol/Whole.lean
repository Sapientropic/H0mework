import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Replanning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument) (fuel : Nat)

structure Program where
  controls : List (Rule code)
  bounded : controls.length ≤ fuel

def programs : List (Program code fuel) :=
  (sequences (rules code) fuel).attach.map fun controls =>
    ⟨controls.val,((mem_sequences_iff _ _ _).mp controls.property).1⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_bounded_program_is_source_generated (program : Program code fuel) : program ∈ programs code fuel := by
  have inside : program.controls ∈ sequences (rules code) fuel :=
    (mem_sequences_iff _ _ _).mpr ⟨program.bounded,fun rule _ => every_rule_is_source_generated code rule⟩
  exact List.mem_map.mpr ⟨⟨program.controls,inside⟩,List.mem_attach _ _,by cases program;rfl⟩

def baseline : Program code fuel := ⟨[],Nat.zero_le _⟩

variable {code fuel}

/-- After the finite prefix, the last installed rule continues; an empty prefix uses the reference. -/
def Program.at (program : Program code fuel) (reference : Rule code) (ordinal : Nat) : Rule code :=
  (program.controls[ordinal]?).getD (program.controls.getLast?.getD reference)

variable (point : Cursor code) (reference : Rule code) (program : Program code fuel)

/-- Stages count feedback cuts, including environment turns; ownership retains its original clock. -/
def controller (rival : Opponent code) : Opponent code :=
  fun history past frame => driver code point.ownerStart
    (program.at reference (history.length-(point.history.length+1+point.cut))) rival history past frame

omit [DecidableEq Port] [DecidableEq Technology] in
theorem own_control_reads_only_its_stage_and_local_record
    (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : ownerAt code point.ownerStart history.length = some site)
    (same : left.inbox site = right.inbox site) :
    controller point reference program first history past left = controller point reference program second history past right :=
  own_action_uses_only_its_actual_local_record code point.ownerStart _ first second history past left right site owned same

def schedule : Cut.Term point.source point.entry point.cut := by
  refine ⟨(List.range (Cut.horizon point.source point.entry point.cut)).map
    (fun ordinal => some (program.at reference ordinal).work.val),?_⟩
  apply (mem_sequences_iff _ _ _).mpr
  refine ⟨by simp,?_⟩
  intro control inside
  obtain ⟨ordinal,_,same⟩ := List.mem_map.mp inside
  subst control
  exact List.mem_append_right _ (List.mem_map.mpr
    ⟨(program.at reference ordinal).work.val,(program.at reference ordinal).work.property,rfl⟩)

abbrev source (rival : Opponent code) :=
  Future.target point.source point.entry point.cut (controller point reference program rival) (schedule point reference program).val
abbrev entry (rival : Opponent code) := Future.takeover point.source point.entry point.cut (controller point reference program rival)

theorem each_work_stage_is_actually_installed (ordinal : Nat)
    (inside : ordinal < Cut.horizon point.source point.entry point.cut) (rival : Opponent code) :
    (source point reference program rival).feedbackPolicy (point.cut+ordinal) =
      some (program.at reference ordinal).work.val := by
  rw [Execution.policy_at]
  simp only [Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

theorem the_complete_program_runs_in_its_own_actual_source (rival : Opponent code) (n : Nat) :
    (source point reference program rival).feedbackState (entry point reference program rival) (point.cut+n) =
      Residual.run code (Residual.scheduleAt point.source point.cut (schedule point reference program).val)
        ⟨controller point reference program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n :=
  Future.the_whole_future_run_is_the_actual_state point.source point.entry point.cut _ _ n

theorem every_old_actual_word_is_retained (rival : Opponent code) (ordinal : Nat)
    (earlier : ordinal < point.history.length+2+point.cut) :
    ProgrammeSource.rawEvent (source point reference program rival).input (ProgrammeHistory.visitAt point.source.input ordinal).current =
      ProgrammeSource.rawEvent point.source.input (ProgrammeHistory.visitAt point.source.input ordinal).current :=
  Future.prior_raw_event point.source point.entry point.cut _ _ rfl ordinal earlier

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (cursor : Cursor model.source.code) (original : Rule model.source.code) (candidate : Program model.source.code fuel)

abbrev actualEvaluation (rival : Opponent model.source.code) :=
  evaluate (Replanning.native model cursor) cursor.entry cursor.cut rfl
    (controller cursor original candidate rival) (schedule cursor original candidate)

abbrev tableController (table : Cut.Table cursor.source cursor.entry cursor.cut) :=
  Future.jointOpponent cursor.source cursor.entry cursor.cut
    (controller cursor original candidate (Cut.opponent cursor.source cursor.entry cursor.cut table))

abbrev tableEvaluation (table : Cut.Table cursor.source cursor.entry cursor.cut) :=
  evaluate (Replanning.native model cursor) cursor.entry cursor.cut rfl
    (tableController model cursor original candidate table) (schedule cursor original candidate)

theorem table_evaluation_is_its_own_actual_program (table : Cut.Table cursor.source cursor.entry cursor.cut) :
    tableEvaluation model cursor original candidate table =
      actualEvaluation model cursor original candidate (Cut.opponent cursor.source cursor.entry cursor.cut table) :=
  evaluate_joint (Replanning.native model cursor) cursor.entry cursor.cut rfl rfl _ _

theorem one_external_restriction_controls_the_entire_program (rival : Opponent model.source.code) :
    tableController model cursor original candidate (externalTable cursor rival) =
      Future.jointOpponent cursor.source cursor.entry cursor.cut (controller cursor original candidate rival) := by
  funext history past frame
  change (if member : (history,past,frame) ∈ Residual.keys model.source.code
      (Residual.seed cursor.source cursor.entry cursor.cut) (Residual.schedules cursor.source cursor.entry cursor.cut)
    then controller cursor original candidate (Cut.opponent cursor.source cursor.entry cursor.cut (externalTable cursor rival)) history past frame
    else none) = _
  by_cases member : (history,past,frame) ∈ Residual.keys model.source.code
      (Residual.seed cursor.source cursor.entry cursor.cut) (Residual.schedules cursor.source cursor.entry cursor.cut)
  · simp only [Future.jointOpponent,Residual.respond,Residual.restrict,dif_pos member,controller,driver]
  · simp only [Future.jointOpponent,Residual.respond,dif_neg member]

theorem one_common_external_table_preserves_the_entire_actual_evaluation (rival : Opponent model.source.code) :
    tableEvaluation model cursor original candidate (externalTable cursor rival) =
      actualEvaluation model cursor original candidate rival := by
  unfold tableEvaluation
  rw [one_external_restriction_controls_the_entire_program]
  exact evaluate_joint (Replanning.native model cursor) cursor.entry cursor.cut rfl rfl _ _

theorem finite_relation_iff_the_same_full_adaptive_opponent
    (relation : Evaluation model.source.code → Evaluation model.source.code → Prop)
    (new old : Program model.source.code fuel) :
    (∀ table ∈ Cut.tables cursor.source cursor.entry cursor.cut,
      relation (tableEvaluation model cursor original new table) (tableEvaluation model cursor original old table)) ↔
      ∀ rival : Opponent model.source.code,
        relation (actualEvaluation model cursor original new rival) (actualEvaluation model cursor original old rival) := by
  constructor
  · intro finite rival
    have checked := finite (externalTable cursor rival) (Residual.restriction_is_generated _ _ _ rival)
    rw [one_common_external_table_preserves_the_entire_actual_evaluation,one_common_external_table_preserves_the_entire_actual_evaluation] at checked
    exact checked
  · intro all table _
    rw [table_evaluation_is_its_own_actual_program,table_evaluation_is_its_own_actual_program]
    exact all _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole

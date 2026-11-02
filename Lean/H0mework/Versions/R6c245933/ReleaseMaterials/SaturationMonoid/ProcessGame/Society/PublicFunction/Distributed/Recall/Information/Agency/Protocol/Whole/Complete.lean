import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Complete

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel otherFuel : Nat}

def horizon : List (Cursor code) → Nat
  | [] => 0
  | point :: rest => max (Cut.horizon point.source point.entry point.cut) (horizon rest)

theorem each_remaining_horizon_is_generated (domain : List (Cursor code)) (point : Cursor code)
    (inside : point ∈ domain) : Cut.horizon point.source point.entry point.cut ≤ horizon domain := by
  induction domain with
  | nil => simp only [List.not_mem_nil] at inside
  | cons first rest ih =>
    rcases List.mem_cons.mp inside with same | member
    · subst point; exact Nat.le_max_left _ _
    · exact (ih member).trans (Nat.le_max_right _ _)

def clip (bound : Nat) (program : Program code fuel) : Program code bound :=
  ⟨program.controls.take bound,List.length_take_le _ _⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem clipping_keeps_each_consumed_stage (bound : Nat) (program : Program code fuel)
    (reference : Rule code) (ordinal : Nat) (inside : ordinal < bound) :
    (clip bound program).at reference ordinal = program.at reference ordinal := by
  by_cases short : program.controls.length ≤ bound
  · simp only [clip,Program.at,List.take_of_length_le short]
  · have present : ordinal < program.controls.length := by omega
    simp only [Program.at,clip,List.getElem?_take_of_lt inside,
      List.getElem?_eq_getElem present,Option.getD_some]

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem replay_history_length (schedule : Residual.Schedule code) (offset : Nat)
    (seed : State code) (moves : List (Move code)) :
    (Residual.replay code schedule offset seed moves).history.length = seed.history.length + moves.length := by
  induction moves generalizing offset seed with
  | nil => simp only [Residual.replay,List.length_nil,Nat.add_zero]
  | cons move rest ih =>
    rw [Residual.replay,ih]
    simp only [Residual.forced,history_keeps_every_actual_word,List.length_append,List.length_cons,List.length_nil]
    omega

private theorem feedback_history_length (point : Cursor code) (count : Nat) :
    (point.source.feedbackState point.entry count).history.length = point.history.length+1+count := by
  induction count with
  | zero => simp only [Machine.feedbackState,Machine.feedbackInitial,List.length_append,List.length_singleton,Nat.add_zero]
  | succ count ih =>
    change (Reaction.Feedback.advance code _ _ _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

theorem every_registered_decision_has_a_consumed_stage (point : Cursor code) (key : Key code)
    (inside : key ∈ Residual.keys code (Residual.seed point.source point.entry point.cut)
      (Residual.schedules point.source point.entry point.cut)) :
    key.1.length-(point.history.length+1+point.cut) < Cut.horizon point.source point.entry point.cut := by
  obtain ⟨schedule,_,member⟩ := List.mem_flatMap.mp (List.mem_dedup.mp inside)
  obtain ⟨moves,generated,same⟩ := List.mem_map.mp member
  have short := (List.mem_filter.mp generated).2
  have lengths := replay_history_length schedule 0 (Residual.seed point.source point.entry point.cut) moves
  rw [← same]
  dsimp only [Residual.key]
  rw [lengths,feedback_history_length]
  simpa only [Nat.add_sub_cancel_left,decide_eq_true_eq] using short

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (reference : Rule model.source.code)
  (first : Program model.source.code fuel) (second : Program model.source.code otherFuel)

theorem stages_generate_the_same_complete_evaluation
    (stages : ∀ ordinal < Cut.horizon point.source point.entry point.cut,
      first.at reference ordinal = second.at reference ordinal) (rival : Opponent model.source.code) :
    actualEvaluation model point reference first rival = actualEvaluation model point reference second rival := by
  have terms : (schedule point reference first).val = (schedule point reference second).val := by
    apply List.map_congr_left
    intro ordinal inside
    rw [stages ordinal (List.mem_range.mp inside)]
  have tables : tableController model point reference first (externalTable point rival) =
      tableController model point reference second (externalTable point rival) := by
    funext history past frame
    change (if member : (history,past,frame) ∈ Residual.keys model.source.code
        (Residual.seed point.source point.entry point.cut) (Residual.schedules point.source point.entry point.cut)
      then controller point reference first (Cut.opponent point.source point.entry point.cut (externalTable point rival)) history past frame else none) = _
    by_cases member : (history,past,frame) ∈ Residual.keys model.source.code
        (Residual.seed point.source point.entry point.cut) (Residual.schedules point.source point.entry point.cut)
    · simp only [tableController,Future.jointOpponent,Residual.respond,Residual.restrict,dif_pos member,controller,
        stages _ (every_registered_decision_has_a_consumed_stage point _ member)]
    · simp only [tableController,Future.jointOpponent,Residual.respond,dif_neg member]
  rw [← one_common_external_table_preserves_the_entire_actual_evaluation model point reference first rival,
    ← one_common_external_table_preserves_the_entire_actual_evaluation model point reference second rival]
  change evaluate _ _ _ _ _ _ = evaluate _ _ _ _ _ _
  rw [tables,show schedule point reference first = schedule point reference second from Subtype.ext terms]

theorem clipping_preserves_the_whole_actual_evaluation (domain : List (Cursor model.source.code))
    (inside : point ∈ domain) (enough : horizon domain ≤ otherFuel) (rival : Opponent model.source.code) :
    actualEvaluation model point reference (clip otherFuel first) rival = actualEvaluation model point reference first rival := by
  apply stages_generate_the_same_complete_evaluation
  intro ordinal consumed
  exact clipping_keeps_each_consumed_stage otherFuel first reference ordinal
    (consumed.trans_le ((each_remaining_horizon_is_generated domain point inside).trans enough))

theorem clipping_preserves_the_whole_table_evaluation (domain : List (Cursor model.source.code))
    (inside : point ∈ domain) (enough : horizon domain ≤ otherFuel)
    (table : Cut.Table point.source point.entry point.cut) :
    tableEvaluation model point reference (clip otherFuel first) table = tableEvaluation model point reference first table := by
  rw [table_evaluation_is_its_own_actual_program,table_evaluation_is_its_own_actual_program]
  exact clipping_preserves_the_whole_actual_evaluation model point reference first domain inside enough _

abbrev FiniteProgram (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :=
  Sigma (Program code)

variable (domain : List (Cursor model.source.code)) (original : Rule model.source.code)

/-- All finite programs share the same raw evaluator; only canonical representatives are searched. -/
def accepted (old new : FiniteProgram model.source.code) : Prop :=
  ∀ (world : Replanning.Point model domain) (table : Replanning.TableAt model domain world),
    Synthesis.accepts model.source.code (economicAxes world.val.source world.val.cut)
      (tableEvaluation model world.val original new.2 table.val)
      (tableEvaluation model world.val original old.2 table.val)

def value (bound : Nat) (program : FiniteProgram model.source.code) : Selection.Axis (fuel := bound) model domain → ℚ
  | .economic world table axis => (tableEvaluation model world.val original program.2 table.val).value axis.val
  | .native world table anchor =>
      if (Authority.Trace.Lawful.inventory (tableEvaluation model world.val original program.2 table.val).native).due.Subperm
        (Authority.Trace.Lawful.inventory (tableEvaluation model world.val original anchor table.val).native).due then 0 else 1

omit [DecidableEq Port] [DecidableEq Technology] in
theorem clipping_a_bounded_program_is_itself (program : Program code fuel) : clip fuel program = program := by
  cases program with
  | mk controls bounded => simp only [clip,List.take_of_length_le bounded]

variable {model domain original}

theorem normalized_acceptance_iff (bound : Nat) (enough : horizon domain ≤ bound)
    (old new : FiniteProgram model.source.code) :
    Selection.acceptable model domain original (clip bound old.2) (clip bound new.2) ↔
      accepted model domain original old new := by
  rw [Selection.acceptable_iff_every_generated_cursor]
  constructor
  · intro all world table
    have checked := all world table
    dsimp only [Selection.readTable] at checked
    rw [clipping_preserves_the_whole_table_evaluation model world.val original new.2 domain world.property enough,
      clipping_preserves_the_whole_table_evaluation model world.val original old.2 domain world.property enough] at checked
    exact checked
  · intro all world table
    dsimp only [Selection.readTable]
    rw [clipping_preserves_the_whole_table_evaluation model world.val original new.2 domain world.property enough,
      clipping_preserves_the_whole_table_evaluation model world.val original old.2 domain world.property enough]
    exact all world table

theorem normalized_value_is_the_entire_finite_value (bound : Nat) (enough : horizon domain ≤ bound)
    (program : FiniteProgram model.source.code) :
    Selection.benefit model domain original (clip bound program.2) = value model domain original bound program := by
  funext axis
  cases axis with
  | economic world table axis =>
    dsimp only [Selection.benefit,Selection.readTable,value]
    rw [clipping_preserves_the_whole_table_evaluation model world.val original program.2 domain world.property enough]
  | native world table anchor =>
    simp only [Selection.benefit,Selection.readTable,value,
      clipping_preserves_the_whole_table_evaluation model world.val original program.2 domain world.property enough]

theorem normalized_improvement_iff (bound : Nat) (enough : horizon domain ≤ bound)
    (old new : FiniteProgram model.source.code) :
    Distributed.Improves (Selection.axes (fuel := bound) model domain) (Selection.benefit model domain original)
        (clip bound old.2) (clip bound new.2) ↔
      Distributed.Improves (Selection.axes (fuel := bound) model domain) (value model domain original bound) old new := by
  unfold Distributed.Improves Distributed.NoWorse
  rw [normalized_value_is_the_entire_finite_value bound enough old,
    normalized_value_is_the_entire_finite_value bound enough new]

variable (model domain original)

def holds (reference : Program model.source.code fuel) (program : FiniteProgram model.source.code)
    (row : Replanning.Row model domain) : Prop :=
  let current := tableEvaluation model row.world.val original program.2 row.table.val
  let prior := tableEvaluation model row.world.val original reference row.table.val
  match row.test with
  | .legal => current.legal = true
  | .complete => current.complete = true
  | .profile => current.profile = prior.profile
  | .native => Authority.Trace.Lawful.NoWorse current.native prior.native
  | .economic axis => current.value axis.val ≤ prior.value axis.val

theorem normalized_row_iff (enough : horizon domain ≤ fuel)
    (reference : Program model.source.code fuel) (program : FiniteProgram model.source.code)
    (row : Replanning.Row model domain) :
    Selection.holds model domain original reference (clip fuel program.2) row ↔ holds model domain original reference program row := by
  dsimp only [Selection.holds,Selection.readTable,holds]
  rw [clipping_preserves_the_whole_table_evaluation model row.world.val original program.2 domain row.world.property enough]
  rfl

def Contract (reference : Program model.source.code fuel) : Selection.Outcome model domain original reference → Prop
  | .selected choice =>
      (∀ other : FiniteProgram model.source.code,
        accepted model domain original ⟨fuel,choice.policy.protocol⟩ other →
          ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (value model domain original fuel)
            ⟨fuel,choice.policy.protocol⟩ other) ∧
      ((∃ other : FiniteProgram model.source.code, accepted model domain original ⟨fuel,reference⟩ other ∧
        Distributed.Improves (Selection.axes (fuel := fuel) model domain) (value model domain original fuel) ⟨fuel,reference⟩ other) →
          Distributed.Improves (Selection.axes (fuel := fuel) model domain) (value model domain original fuel)
            ⟨fuel,reference⟩ ⟨fuel,choice.policy.protocol⟩)
  | .blocked rejected => ∀ other : FiniteProgram model.source.code,
      (rejected (clip fuel other.2)).row ∈ Replanning.rows model domain ∧
        ¬ holds model domain original reference other (rejected (clip fuel other.2)).row

theorem every_generated_outcome_covers_all_finite_programs (enough : horizon domain ≤ fuel)
    (reference : Program model.source.code fuel) (outcome : Selection.Outcome model domain original reference) :
    Contract model domain original reference outcome := by
  cases outcome with
  | selected choice =>
    constructor
    · intro other acceptable better
      have checked := (normalized_acceptance_iff fuel enough ⟨fuel,choice.policy.protocol⟩ other).mpr acceptable
      have strict := (normalized_improvement_iff fuel enough ⟨fuel,choice.policy.protocol⟩ other).mpr better
      rw [clipping_a_bounded_program_is_itself] at checked strict
      exact Selection.selected_has_no_full_responsibility_dominator model domain original reference choice _ checked strict
    · rintro ⟨other,acceptable,better⟩
      have checked := (normalized_acceptance_iff fuel enough ⟨fuel,reference⟩ other).mpr acceptable
      have strict := (normalized_improvement_iff fuel enough ⟨fuel,reference⟩ other).mpr better
      rw [clipping_a_bounded_program_is_itself] at checked strict
      have realized := Selection.every_full_responsibility_improvement_is_realized model domain original reference choice
        ⟨clip fuel other.2,checked,strict⟩
      apply (normalized_improvement_iff fuel enough ⟨fuel,reference⟩ ⟨fuel,choice.policy.protocol⟩).mp
      simpa only [clipping_a_bounded_program_is_itself] using realized
  | blocked rejected =>
    intro other
    exact ⟨(rejected (clip fuel other.2)).generated,fun passes =>
      (rejected (clip fuel other.2)).broken ((normalized_row_iff model domain original enough reference other _).mpr passes)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Complete

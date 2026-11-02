import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Complete

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

abbrev FiniteProgram (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :=
  Sigma (Program code)


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
  exact Continuation.Whole.Complete.clipping_a_bounded_program_is_itself program

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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Complete

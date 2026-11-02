import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Machine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Termination
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

/-- A proof bound on the original transitions; execution never reads it. -/
def formulaCost : Expand.Formula → Nat
  | .literal _ => 1
  | .binary opcode left right =>
      1+formulaCost left+formulaCost right+(opcode.operation left.value right.value).initial.weight+2

def expressionCost : Expression pool → Nat
  | .literal _ => 1
  | .source field => 1+formulaCost (Expand.resolve field)
  | .binary opcode left right =>
      1+expressionCost left+expressionCost right+(opcode.operation left.value right.value).initial.weight+2

theorem render_cost (formula : Expand.Formula) : expressionCost pool formula.render = formulaCost formula := by
  induction formula with
  | literal => rfl
  | binary opcode left right ihL ihR =>
    simp only [Expand.Formula.render,expressionCost,ihL,ihR,Expand.Formula.render_value,formulaCost]

def tasksCost : List (Task pool) → List Nat → Nat
  | [],_ => 0
  | .expression source::tail,stack => expressionCost pool source+tasksCost tail (source.value::stack)
  | .apply opcode::tail,right::left::stack =>
      (opcode.operation left right).initial.weight+2+tasksCost tail ((opcode.operation left right).value::stack)
  | .apply _::_,_ => 0

def rank : Frame pool → Nat
  | .program stack tasks => tasksCost pool tasks stack
  | .arithmetic stack operation tail state _ => state.weight+1+tasksCost pool tail (operation.value::stack)

def finished : Frame pool → Bool
  | .program _ [] => true
  | _ => false

theorem each_original_update_progresses {before : Frame pool} (update : Update pool before)
    (active : finished pool before = false) (actual : advance pool before = .updated update) :
    rank pool update.after < rank pool before := by
  cases before with
  | program stack tasks =>
    cases tasks with
    | nil => cases active
    | cons task tail =>
      cases task with
      | expression source =>
        cases source with
        | literal value =>
          cases Step.updated.inj actual
          simp only [rank,tasksCost,expressionCost,Expression.value];omega
        | source field =>
          cases Step.updated.inj actual
          simp only [rank,tasksCost,expressionCost,render_cost,Expand.Formula.render_value,Expand.resolve_value,Expression.value]
          omega
        | binary opcode left right =>
          cases Step.updated.inj actual
          simp only [rank,tasksCost,expressionCost,Expression.value]
          omega
      | apply opcode =>
        cases stack with
        | nil => cases actual
        | cons right rest => cases rest with
          | nil => cases actual
          | cons left rest =>
            cases Step.updated.inj actual
            simp only [rank,tasksCost];omega
  | arithmetic stack operation tail state valid =>
    dsimp only [advance] at actual;split at actual
    · rename_i empty
      cases Step.updated.inj actual
      have exactValue : state.accumulator = operation.value := by
        simpa only [PaidBudgetArithmetic.State.value,empty,List.map_nil,List.sum_nil,Nat.add_zero] using valid
      simp only [rank,exactValue]
      omega
    · rename_i head later commands
      cases Step.updated.inj actual
      have reduced := PaidBudgetArithmetic.advance_strictly_reduces_the_source_program state.accumulator head later
      have same : PaidBudgetArithmetic.State.mk state.accumulator (head::later) = state := by cases state;cases commands;rfl
      rw [same] at reduced
      simp only [rank]
      omega

theorem zero_rank_finishes (before : Frame pool) (valid : before.meaning pool ≠ none) (zero : rank pool before = 0) :
    finished pool before = true := by
  cases active : finished pool before with
  | true => rfl
  | false =>
    cases actual : advance pool before with
    | invalid broken => exact False.elim (valid broken)
    | updated update =>
      have reduced := each_original_update_progresses pool update active actual
      omega

theorem source_rank_finishes_the_original_run (fuel : Nat) (before : Frame pool) (valid : before.meaning pool ≠ none)
    (enough : rank pool before ≤ fuel) : finished pool (execute pool fuel before).endpoint = true := by
  induction fuel generalizing before with
  | zero =>
    have stopped := zero_rank_finishes pool before valid (by omega)
    cases before with
    | program stack tasks =>
      cases tasks with
      | nil => rfl
      | cons => cases stopped
    | arithmetic => cases stopped
  | succ fuel ih =>
    cases before with
    | program stack tasks =>
      cases tasks with
      | nil => rfl
      | cons task tail =>
        dsimp only [execute];split
        · rename_i broken actual;exact False.elim (valid broken)
        · rename_i update actual
          apply ih update.after (fun broken => valid (update.preserved.trans broken))
          have reduced := each_original_update_progresses pool update rfl actual
          omega
    | arithmetic stack operation tail state value =>
      dsimp only [execute];split
      · rename_i broken actual;exact False.elim (valid broken)
      · rename_i update actual
        apply ih update.after (fun broken => valid (update.preserved.trans broken))
        have reduced := each_original_update_progresses pool update rfl actual
        omega

theorem finished_has_a_cached_stack (before : Frame pool) (done : finished pool before = true) :
    ∃ stack,before = .program stack [] := by
  cases before with
  | program stack tasks => cases tasks <;> simp_all [finished]
  | arithmetic => cases done

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Termination

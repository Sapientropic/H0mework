import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Operand
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue)

inductive Task where
  | expression (source : Expression pool)
  | apply (opcode : Opcode)
def pure : List (Task pool) → List Nat → Option (List Nat)
  | [],stack => some stack
  | .expression source::tail,stack => pure tail (source.value::stack)
  | .apply opcode::tail,right::left::stack => pure tail ((opcode.operation left right).value::stack)
  | .apply _::_,_ => none

inductive Frame where
  | program (stack : List Nat) (tasks : List (Task pool))
  | arithmetic (stack : List Nat) (operation : PaidBudgetArithmetic.Operation) (tail : List (Task pool))
      (state : PaidBudgetArithmetic.State) (valid : state.value = operation.value)
def Frame.meaning : Frame pool → Option (List Nat)
  | .program stack tasks => pure pool tasks stack
  | .arithmetic stack operation tail _ _ => pure pool tail (operation.value::stack)

inductive Event where
  | source (field : Operand pool) (value : Nat)
  | sourceExpansion (field : Operand pool) (formula : Expand.Formula)
  | literal (value : Nat)
  | expand (opcode : Opcode) (left right : Expression pool)
  | begin (operation : PaidBudgetArithmetic.Operation)
  | micro (before after : PaidBudgetArithmetic.State)
  | finish (operation : PaidBudgetArithmetic.Operation) (value : Nat)
def Event.Valid : Event pool → Prop
  | .source field value => value = field.value pool
  | .sourceExpansion field formula => formula.value = field.value pool
  | .micro before after => ∃ head tail,before.commands = head::tail ∧ after = PaidBudgetArithmetic.advance before.accumulator head tail
  | .finish operation value => value = operation.value
  | _ => True

structure Update (before : Frame pool) where
  private mk ::
  after : Frame pool
  event : Event pool
  valid : event.Valid pool
  preserved : before.meaning pool = after.meaning pool
inductive Step (before : Frame pool) where
  | invalid (broken : before.meaning pool = none)
  | updated (made : Update pool before)

def advance : (before : Frame pool) → Step pool before
  | .program stack [] => .updated ⟨.program stack [],.literal 0,True.intro,rfl⟩
  | .program stack (.expression source::tail) => match source with
    | .literal value => .updated ⟨.program (value::stack) tail,.literal value,True.intro,rfl⟩
    | .source field =>
      let formula := Expand.resolve field
      .updated ⟨.program stack (.expression formula.render::tail),.sourceExpansion field formula,
        Expand.resolve_value field,by
          change pure pool tail (field.value pool::stack) = pure pool tail ((formula.render (pool := pool)).value::stack)
          rw [Expand.Formula.render_value,Expand.resolve_value]⟩
    | .binary opcode left right => .updated
        ⟨.program stack (.expression left::.expression right::.apply opcode::tail),.expand opcode left right,True.intro,rfl⟩
  | .program stack (.apply opcode::tail) => match stack with
    | [] | [_] => .invalid rfl
    | right::left::rest =>
      let operation := opcode.operation left right
      .updated ⟨.arithmetic rest operation tail operation.initial operation.initial_value,.begin operation,True.intro,rfl⟩
  | .arithmetic stack operation tail state valid => match commands : state.commands with
    | [] =>
      have exact : state.accumulator = operation.value := by
        simpa only [PaidBudgetArithmetic.State.value,commands,List.map_nil,List.sum_nil,Nat.add_zero] using valid
      .updated ⟨.program (state.accumulator::stack) tail,.finish operation state.accumulator,exact,by
        change pure pool tail (operation.value::stack) = pure pool tail (state.accumulator::stack);rw [exact]⟩
    | head::later =>
      let next := PaidBudgetArithmetic.advance state.accumulator head later
      have retained : next.value = operation.value := by
        have previous := PaidBudgetArithmetic.advance_preserves_the_original_value state.accumulator head later
        have same : PaidBudgetArithmetic.State.mk state.accumulator (head::later) = state := by cases state;cases commands;rfl
        exact previous.trans ((congrArg PaidBudgetArithmetic.State.value same).trans valid)
      .updated ⟨.arithmetic stack operation tail next retained,.micro state next,⟨head,later,commands,rfl⟩,rfl⟩

-- Fuel is the already-paid invoice capacity; no transition is taken at zero.
inductive Run : Nat → Frame pool → Type where
  | done (fuel : Nat) (stack : List Nat) : Run fuel (.program stack [])
  | exhausted (before : Frame pool) : Run 0 before
  | malformed (fuel : Nat) (before : Frame pool) (broken : before.meaning pool = none) : Run (fuel+1) before
  | next (fuel : Nat) (before : Frame pool) (step : Update pool before) (later : Run fuel step.after) : Run (fuel+1) before

def execute : (fuel : Nat) → (before : Frame pool) → Run pool fuel before
  | fuel,.program stack [] => .done fuel stack
  | 0,before => .exhausted before
  | fuel+1,before => match advance pool before with
    | .invalid broken => .malformed fuel before broken
    | .updated step => .next fuel before step (execute fuel step.after)

namespace Run
variable {pool} {fuel : Nat} {before : Frame pool}
def endpoint : {fuel : Nat} → {before : Frame pool} → Run pool fuel before → Frame pool
  | _,_,.done _ stack => .program stack []
  | _,_,.exhausted state | _,_,.malformed _ state _ => state
  | _,_,.next _ _ _ later => later.endpoint
def spent : {fuel : Nat} → {before : Frame pool} → Run pool fuel before → Nat
  | _,_,.done .. | _,_,.exhausted .. => 0
  | _,_,.malformed .. => 1
  | _,_,.next _ _ _ later => later.spent+1
def work : {fuel : Nat} → {before : Frame pool} → Run pool fuel before → List (Event pool)
  | _,_,.done .. | _,_,.exhausted .. | _,_,.malformed .. => []
  | _,_,.next _ _ step later => step.event::later.work

theorem bounded (run : Run pool fuel before) : run.spent ≤ fuel := by
  induction run with
  | done | exhausted | malformed => simp [spent]
  | next _ _ _ _ ih => simp only [spent];omega

theorem work_count (run : Run pool fuel before) : run.work.length ≤ run.spent := by
  induction run with
  | done | exhausted | malformed => simp [spent,work]
  | next _ _ _ _ ih => simp only [spent,work,List.length_cons];omega

theorem meaning_preserved (run : Run pool fuel before) : before.meaning pool = run.endpoint.meaning pool := by
  induction run with
  | done | exhausted | malformed => rfl
  | next _ _ step _ ih => exact step.preserved.trans ih

theorem work_is_valid (run : Run pool fuel before) : ∀ event ∈ run.work,event.Valid pool := by
  induction run with
  | done | exhausted | malformed => simp only [work,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | next _ _ step _ ih =>
    intro event inside
    rcases List.mem_cons.mp inside with same | later
    · subst event;exact step.valid
    · exact ih event later

inductive Answer (run : Run pool fuel before) where
  | complete (stack : List Nat) (same : run.endpoint = .program stack [])
  | exhausted (state : Frame pool) (same : run.endpoint = state) (all_spent : run.spent = fuel)
  | malformed (broken : run.endpoint.meaning pool = none)
def answer : {fuel : Nat} → {before : Frame pool} → (run : Run pool fuel before) → Answer run
  | _,_,.done _ stack => .complete stack rfl
  | _,_,.exhausted state => .exhausted state rfl rfl
  | _,_,.malformed _ _ broken => .malformed broken
  | _,_,.next _ _ _ later => match later.answer with
    | .complete stack same => .complete stack same
    | .exhausted state same all_spent => .exhausted state same (congrArg Nat.succ all_spent)
    | .malformed broken => .malformed broken
end Run

structure Calculation (fuel : Nat) where
  private mk ::
  run : Run pool fuel (.program [] [.expression (joint pool)])
  generated : run = execute pool fuel (.program [] [.expression (joint pool)])
def calculate (fuel : Nat) : Calculation pool fuel := ⟨execute pool fuel (.program [] [.expression (joint pool)]),rfl⟩

namespace Calculation
variable {pool} {fuel : Nat} (made : Calculation pool fuel)
theorem completed_value_is_the_same_paid_source (stack : List Nat)
    (complete : made.run.endpoint = .program stack []) : stack = [Body.units pool + Work.workBudget pool] := by
  have semantics := made.run.meaning_preserved
  rw [complete] at semantics
  change some [(joint pool).value] = some stack at semantics
  rw [joint_value] at semantics
  exact (Option.some.inj semantics).symm
inductive Result where
  | budget (value : Nat) (same : made.run.endpoint = .program [value] [])
      (correct : value = Body.units pool + Work.workBudget pool)
  | exhausted (state : Frame pool) (residual : made.run.endpoint = state) (all_spent : made.run.spent = fuel)
def result : Result made := match made.run.answer with
  | .exhausted state same all_spent => .exhausted state same all_spent
  | .malformed broken => False.elim (by
    have bad := made.run.meaning_preserved.trans broken
    change some [(joint pool).value] = none at bad
    cases bad)
  | .complete stack same =>
    have exact := made.completed_value_is_the_same_paid_source stack same
    .budget (stack.headD 0) (by
      have cached : stack = [stack.headD 0] := by rw [exact];rfl
      rw [same,cached];rfl) (by rw [exact];rfl)
end Calculation
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter
namespace Acquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
  {catalogue : Catalogue snapshot} (pool : Comparison.Pool catalogue) (units : Nat)
private theorem canonical (made : Calculation pool units) : made = calculate pool units := by
  rcases made with ⟨run,generated⟩;cases generated;rfl
inductive State where
  | running (left : Nat) (current : Frame pool)
      (wrap : Run pool left current → Run pool units (.program [] [.expression (joint pool)]))
      (coherent : wrap (execute pool left current) = execute pool units (.program [] [.expression (joint pool)]))
  | finished (calculation : Calculation pool units) (generated : calculation = calculate pool units)
def initial : State pool units := .running units (.program [] [.expression (joint pool)]) id rfl
inductive Event where
  | step (current : Frame pool) (update : Update pool current) (actual : advance pool current = .updated update)
  | complete (calculation : Calculation pool units) (generated : calculation = calculate pool units)
private def finish {left : Nat} {current : Frame pool}
    (wrap : Run pool left current → Run pool units (.program [] [.expression (joint pool)]))
    (coherent : wrap (execute pool left current) = execute pool units (.program [] [.expression (joint pool)]))
    (tail : Run pool left current) (actual : tail = execute pool left current) : Calculation pool units :=
  ⟨wrap tail,(congrArg wrap actual).trans coherent⟩

def move : State pool units → Option (State pool units × Event pool units)
  | .running left (.program stack []) wrap coherent =>
      let made := finish pool units wrap coherent (.done left stack) (by rw [execute])
      some (.finished made (canonical pool units made),.complete made (canonical pool units made))
  | .running 0 (.program stack (head::tail)) wrap coherent =>
      let made := finish pool units wrap coherent (.exhausted _) (by rw [execute];simp)
      some (.finished made (canonical pool units made),.complete made (canonical pool units made))
  | .running (left+1) (.program stack (head::tail)) wrap coherent =>
      match actual : advance pool (.program stack (head::tail)) with
      | .invalid broken =>
          let made := finish pool units wrap coherent (.malformed left _ broken) (by
            rw [execute]
            · split
              · rfl
              · rename_i update observed;cases actual.symm.trans observed
            · simp)
          some (.finished made (canonical pool units made),.complete made (canonical pool units made))
      | .updated update =>
          some (.running left update.after (fun later => wrap (.next left _ update later)) (by
            rw [← coherent];congr 1
            rw [execute]
            · split
              · rename_i broken observed;cases actual.symm.trans observed
              · rename_i other observed;cases Step.updated.inj (actual.symm.trans observed);rfl
            · simp),.step _ update actual)
  | .running 0 (.arithmetic stack operation tail state valid) wrap coherent =>
      let made := finish pool units wrap coherent (.exhausted _) (by rw [execute];simp)
      some (.finished made (canonical pool units made),.complete made (canonical pool units made))
  | .running (left+1) (.arithmetic stack operation tail state valid) wrap coherent =>
      match actual : advance pool (.arithmetic stack operation tail state valid) with
      | .invalid broken =>
          let made := finish pool units wrap coherent (.malformed left _ broken) (by
            rw [execute]
            · split
              · rfl
              · rename_i update observed;cases actual.symm.trans observed
            · simp)
          some (.finished made (canonical pool units made),.complete made (canonical pool units made))
      | .updated update =>
          some (.running left update.after (fun later => wrap (.next left _ update later)) (by
            rw [← coherent];congr 1
            rw [execute]
            · split
              · rename_i broken observed;cases actual.symm.trans observed
              · rename_i other observed;cases Step.updated.inj (actual.symm.trans observed);rfl
            · simp),.step _ update actual)
  | .finished .. => none

def State.rank : State pool units → Nat | .running left .. => left+1 | .finished .. => 0
def State.done : State pool units → Bool | .finished .. => true | _ => false
theorem progress {before after : State pool units} {event : Event pool units}
    (actual : move pool units before = some (after,event)) : after.rank pool units < before.rank pool units := by
  cases before with
  | running left current wrap coherent =>
      cases current with
      | program stack tasks =>
          cases tasks with
          | nil => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
          | cons head tail =>
              cases left with
              | zero => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
              | succ left =>
                  dsimp only [move] at actual;split at actual
                  all_goals cases Option.some.inj actual;simp only [State.rank];omega
      | arithmetic =>
          cases left with
          | zero => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
          | succ left =>
              dsimp only [move] at actual;split at actual
              all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State pool units) : move pool units before = none ↔ before.done pool units = true := by
  cases before with
  | running left current wrap coherent =>
      cases current with
      | program stack tasks =>
          cases tasks with
          | nil => simp [move,State.done]
          | cons head tail => cases left <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
      | arithmetic => cases left <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
  | finished => simp [move,State.done]
end Acquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter

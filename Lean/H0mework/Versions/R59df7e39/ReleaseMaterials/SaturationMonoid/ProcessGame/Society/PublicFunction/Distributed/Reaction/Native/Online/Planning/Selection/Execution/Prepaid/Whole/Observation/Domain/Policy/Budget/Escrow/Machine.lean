import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Arithmetic.Consumer
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

inductive Frame where
  | program (core : SourceBudgetMachine.Core) (commands : List SourceBudgetMachine.Instruction)
  | arithmetic (core : SourceBudgetMachine.Core) (head : SourceBudgetMachine.Instruction) (tail : List SourceBudgetMachine.Instruction)
      (request : PaidBudgetArithmetic.Request head core) (state : PaidBudgetArithmetic.State) (valid : state.value = request.operation.value)

def Frame.meaning (prepared : Prepared input) : Frame → Option SourceBudgetMachine.Core
  | .program core commands => SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) commands core
  | .arithmetic core head tail _ _ _ => SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) (head::tail) core

structure Update (prepared : Prepared input) (before : Frame) where
  private mk ::
  after : Frame
  work : List (Budget.Event prepared)
  sound : ∀ event ∈ work,event.Valid prepared
  preserved : before.meaning prepared = after.meaning prepared

inductive Step (prepared : Prepared input) (before : Frame) where
  | invalid (broken : before.meaning prepared = none)
  | updated (made : Update prepared before)

def advance (prepared : Prepared input) : (before : Frame) → Step prepared before
  | .program core [] => .updated ⟨.program core [],[],by simp,rfl⟩
  | .program core (head::tail) =>
    match found : PaidBudgetArithmetic.request head core with
    | some request => .updated ⟨.arithmetic core head tail request request.operation.initial request.operation.initial_value,
        [],by simp,rfl⟩
    | none => match SourceBudgetMachine.evaluate prepared head core with
      | .invalid broken => .invalid (by change (SourceBudgetMachine.step _ _ _).bind _ = none;rw [broken];rfl)
      | .done made => .updated ⟨.program made.after tail,made.work,made.valid,by
          change (SourceBudgetMachine.step _ _ _).bind _ = _;rw [made.exact];rfl⟩
  | .arithmetic core head tail request state valid =>
    match commands : state.commands with
    | [] =>
      have correct : state.accumulator = request.operation.value := by
        simpa only [PaidBudgetArithmetic.State.value,commands,List.map_nil,List.sum_nil,Nat.add_zero] using valid
      .updated ⟨.program (request.after state.accumulator) tail,[request.operation.event prepared state.accumulator],
        by intro event inside;have same := List.mem_singleton.mp inside;subst event;exact request.operation.event_valid prepared _ correct,
        by change (SourceBudgetMachine.step _ _ _).bind _ = _;rw [request.original_step state.accumulator correct];rfl⟩
    | command::later =>
      let next := PaidBudgetArithmetic.advance state.accumulator command later
      have retained : next.value = request.operation.value := by
        have previous := PaidBudgetArithmetic.advance_preserves_the_original_value state.accumulator command later
        have same : PaidBudgetArithmetic.State.mk state.accumulator (command::later) = state := by cases state;cases commands;rfl
        exact previous.trans ((congrArg PaidBudgetArithmetic.State.value same).trans valid)
      .updated ⟨.arithmetic core head tail request next retained,[],by simp,rfl⟩

inductive Run (prepared : Prepared input) : Nat → Frame → Type where
  | done (fuel : Nat) (core : SourceBudgetMachine.Core) : Run prepared fuel (.program core [])
  | exhausted (before : Frame) : Run prepared 0 before
  | malformed (fuel : Nat) (before : Frame) (broken : before.meaning prepared = none) : Run prepared (fuel+1) before
  | next (fuel : Nat) (before : Frame) (step : Update prepared before)
      (later : Run prepared fuel step.after) : Run prepared (fuel+1) before

def execute (prepared : Prepared input) : (fuel : Nat) → (before : Frame) → Run prepared fuel before
  | fuel,.program core [] => .done fuel core
  | 0,before => .exhausted before
  | fuel+1,before => match advance prepared before with
    | .invalid broken => .malformed fuel before broken
    | .updated step => .next fuel before step (execute prepared fuel step.after)

namespace Run
variable {fuel : Nat} {before : Frame}

def endpoint : {fuel : Nat} → {before : Frame} → Run prepared fuel before → Frame
  | _,_,.done _ core => .program core []
  | _,_,.exhausted state => state
  | _,_,.malformed _ state _ => state
  | _,_,.next _ _ _ later => later.endpoint

def spent : {fuel : Nat} → {before : Frame} → Run prepared fuel before → Nat
  | _,_,.done .. => 0
  | _,_,.exhausted .. => 0
  | _,_,.malformed .. => 1
  | _,_,.next _ _ _ later => later.spent+1

def work : {fuel : Nat} → {before : Frame} → Run prepared fuel before → List (Budget.Event prepared)
  | _,_,.done .. => []
  | _,_,.exhausted .. => []
  | _,_,.malformed .. => []
  | _,_,.next _ _ step later => step.work ++ later.work

theorem bounded (run : Run prepared fuel before) : run.spent ≤ fuel := by
  induction run with
  | done | exhausted | malformed => simp [spent]
  | next _ _ _ _ ih => simp only [spent];omega

theorem meaning_preserved (run : Run prepared fuel before) : before.meaning prepared = run.endpoint.meaning prepared := by
  induction run with
  | done | exhausted | malformed => rfl
  | next _ _ step _ ih => exact step.preserved.trans ih

theorem all_work_is_valid (run : Run prepared fuel before) : ∀ event ∈ run.work,event.Valid prepared := by
  induction run with
  | done | exhausted | malformed => simp only [work,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | next _ _ step _ ih =>
    intro event inside
    rcases List.mem_append.mp inside with first | rest
    · exact step.sound event first
    · exact ih event rest

inductive Answer (run : Run prepared fuel before) where
  | complete (core : SourceBudgetMachine.Core) (same : run.endpoint = .program core [])
  | exhausted (state : Frame) (same : run.endpoint = state) (all_spent : run.spent = fuel)
  | malformed (broken : run.endpoint.meaning prepared = none)

def answer : {fuel : Nat} → {before : Frame} → (run : Run prepared fuel before) → Answer run
  | _,_,.done _ core => .complete core rfl
  | _,_,.exhausted state => .exhausted state rfl rfl
  | _,_,.malformed _ _ broken => .malformed broken
  | _,_,.next _ _ _ later => match later.answer with
    | .complete core same => .complete core same
    | .exhausted state same all_spent => .exhausted state same (congrArg Nat.succ all_spent)
    | .malformed broken => .malformed broken

-- Each transition consumes its own ordinal; allocation is independent of body results.
def slot (run : Run prepared fuel before) (ordinal : Fin run.spent) : Fin fuel :=
  ⟨ordinal.val,Nat.lt_of_lt_of_le ordinal.isLt run.bounded⟩

theorem no_slot_reuse (run : Run prepared fuel before) : Function.Injective run.slot := by
  intro first second same
  exact Fin.ext (congrArg (fun slot : Fin fuel => slot.val) same)
end Run

structure Calculation (prepared : Prepared input) (fuel : Nat) where
  private mk ::
  run : Run prepared fuel (.program SourceBudgetMachine.initial SourceBudgetMachine.code)
  generated : run = execute prepared fuel (.program SourceBudgetMachine.initial SourceBudgetMachine.code)

def calculate (prepared : Prepared input) (fuel : Nat) : Calculation prepared fuel :=
  ⟨execute prepared fuel (.program SourceBudgetMachine.initial SourceBudgetMachine.code),rfl⟩

namespace Calculation
variable {fuel : Nat} (made : Calculation prepared fuel)

theorem complete_value_is_for_the_frozen_paid_source (core : SourceBudgetMachine.Core)
    (complete : made.run.endpoint = .program core []) : core.stack.head? = some (Work.workBudget prepared) := by
  have semantics := made.run.meaning_preserved
  rw [complete] at semantics
  change SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) SourceBudgetMachine.code SourceBudgetMachine.initial = some core at semantics
  have source := SourceBudgetMachine.the_source_program_computes_the_original_work_budget prepared
  rw [semantics] at source
  exact Option.some.inj source

inductive Result where
  | budget (value : Nat) (core : SourceBudgetMachine.Core) (cached : made.run.endpoint = .program core [])
      (observed : core.stack.head? = some value) (correct : value = Work.workBudget prepared)
  | exhausted (state : Frame) (residual : made.run.endpoint = state) (all_spent : made.run.spent = fuel)

def result : Result made :=
  match made.run.answer with
  | .exhausted state same all_spent => .exhausted state same all_spent
  | .malformed broken => False.elim (by
      have bad := made.run.meaning_preserved.trans broken
      change SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) SourceBudgetMachine.code SourceBudgetMachine.initial = none at bad
      have source := SourceBudgetMachine.the_source_program_computes_the_original_work_budget prepared
      change (SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) SourceBudgetMachine.code SourceBudgetMachine.initial).map (fun core => core.stack.head?) = _ at source
      rw [bad] at source
      cases source)
  | .complete core same =>
      let correct := made.complete_value_is_for_the_frozen_paid_source core same
      .budget (core.stack.head?.getD 0) core same (by rw [correct];rfl) (by rw [correct];rfl)
end Calculation
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
namespace CalculationAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} (prepared : Prepared input) (units : Nat)
private theorem canonical (made : Calculation prepared units) : made = calculate prepared units := by
  rcases made with ⟨run,generated⟩;cases generated;rfl
inductive State where
  | running (left : Nat) (current : Frame)
      (wrap : Run prepared left current → Run prepared units (.program SourceBudgetMachine.initial SourceBudgetMachine.code))
      (coherent : wrap (execute prepared left current) = execute prepared units (.program SourceBudgetMachine.initial SourceBudgetMachine.code))
  | finished (calculation : Calculation prepared units) (generated : calculation = calculate prepared units)
def initial : State prepared units := .running units (.program SourceBudgetMachine.initial SourceBudgetMachine.code) id rfl
inductive Event where
  | step (current : Frame) (update : Update prepared current) (actual : advance prepared current = .updated update)
  | complete (calculation : Calculation prepared units) (generated : calculation = calculate prepared units)
private def finish {left : Nat} {current : Frame}
    (wrap : Run prepared left current → Run prepared units (.program SourceBudgetMachine.initial SourceBudgetMachine.code))
    (coherent : wrap (execute prepared left current) = execute prepared units (.program SourceBudgetMachine.initial SourceBudgetMachine.code))
    (tail : Run prepared left current) (actual : tail = execute prepared left current) : Calculation prepared units :=
  ⟨wrap tail,(congrArg wrap actual).trans coherent⟩

def move : State prepared units → Option (State prepared units × Event prepared units)
  | .running left (.program stack []) wrap coherent =>
      let made := finish prepared units wrap coherent (.done left stack) (by rw [execute])
      some (.finished made (canonical prepared units made),.complete made (canonical prepared units made))
  | .running 0 (.program stack (head::tail)) wrap coherent =>
      let made := finish prepared units wrap coherent (.exhausted _) (by rw [execute];simp)
      some (.finished made (canonical prepared units made),.complete made (canonical prepared units made))
  | .running (left+1) (.program stack (head::tail)) wrap coherent =>
      match actual : advance prepared (.program stack (head::tail)) with
      | .invalid broken =>
          let made := finish prepared units wrap coherent (.malformed left _ broken) (by
            rw [execute]
            · split
              · rfl
              · rename_i update observed;cases actual.symm.trans observed
            · simp)
          some (.finished made (canonical prepared units made),.complete made (canonical prepared units made))
      | .updated update =>
          some (.running left update.after (fun later => wrap (.next left _ update later)) (by
            rw [← coherent];congr 1
            rw [execute]
            · split
              · rename_i broken observed;cases actual.symm.trans observed
              · rename_i other observed;cases Step.updated.inj (actual.symm.trans observed);rfl
            · simp),.step _ update actual)
  | .running 0 (.arithmetic stack head tail request state valid) wrap coherent =>
      let made := finish prepared units wrap coherent (.exhausted _) (by rw [execute];simp)
      some (.finished made (canonical prepared units made),.complete made (canonical prepared units made))
  | .running (left+1) (.arithmetic stack head tail request state valid) wrap coherent =>
      match actual : advance prepared (.arithmetic stack head tail request state valid) with
      | .invalid broken =>
          let made := finish prepared units wrap coherent (.malformed left _ broken) (by
            rw [execute]
            · split
              · rfl
              · rename_i update observed;cases actual.symm.trans observed
            · simp)
          some (.finished made (canonical prepared units made),.complete made (canonical prepared units made))
      | .updated update =>
          some (.running left update.after (fun later => wrap (.next left _ update later)) (by
            rw [← coherent];congr 1
            rw [execute]
            · split
              · rename_i broken observed;cases actual.symm.trans observed
              · rename_i other observed;cases Step.updated.inj (actual.symm.trans observed);rfl
            · simp),.step _ update actual)
  | .finished .. => none

def State.rank : State prepared units → Nat | .running left .. => left+1 | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move prepared units before = some (after,event)) : after.rank prepared units < before.rank prepared units := by
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

theorem no_move_iff_done (before : State prepared units) : move prepared units before = none ↔ before.done prepared units = true := by
  cases before with
  | running left current wrap coherent =>
      cases current with
      | program stack tasks =>
          cases tasks with
          | nil => simp [move,State.done]
          | cons head tail => cases left <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
      | arithmetic => cases left <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
  | finished => simp [move,State.done]
end CalculationAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget

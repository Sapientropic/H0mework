import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Machine
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Arithmetic
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.PaidBudgetArithmetic

open Institutions.Capitalism.Universal.Source.Program

namespace Operation
def opcode : Operation → SourceBudgetMachine.Instruction
  | .add .. => .add
  | .multiply .. => .multiply
  | .maximum .. => .maximum

def operands : Operation → List Nat
  | .add left right | .multiply left right | .maximum left right => [right,left]
end Operation

structure Request (command : SourceBudgetMachine.Instruction) (before : SourceBudgetMachine.Core) where
  private mk ::
  operation : Operation
  tail : List Nat
  command_exact : command = operation.opcode
  stack_exact : before.stack = operation.operands ++ tail

-- The live stack fixes both operands. No caller chooses a result or an
-- alternative operand pair, and this decoder never calls atomic evaluate.
def request (command : SourceBudgetMachine.Instruction) (before : SourceBudgetMachine.Core) :
    Option (Request command before) :=
  match command,stack : before.stack with
  | .add,right::left::tail => some ⟨.add left right,tail,rfl,stack⟩
  | .multiply,right::left::tail => some ⟨.multiply left right,tail,rfl,stack⟩
  | .maximum,right::left::tail => some ⟨.maximum left right,tail,rfl,stack⟩
  | _,_ => none

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O]
  [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {point : NativePoint input}
  {command : SourceBudgetMachine.Instruction} {before : SourceBudgetMachine.Core}

def Operation.event (prepared : Prepared input) (result : Nat) : Operation → Budget.Event prepared
  | .add left right => .add left right result
  | .multiply left right => .multiply left right result
  | .maximum left right => .maximum left right result

theorem Operation.event_valid (prepared : Prepared input) (operation : Operation) (result : Nat)
    (exact : result = operation.value) : (operation.event prepared result).Valid prepared := by
  cases operation <;> exact exact

def Request.after (source : Request command before) (result : Nat) : SourceBudgetMachine.Core :=
  {before with stack := result :: source.tail}

theorem Request.original_step (source : Request command before) (result : Nat)
    (exact : result = source.operation.value) :
    SourceBudgetMachine.step (SourceBudgetMachine.Source.expected prepared) command before =
      some (source.after result) := by
  rcases source with ⟨operation,tail,commandExact,original⟩
  cases commandExact
  dsimp only [Request.after] at *
  cases operation with
  | add left right =>
      simp only [Operation.opcode,SourceBudgetMachine.step,original,Operation.operands,List.cons_append,List.nil_append]
      rw [exact]
      rfl
  | multiply left right =>
      simp only [Operation.opcode,SourceBudgetMachine.step,original,Operation.operands,List.cons_append,List.nil_append]
      rw [exact]
      rfl
  | maximum left right =>
      simp only [Operation.opcode,SourceBudgetMachine.step,original,Operation.operands,List.cons_append,List.nil_append]
      rw [exact]
      rfl

structure Update (scope : OriginalScope point) (source : Request command before) where
  private mk ::
  calculation : Computation scope source.operation
  completed : calculation.execution.finalState.commands = []
  value : Nat
  cached : value = calculation.execution.finalState.accumulator
  exact : value = source.operation.value
  after : SourceBudgetMachine.Core
  after_exact : after = source.after value
  source_step : SourceBudgetMachine.step (SourceBudgetMachine.Source.expected prepared) command before = some after
  event : Budget.Event prepared
  event_exact : event = source.operation.event prepared value
  valid : event.Valid prepared

def finish {scope : OriginalScope point} (source : Request command before)
    (made : Computation scope source.operation) (completed : made.execution.finalState.commands = []) :
    Update (prepared := prepared) scope source :=
  let value := made.execution.finalState.accumulator
  let correct := (made.execution.completed_value_is_the_original_arithmetic completed).trans source.operation.initial_value
  ⟨made,completed,value,rfl,correct,source.after value,rfl,source.original_step value correct,
    source.operation.event prepared value,rfl,source.operation.event_valid prepared value correct⟩

inductive Outcome (prepared : Prepared input) (scope : OriginalScope point)
    (command : SourceBudgetMachine.Instruction) (before : SourceBudgetMachine.Core) where
  | unhandled (observed : request command before = none)
  | blocked (source : Request command before) (observed : request command before = some source)
      (calculation : Computation scope source.operation) (failure : Run.Blocked calculation.execution)
  | updated (source : Request command before) (observed : request command before = some source)
      (update : Update (prepared := prepared) scope source)

def evaluate (prepared : Prepared input) (scope : OriginalScope point)
    (command : SourceBudgetMachine.Instruction) (before : SourceBudgetMachine.Core) : Outcome prepared scope command before :=
  match observed : request command before with
  | none => .unhandled observed
  | some source =>
    let calculation := compute scope source.operation
    match calculation.answer with
    | .blocked failure => .blocked source observed calculation failure
    | .value _ _ _ completed => .updated source observed (finish source calculation completed)

namespace Update
variable {scope : OriginalScope point} {source : Request command before}
    (made : Update (prepared := prepared) scope source)

theorem result_is_read_from_the_same_paid_computation :
    made.value = made.calculation.execution.finalState.accumulator := made.cached

theorem the_original_budget_program_consumes_the_paid_result (tail : List SourceBudgetMachine.Instruction) :
    SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) (command::tail) before =
      SourceBudgetMachine.runPure (SourceBudgetMachine.Source.expected prepared) tail made.after := by
  change (SourceBudgetMachine.step _ _ _).bind _ = _
  rw [made.source_step]
  rfl

theorem actual_scope_keeps_the_complete_fee_prefix :
    made.calculation.execution.finalScope.continuation.words =
      scope.continuation.words ++ made.calculation.execution.emitted :=
  made.calculation.execution.every_actual_fee_word_is_preserved

theorem no_arithmetic_step_reuses_a_paid_prefix_address :
    made.calculation.execution.paymentAddresses.Nodup :=
  made.calculation.execution.no_successful_microstep_reuses_a_prior_invoice_address
end Update

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.PaidBudgetArithmetic

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.PaidBudgetArithmetic

open Institutions.Capitalism.Universal.Source.Program

inductive Command where
  | add (remaining : Nat)
  | multiply (left right : Nat)
  | maximum (left right : Nat)
  deriving DecidableEq

def Command.value : Command → Nat
  | .add remaining => remaining
  | .multiply left right => left * right
  | .maximum left right => max left right

def Command.weight : Command → Nat
  | .add remaining => remaining + 1
  | .multiply left right => right * (left + 2) + 1
  | .maximum left right => left + right + 2

structure State where
  accumulator : Nat
  commands : List Command

def State.value (state : State) : Nat :=
  state.accumulator + (state.commands.map Command.value).sum

def State.weight (state : State) : Nat := (state.commands.map Command.weight).sum

-- The executed language uses only constructor inspection, successors and list
-- operations. Multiplication and maximum below occur only in its specification.
def advance (accumulator : Nat) (command : Command) (tail : List Command) : State :=
  match command with
  | .add 0 => ⟨accumulator,tail⟩
  | .add (remaining+1) => ⟨accumulator+1,.add remaining :: tail⟩
  | .multiply _ 0 => ⟨accumulator,tail⟩
  | .multiply left (right+1) => ⟨accumulator,.add left :: .multiply left right :: tail⟩
  | .maximum 0 right => ⟨accumulator,.add right :: tail⟩
  | .maximum (left+1) 0 => ⟨accumulator,.add (left+1) :: tail⟩
  | .maximum (left+1) (right+1) => ⟨accumulator+1,.maximum left right :: tail⟩

theorem advance_preserves_the_original_value (accumulator : Nat) (command : Command) (tail : List Command) :
    (advance accumulator command tail).value = (State.mk accumulator (command :: tail)).value := by
  cases command with
  | add remaining => cases remaining <;> simp [advance,State.value,Command.value,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | multiply left right => cases right <;> simp [advance,State.value,Command.value,Nat.mul_succ,Nat.add_assoc,Nat.add_comm]
  | maximum left right =>
    cases left <;> cases right <;>
      simp [advance,State.value,Command.value,Nat.succ_max_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem advance_strictly_reduces_the_source_program (accumulator : Nat) (command : Command) (tail : List Command) :
    (advance accumulator command tail).weight < (State.mk accumulator (command :: tail)).weight := by
  cases command with
  | add remaining => cases remaining <;> simp [advance,State.weight,Command.weight]
  | multiply left right => cases right <;> simp [advance,State.weight,Command.weight,Nat.succ_mul]; omega
  | maximum left right => cases left <;> cases right <;> simp [advance,State.weight,Command.weight]; omega

variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O]
  [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {point : NativePoint input}

abbrev OriginalScope (point : NativePoint input) :=
  Scope (Policy.initial input point) input.pricing input.future (Policy.reference input point) input.actor input.position

def refresh (scope : OriginalScope point) : OriginalScope point :=
  Whole.withOwnInvoices scope (Production.invoiceQuotations (Policy.initial input point) input.pricing input.future
    (Policy.reference input point) input.actor input.position scope input.span)

structure Payment (scope : OriginalScope point) where
  private mk ::
  bill : Prefix.Bill (Whole.paidPoint scope) input.actor input.position
  before : bill.before = scope.continuation.words
  units : bill.units = 1
  quoted : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words 1 = some ⟨bill,before,units⟩
  paid : bill.payment.succeeded = true
  after : OriginalScope point
  after_exact : after = refresh (Whole.extend scope bill before)

theorem Payment.actual_prefix (scope : OriginalScope point) (paid : Payment scope) :
    paid.after.continuation.words = scope.continuation.words ++ [paid.bill.payment.output] := by
  rw [paid.after_exact]
  exact scope.continuation.append_words paid.bill paid.before

inductive Attempt (scope : OriginalScope point) where
  | absent (why : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words 1 = none)
  | refused (bill : Prefix.Bill (Whole.paidPoint scope) input.actor input.position)
      (before : bill.before = scope.continuation.words) (units : bill.units = 1)
      (quoted : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words 1 = some ⟨bill,before,units⟩)
      (unpaid : bill.payment.succeeded = false)
  | paid (receipt : Payment scope)

def pay (scope : OriginalScope point) : Attempt scope :=
  match quoted : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words 1 with
  | none => .absent quoted
  | some invoice =>
    if paid : invoice.val.payment.succeeded = true then
      .paid ⟨invoice.val,invoice.property.1,invoice.property.2,quoted,paid,
        refresh (Whole.extend scope invoice.val invoice.property.1),rfl⟩
    else .refused invoice.val invoice.property.1 invoice.property.2 quoted (Bool.eq_false_iff.mpr paid)

def Attempt.after {scope : OriginalScope point} : Attempt scope → OriginalScope point
  | .absent _ => scope
  | .refused bill before .. => Whole.extend scope bill before
  | .paid receipt => receipt.after

def Attempt.emitted {scope : OriginalScope point} : Attempt scope →
    List (List (Future.Recovery.Action (Policy.initial input point).model))
  | .absent _ => []
  | .refused bill .. => [bill.payment.output]
  | .paid receipt => [receipt.bill.payment.output]

def Attempt.failed {scope : OriginalScope point} : Attempt scope → Prop
  | .absent _ | .refused .. => True
  | .paid _ => False

inductive Debt where
  | quotation (before : OriginalScope point)
  | replay (before : OriginalScope point)
      (bill : Prefix.Bill (Whole.paidPoint before) input.actor input.position)
  | refresh (before after : OriginalScope point)
  | control (before : State)
  | storage (before after : State)

def Attempt.pending {scope : OriginalScope point} : Attempt scope → List (Debt (point := point))
  | .absent _ => [.quotation scope]
  | .refused bill .. => [.quotation scope,.replay scope bill]
  | .paid receipt => [.quotation scope,.replay scope receipt.bill,
      .refresh (Whole.extend scope receipt.bill receipt.before) receipt.after]

theorem Attempt.actual_prefix {scope : OriginalScope point} (attempt : Attempt scope) :
    attempt.after.continuation.words = scope.continuation.words ++ attempt.emitted := by
  cases attempt with
  | absent => exact (List.append_nil _).symm
  | refused bill before _ _ _ => exact scope.continuation.append_words bill before
  | paid receipt => exact receipt.actual_prefix scope

-- Every recursive transition contains a successful payment from its own
-- predecessor scope. A failed payment does not execute the arithmetic move.
inductive Run : OriginalScope point → State → Type where
  | done (scope : OriginalScope point) (accumulator : Nat) : Run scope ⟨accumulator,[]⟩
  | blocked (scope : OriginalScope point) (accumulator : Nat) (head : Command) (tail : List Command)
      (attempt : Attempt scope) (failed : attempt.failed) : Run scope ⟨accumulator,head::tail⟩
  | next (scope : OriginalScope point) (accumulator : Nat) (head : Command) (tail : List Command)
      (receipt : Payment scope) (later : Run receipt.after (advance accumulator head tail)) :
      Run scope ⟨accumulator,head::tail⟩

def execute (scope : OriginalScope point) (state : State) : Run scope state :=
  match state with
  | ⟨accumulator,[]⟩ => .done scope accumulator
  | ⟨accumulator,head::tail⟩ =>
    match pay scope with
    | .absent why => .blocked scope accumulator head tail (.absent why) True.intro
    | .refused bill before units quoted unpaid =>
      .blocked scope accumulator head tail (.refused bill before units quoted unpaid) True.intro
    | .paid receipt => .next scope accumulator head tail receipt (execute receipt.after (advance accumulator head tail))
termination_by state.weight
decreasing_by exact advance_strictly_reduces_the_source_program _ _ _

namespace Run
def finalScope : {scope : OriginalScope point} → {state : State} → Run scope state → OriginalScope point
  | _,_,.done scope _ => scope
  | _,_,.blocked _ _ _ _ attempt _ => attempt.after
  | _,_,.next _ _ _ _ _ later => later.finalScope

def finalState : {scope : OriginalScope point} → {state : State} → Run scope state → State
  | _,_,.done _ accumulator => ⟨accumulator,[]⟩
  | _,_,.blocked _ accumulator head tail _ _ => ⟨accumulator,head::tail⟩
  | _,_,.next _ _ _ _ _ later => later.finalState

def paidSteps : {scope : OriginalScope point} → {state : State} → Run scope state → Nat
  | _,_,.done .. | _,_,.blocked .. => 0
  | _,_,.next _ _ _ _ _ later => later.paidSteps + 1

def emitted : {scope : OriginalScope point} → {state : State} → Run scope state →
    List (List (Future.Recovery.Action (Policy.initial input point).model))
  | _,_,.done .. => []
  | _,_,.blocked _ _ _ _ attempt _ => attempt.emitted
  | _,_,.next _ _ _ _ receipt later => receipt.bill.payment.output :: later.emitted

def pending : {scope : OriginalScope point} → {state : State} → Run scope state → List (Debt (point := point))
  | _,_,.done .. => []
  | _,_,.blocked _ accumulator head tail attempt _ =>
      .control ⟨accumulator,head::tail⟩ :: attempt.pending
  | _,_,.next scope accumulator head tail receipt later =>
      [.control ⟨accumulator,head::tail⟩,.storage ⟨accumulator,head::tail⟩ (advance accumulator head tail)] ++
      (Attempt.paid receipt).pending ++ later.pending

def paymentAddresses : {scope : OriginalScope point} → {state : State} → Run scope state → List Nat
  | _,_,.done .. | _,_,.blocked .. => []
  | _,_,.next _ _ _ _ receipt later => receipt.bill.before.length :: later.paymentAddresses

variable {scope : OriginalScope point} {state : State} (run : Run scope state)

theorem exact_value_is_preserved_even_when_payment_fails : run.finalState.value = state.value := by
  induction run with
  | done | blocked => rfl
  | next scope accumulator head tail receipt later ih =>
    exact ih.trans (advance_preserves_the_original_value accumulator head tail)

theorem every_actual_fee_word_is_preserved :
    run.finalScope.continuation.words = scope.continuation.words ++ run.emitted := by
  induction run with
  | done => exact (List.append_nil _).symm
  | blocked scope accumulator head tail attempt failed => exact attempt.actual_prefix
  | next scope accumulator head tail receipt later ih =>
    rw [show (Run.next scope accumulator head tail receipt later).finalScope = later.finalScope from rfl,ih,receipt.actual_prefix]
    exact List.append_assoc _ _ _

theorem completed_value_is_the_original_arithmetic (completed : run.finalState.commands = []) :
    run.finalState.accumulator = state.value := by
  have exactValue := run.exact_value_is_preserved_even_when_payment_fails
  simpa only [State.value,completed,List.map_nil,List.sum_nil,Nat.add_zero] using exactValue

theorem every_successful_step_has_its_own_invoice_slot : run.paymentAddresses.length = run.paidSteps := by
  induction run with
  | done | blocked => rfl
  | next scope accumulator head tail receipt later ih =>
      change later.paymentAddresses.length + 1 = later.paidSteps + 1
      exact congrArg Nat.succ ih

theorem every_payment_address_starts_after_the_original_prefix :
    ∀ address ∈ run.paymentAddresses,scope.continuation.words.length ≤ address := by
  induction run with
  | done | blocked => simp only [paymentAddresses,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | next scope accumulator head tail receipt later ih =>
      intro address inside
      rcases List.mem_cons.mp inside with same | following
      · subst address;rw [receipt.before]
      · have bounded := ih address following
        have appended := congrArg List.length (receipt.actual_prefix scope)
        simp only [List.length_append,List.length_singleton] at appended
        omega

theorem no_successful_microstep_reuses_a_prior_invoice_address : run.paymentAddresses.Nodup := by
  induction run with
  | done | blocked => exact List.nodup_nil
  | next scope accumulator head tail receipt later ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro reused
        have bounded := later.every_payment_address_starts_after_the_original_prefix _ reused
        have appended := congrArg List.length (receipt.actual_prefix scope)
        simp only [List.length_append,List.length_singleton,receipt.before] at appended bounded
        omega
      · exact ih

structure Blocked (run : Run scope state) where
  before : OriginalScope point
  accumulator : Nat
  head : Command
  tail : List Command
  attempt : Attempt before
  failure : attempt.failed
  endpoint : run.finalScope = attempt.after
  residual : run.finalState = ⟨accumulator,head::tail⟩

inductive Resolution (run : Run scope state) where
  | complete (finished : run.finalState.commands = [])
  | blocked (failure : Blocked run)

def resolve : {scope : OriginalScope point} → {state : State} →
    (run : Run scope state) → Resolution run
  | _,_,.done .. => .complete rfl
  | _,_,.blocked scope accumulator head tail attempt failed =>
      .blocked ⟨scope,accumulator,head,tail,attempt,failed,rfl,rfl⟩
  | _,_,.next _ _ _ _ _ later =>
      match later.resolve with
      | .complete finished => .complete finished
      | .blocked failure => .blocked ⟨failure.before,failure.accumulator,failure.head,failure.tail,
          failure.attempt,failure.failure,failure.endpoint,failure.residual⟩
end Run

inductive Operation where
  | add (left right : Nat)
  | multiply (left right : Nat)
  | maximum (left right : Nat)
  deriving DecidableEq

def Operation.initial : Operation → State
  | .add left right => ⟨left,[.add right]⟩
  | .multiply left right => ⟨0,[.multiply left right]⟩
  | .maximum left right => ⟨0,[.maximum left right]⟩

def Operation.value : Operation → Nat
  | .add left right => left + right
  | .multiply left right => left * right
  | .maximum left right => max left right

theorem Operation.initial_value (operation : Operation) : operation.initial.value = operation.value := by
  cases operation <;> simp [initial,State.value,Command.value,value]

structure Computation (scope : OriginalScope point) (operation : Operation) where
  private mk ::
  execution : Run scope operation.initial
  generated : execution = execute scope operation.initial

def compute (scope : OriginalScope point) (operation : Operation) : Computation scope operation :=
  ⟨execute scope operation.initial,rfl⟩

inductive Answer {scope : OriginalScope point} {operation : Operation} (made : Computation scope operation) where
  | value (result : Nat) (observed : result = made.execution.finalState.accumulator)
      (exact : result = operation.value) (completed : made.execution.finalState.commands = [])
  | blocked (failure : Run.Blocked made.execution)

def Computation.answer {scope : OriginalScope point} {operation : Operation}
    (made : Computation scope operation) : Answer made :=
  match made.execution.resolve with
  | .blocked failure => .blocked failure
  | .complete completed => .value made.execution.finalState.accumulator rfl
      ((made.execution.completed_value_is_the_original_arithmetic completed).trans operation.initial_value) completed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.PaidBudgetArithmetic

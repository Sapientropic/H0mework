import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.BodyPaid
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Arithmetic
set_option autoImplicit false
set_option linter.unusedSimpArgs false
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

-- The pending implementation of each named source read remains separately visible.
inductive Operand where
  | body (query : Work.Query pool)
  | selection (query : Work.Query pool)
def Operand.value : Operand pool → Nat
  | .body query => Body.atom query
  | .selection query => Work.atomBudget pool query

inductive Opcode where
  | add | multiply | maximum
  deriving DecidableEq
def Opcode.operation (left right : Nat) : Opcode → PaidBudgetArithmetic.Operation
  | .add => .add left right
  | .multiply => .multiply left right
  | .maximum => .maximum left right

inductive Expression where
  | literal (value : Nat)
  | source (field : Operand pool)
  | binary (opcode : Opcode) (left right : Expression)

def Expression.value : Expression pool → Nat
  | .literal n => n
  | .source field => field.value pool
  | .binary opcode left right => (opcode.operation left.value right.value).value
variable {pool}
def plus (left right : Expression pool) := Expression.binary .add left right
def times (left right : Expression pool) := Expression.binary .multiply left right
def largest (left right : Expression pool) := Expression.binary .maximum left right
local infixl:65 " ⊞ " => plus
local infixl:70 " ⊠ " => times
def lit (n : Nat) : Expression pool := .literal n

def length {α : Type} : List α → Expression pool
  | [] => lit 0
  | _::tail => length tail ⊞ lit 1
theorem length_value {α : Type} (items : List α) : (length (pool := pool) items).value = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => change (length tail).value+1 = tail.length+1;rw [ih]

def bodyLength {α : Type} (items : List α) : Expression pool := lit 3 ⊠ length items ⊞ lit 2
theorem bodyLength_value {α : Type} (items : List α) : (bodyLength (pool := pool) items).value = BodySource.length items := by
  change 3*(length items).value+2 = 3*items.length+2
  rw [length_value]

def ceiling {α : Type} (field : α → Expression pool) : List α → Expression pool
  | [] => lit 0
  | head::tail => largest (field head) (ceiling field tail)
theorem ceiling_value {α : Type} (field : α → Expression pool) (items : List α) :
    (ceiling field items).value = Policy.Work.ceiling (fun item => (field item).value) items := by
  induction items with
  | nil => rfl
  | cons head tail ih => change max (field head).value (ceiling field tail).value = max _ _;rw [ih]

def bodyCeiling {α : Type} (field : α → Expression pool) : List α → Expression pool
  | [] => lit 2
  | head::tail => field head ⊞ bodyCeiling field tail ⊞ lit 2
theorem bodyCeiling_value {α : Type} (field : α → Expression pool) (items : List α) :
    (bodyCeiling field items).value = Body.ceiling (fun item => (field item).value) items := by
  induction items with
  | nil => rfl
  | cons head tail ih => change (field head).value+(bodyCeiling field tail).value+2 = _;rw [ih];rfl

variable (pool)
-- Reproduce the source formula's cost-algebra (+1 per original operator).
variable {pool}
def costPlus (a b : Expression pool) := a ⊞ b ⊞ lit 1

local infixl:65 " ⨁ " => costPlus
local infixl:70 " ⨂ " => costPlus

variable (pool)
def bodyFormula : Expression pool :=
  let count := bodyLength (sections pool)
  let atoms := lit 1 ⊞ bodyCeiling (fun query => .source (.body query)) (Work.queries pool)
  let tables := bodyCeiling (fun index : Index prepared => bodyLength (Comparison.tables pool index)) (keys prepared)
  let words := bodyCeiling (fun index : Index prepared => bodyLength (Work.capabilityWords index)) (keys prepared)
  let admission := bodyLength (rows pool) ⨂ (lit 1 ⨁ lit 1)
  let benefit := bodyLength (keys prepared) ⨂ (lit 1 ⨂ (lit 1 ⨁ lit 1 ⨁ lit 1 ⨂ lit 1 ⨂ (lit 1 ⨁ lit 1)) ⨁ lit 1)
  let strict := lit 1 ⨂ lit 1 ⨁ lit 1
  let verification := lit 1 ⨁ lit 1 ⨁ (lit 1 ⨂ (lit 1 ⨁ lit 1 ⨁ lit 1))
  let result := lit 1 ⨂ (lit 1 ⨁ lit 1) ⨁ lit 1 ⨂ (lit 1 ⨁ lit 1) ⨁ lit 1 ⨁ lit 1 ⨂ lit 1 ⨁ lit 1
  count ⊞ atoms ⊞ tables ⊞ words ⊞ admission ⊞ benefit ⊞ strict ⊞ verification ⊞ result

theorem bodyFormula_value : (bodyFormula pool).value = Body.units pool := by
  simp only [bodyFormula,plus,times,Expression.value,Opcode.operation,PaidBudgetArithmetic.Operation.value,
    costPlus,bodyLength_value,bodyCeiling_value,Operand.value]
  rfl

def selection : Expression pool :=
  let count := length (sections pool)
  let atoms := ceiling (fun query => .source (.selection query)) (Work.queries pool)
  let tables := ceiling (fun index : Index prepared => length (Comparison.tables pool index)) (keys prepared)
  let words := ceiling (fun index : Index prepared => length (Work.capabilityWords index)) (keys prepared)
  let admission := length (rows pool) ⊠ (atoms ⊞ lit 1)
  let benefit := length (keys prepared) ⊠ (tables ⊠ (atoms ⊞ lit 3 ⊞ lit 2 ⊠ words ⊠ (atoms ⊞ lit 1)) ⊞ lit 1)
  let strict := lit 2 ⊠ benefit ⊞ lit 2
  let verification := admission ⊞ lit 1 ⊞ (count ⊠ (admission ⊞ strict ⊞ lit 3))
  count ⊠ (admission ⊞ lit 1) ⊞ count ⊠ (strict ⊞ lit 1) ⊞ verification ⊞ count ⊠ admission ⊞ lit 1

theorem selection_value : (selection pool).value = Work.workBudget pool := by
  simp only [selection,plus,times,Expression.value,Opcode.operation,PaidBudgetArithmetic.Operation.value,
    length_value,ceiling_value,Operand.value]
  rfl

def joint := bodyFormula pool ⊞ selection pool
theorem joint_value : (joint pool).value = Body.units pool + Work.workBudget pool := by
  change (bodyFormula pool).value+(selection pool).value = _
  rw [bodyFormula_value,selection_value]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter

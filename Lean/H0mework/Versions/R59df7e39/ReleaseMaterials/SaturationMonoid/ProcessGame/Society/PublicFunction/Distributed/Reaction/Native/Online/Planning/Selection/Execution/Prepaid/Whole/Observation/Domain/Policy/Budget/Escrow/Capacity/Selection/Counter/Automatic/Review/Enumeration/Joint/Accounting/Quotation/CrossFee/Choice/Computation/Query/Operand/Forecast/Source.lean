import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}

namespace WholeTarget
variable {driver : Feedback.Input seed.source.code} {cursor : Online.Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)} {n : Nat}
  {reference : Term cursor} {actor : P} {position : Nat}
  (scope : Whole.Scope cursor pricing n reference actor position) (span : Nat)
  (intent : Whole.Intent scope) (rival : Opponent cursor.source.val.code)

def state : Feedback.State cursor.source.val.code := match intent with
  | .keep => cursor.state
  | .paid plan => plan.point.state
def control : Feedback.Residual.Schedule cursor.source.val.code := match intent with
  | .keep => Planning.schedule cursor reference
  | .paid plan => Planning.schedule plan.point plan.term
def horizon : Nat := match intent with | .keep => span | .paid _ => n
def budget : Nat := match intent with | .keep => cursor.input.budget | .paid plan => plan.point.input.budget
def driving : Feedback.Input cursor.source.val.code := ⟨rival,budget scope intent⟩
def install (words : List (RawEvent P G O (Mandate.State P T) I)) := match intent with
  | .keep => cursor.install words
  | .paid plan => plan.point.install words
abbrev Start := Forecast.Cursor cursor.source.val.code (control scope intent) (driving scope intent rival) (state scope intent) (horizon scope span intent)
def start : Start scope span intent rival := Forecast.initial _ _ _ _ _
abbrev Done := Forecast.Completed cursor.source.val.code (control scope intent) (driving scope intent rival) (state scope intent) (horizon scope span intent)
def source (completed : Done scope span intent rival) : Future.Recovery.SameCodeTarget cursor.model :=
  ⟨install scope intent completed.words,by cases intent <;> rfl⟩

theorem source_exact (completed : Done scope span intent rival) :
    source scope span intent rival completed = Whole.target scope span intent rival := by
  apply Subtype.ext
  dsimp only [source]
  rw [completed.words_exact]
  cases intent <;> rfl

-- Downstream evaluation consumes the emitted source; its own internal work is not settled here.
def render (emitted : Future.Recovery.SameCodeTarget cursor.model) : Planning.Tensor cursor :=
  let bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I) :=
    ⟨seed.base,seed.scope,emitted.val,emitted.indexed.property.1,emitted.indexed.property.2⟩
  ⟨emitted.property ▸ Window.evaluate bound cursor.depth (Whole.extent scope span intent),
    Whole.restoration (pricing := pricing) emitted (Whole.count scope span intent)⟩

def tensor (completed : Done scope span intent rival) : Planning.Tensor cursor :=
  render scope span intent (source scope span intent rival completed)

theorem tensor_exact (completed : Done scope span intent rival) :
    tensor scope span intent rival completed = Whole.tensor scope span intent rival := by
  exact congrArg (render scope span intent) (source_exact scope span intent rival completed)

def produce (capacity : Nat) := Forecast.run capacity (start scope span intent rival)
theorem produces_when_covered (capacity : Nat) (enough : horizon scope span intent ≤ capacity) :
    (produce scope span intent rival capacity).endpoint.completed.isSome = true :=
  Forecast.run_sufficient _ _ enough

theorem emitted_work (capacity : Nat) : (produce scope span intent rival capacity).work.length = min capacity (horizon scope span intent) :=
  Forecast.run_work_exact _ _
end WholeTarget

variable {input : Input seed} {prepared : Prepared input} {position : Nat}
  {pool : List (Offer (prepared := prepared) (position := position))}
  (cache : Tables.Completed pool) (index : Index prepared)

structure Address where
  table : Fin (cache.at index).length
  policy : Fin pool.length
namespace Address
variable {cache index}
def pick (address : Address cache index) := pool[address.policy]
def actualTable (address : Address cache index) := (cache.at index)[address.table]
def rival (address : Address cache index) := Choice.rival pool index address.actualTable
def view (address : Address cache index) := address.pick.view index
abbrev Start (address : Address cache index) := WholeTarget.Start address.view.scope input.span address.view.intent address.rival
abbrev Done (address : Address cache index) := WholeTarget.Done address.view.scope input.span address.view.intent address.rival
def start (address : Address cache index) : address.Start := WholeTarget.start address.view.scope input.span address.view.intent address.rival
def tensor (address : Address cache index) (completed : address.Done) :=
  WholeTarget.tensor address.view.scope input.span address.view.intent address.rival completed

theorem tensor_exact (address : Address cache index) (completed : address.Done) :
    address.tensor completed = (address.pick.view index).tensor address.rival :=
  WholeTarget.tensor_exact address.view.scope input.span address.view.intent address.rival completed

structure Session (address : Address cache index) (capacity : Nat) where
  private mk ::
  run : Forecast.Run address.start capacity
  generated : run = Forecast.run capacity address.start

def produce (address : Address cache index) (capacity : Nat) : Session address capacity :=
  ⟨Forecast.run capacity address.start,rfl⟩

structure Materialized (address : Address cache index) where
  private mk ::
  source : address.Done
  tensor : Planning.Tensor (Policy.initial input prepared.saved[index].point)
  generated : tensor = address.tensor source

def Session.completed {address : Address cache index} {capacity : Nat} (session : Session address capacity) : Option (Materialized address) :=
  match session.run.endpoint.completed with
  | none => none
  | some actual => some ⟨actual,address.tensor actual,rfl⟩

theorem Materialized.exact {address : Address cache index} (made : Materialized address) :
    made.tensor = (address.pick.view index).tensor address.rival :=
  made.generated.trans (address.tensor_exact made.source)

-- Both arms use the same table ordinal; all original responsibility fields are retained.
def pairQuery (left right : Address cache index) (sameTable : left.table = right.table)
    (new : Materialized left) (previous : Materialized right) :
    Query.Code (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (.truth
      (Full.TensorLe (Policy.initial input prepared.saved[index].point)
        ((left.pick.view index).tensor left.rival) ((right.pick.view index).tensor left.rival))) :=
  Query.Code.transport (by
    have sameRival : left.rival = right.rival := congrArg (fun table => Choice.rival pool index ((cache.at index)[table])) sameTable
    rw [new.exact,previous.exact,sameRival])
    (Query.Source.tensor (Policy.initial input prepared.saved[index].point) new.tensor previous.tensor)

end Address
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast

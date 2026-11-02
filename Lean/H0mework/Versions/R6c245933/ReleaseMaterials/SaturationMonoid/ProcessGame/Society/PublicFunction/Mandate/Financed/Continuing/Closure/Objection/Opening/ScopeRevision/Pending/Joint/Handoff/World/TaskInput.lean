import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
open Institutions.Capitalism.Universal.Source.Program

/-- An earlier received source, kept with its own actual route to the current packet. -/
structure ReceivedBasis (packet : Packet) where
  private mk ::
  first : Packet
  pending : List Action
  private route : Unit → Input.Event.Evolution first packet

def ReceivedBasis.native {packet : Packet} (basis : ReceivedBasis packet) :
    Input.Event.Evolution basis.first packet := basis.route ()

def ReceivedBasis.advance {first last : Packet} (basis : ReceivedBasis first)
    (native : Unit → Input.Event.Evolution first last) : ReceivedBasis last :=
  ⟨basis.first,basis.pending,fun _ => .append basis.native (native ())⟩

/-- The current received occurrence and every earlier basis on this actual input history. -/
structure FutureOrigin (packet : Packet) where
  private mk ::
  first : Packet
  pending : List Action
  private route : Unit → Input.Event.Evolution first packet
  ancestors : List (ReceivedBasis packet)

def FutureOrigin.native {packet : Packet} (origin : FutureOrigin packet) :
    Input.Event.Evolution origin.first packet := origin.route ()

def FutureOrigin.basis {packet : Packet} (origin : FutureOrigin packet) : ReceivedBasis packet :=
  ⟨origin.first,origin.pending,fun _ => origin.native⟩

def FutureOrigin.receive
    {cursor : Input.Challenge.Redress.Shared.Iteration.Requests.Cursor} {word : List Action}
    (response : Input.Challenge.Redress.Shared.Iteration.Requests.Result cursor word) :
    FutureOrigin response.next.saved :=
  ⟨response.next.saved,response.report.residual,fun _ => .same _,[]⟩

/-- A new response adds its own basis and carries all previous ones along that same response. -/
def FutureOrigin.receiveAfter
    {cursor : Input.Challenge.Redress.Shared.Iteration.Requests.Cursor} {word : List Action}
    (earlier : Option (FutureOrigin cursor.saved))
    (response : Input.Challenge.Redress.Shared.Iteration.Requests.Result cursor word) :
    FutureOrigin response.next.saved :=
  match earlier with
  | none => receive response
  | some origin =>
      ⟨response.next.saved,response.report.residual,fun _ => .same _,
        (origin.basis :: origin.ancestors).map (fun basis => basis.advance (fun _ => response.native))⟩

def FutureOrigin.advance {first last : Packet} (origin : FutureOrigin first)
    (native : Unit → Input.Event.Evolution first last) : FutureOrigin last :=
  ⟨origin.first,origin.pending,fun _ => .append origin.native (native ()),
    origin.ancestors.map (fun basis => basis.advance native)⟩

theorem FutureOrigin.receive_uses_the_same_response
    {cursor : Input.Challenge.Redress.Shared.Iteration.Requests.Cursor} {word : List Action}
    (response : Input.Challenge.Redress.Shared.Iteration.Requests.Result cursor word) :
    (receive response).first = response.next.saved ∧
      (receive response).pending = response.report.residual := ⟨rfl,rfl⟩

theorem FutureOrigin.advance_keeps_the_received_basis {first last : Packet} (origin : FutureOrigin first)
    (native : Unit → Input.Event.Evolution first last) :
    (origin.advance native).first = origin.first ∧ (origin.advance native).pending = origin.pending := ⟨rfl,rfl⟩

theorem FutureOrigin.new_response_keeps_every_previous_basis
    {cursor : Input.Challenge.Redress.Shared.Iteration.Requests.Cursor} {word : List Action}
    (origin : FutureOrigin cursor.saved)
    (response : Input.Challenge.Redress.Shared.Iteration.Requests.Result cursor word) :
    (receiveAfter (some origin) response).ancestors =
      (origin.basis :: origin.ancestors).map (fun basis => basis.advance (fun _ => response.native)) := rfl

theorem FutureOrigin.advance_keeps_every_ancestor {first last : Packet} (origin : FutureOrigin first)
    (native : Unit → Input.Event.Evolution first last) :
    (origin.advance native).ancestors = origin.ancestors.map (fun basis => basis.advance native) := rfl

theorem FutureOrigin.advance_uses_the_exact_actual_path {first last : Packet} (origin : FutureOrigin first)
    (native : Unit → Input.Event.Evolution first last) :
    (origin.advance native).native = .append origin.native (native ()) := rfl

/-- Raw World input is indexed by its actual law and scope. A public recall
birth may change the native machine while retaining these same input origins. -/
inductive TaskInput : {Party Good Port Technology Instrument : Type} →
    [DecidableEq Party] → [DecidableEq Good] → [DecidableEq Port] →
    [DecidableEq Technology] → [DecidableEq Instrument] →
    RawLaw Party Good Port Technology Instrument →
    Mandate.Scope (Party := Party) (Good := Good) (Port := Port) → Type where
  | actual {epoch : Epoch} (inventory : Inventory epoch) : TaskInput base epoch.scope
  | received {epoch : Epoch} (inventory : Inventory epoch)
      (origin : FutureOrigin (⟨epoch,inventory⟩ : Packet)) : TaskInput base epoch.scope

namespace TaskInput
/-- Input ingestion is quoted from existing positions, before evaluating a
candidate. This descriptor contains no response, report or funding verdict. -/
structure Schema where
  history : List Nat
  pastGrants : Nat
  pastChallenges : Nat
  pastServices : Nat
  grants : Nat
  challenges : Nat
  services : Nat
  financialSlots : Nat
  deriving DecidableEq, Repr

def Schema.units (schema : Schema) : Nat :=
  1 + (schema.history.map (1 + ·)).sum + schema.pastGrants + schema.pastChallenges +
    schema.pastServices + schema.grants + schema.challenges + schema.services + schema.financialSlots

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

def schema (input : TaskInput law scope) : Schema :=
  match input with
  | .actual inventory | .received inventory _ =>
      ⟨inventory.inputs.map List.length,inventory.pastGrants.length,inventory.pastChallenges.length,
        inventory.pastServices.length,inventory.grants.length,inventory.objections.length,
        scope.task.slots.length,inventory.finance.current.slots.length⟩

def packet (input : TaskInput law scope) : Packet :=
  match input with
  | .actual inventory | .received inventory _ => ⟨_,inventory⟩

def futureOrigin (input : TaskInput law scope) : Option (FutureOrigin input.packet) :=
  match input with
  | .actual _ => none
  | .received _ origin => some origin

def units (input : TaskInput law scope) : Nat := input.schema.units

theorem units_positive (input : TaskInput law scope) : 0 < input.units := by
  unfold units Schema.units
  omega

theorem every_actual_input_position_is_quoted {epoch : Epoch} (inventory : Inventory epoch) :
    (schema (.actual inventory)).history = inventory.inputs.map List.length ∧
    (schema (.actual inventory)).pastGrants = inventory.pastGrants.length ∧
    (schema (.actual inventory)).pastChallenges = inventory.pastChallenges.length ∧
    (schema (.actual inventory)).pastServices = inventory.pastServices.length ∧
    (schema (.actual inventory)).grants = inventory.grants.length ∧
    (schema (.actual inventory)).challenges = inventory.objections.length ∧
    (schema (.actual inventory)).services = epoch.scope.task.slots.length ∧
    (schema (.actual inventory)).financialSlots = inventory.finance.current.slots.length :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end TaskInput
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

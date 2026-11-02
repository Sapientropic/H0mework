import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)) (n : Nat)
  (reference : Term cursor)

/-- The invoice measures explicit control transitions. Native evaluation obligations remain separate. -/
def IsWorkFee (actor : Party) (request : Future.Recovery.Action cursor.model) : Prop :=
  request.signer = actor ∧ (∀ consent ∈ request.consents,consent = actor) ∧
  ¬ Mandate.TaskUse cursor.model.scope request ∧
  match request.operation with
  | .use bearer bundle .external => bearer = actor ∧ NonnegativeBundle Good bundle ∧
      ∃ good ∈ cursor.source.val.code.goods,0 < amount Good bundle good
  | _ => False
instance (actor : Party) (request : Future.Recovery.Action cursor.model) : Decidable (IsWorkFee cursor actor request) := by
  unfold IsWorkFee
  cases request.operation <;> try infer_instance
  rename_i bearer bundle purpose
  cases purpose <;> infer_instance

def feeAt (actor : Party) (position : Nat) : Option (Future.Recovery.Action cursor.model) :=
  match cursor.source.val.code.actions[position]? with
  | none => none
  | some fee => if IsWorkFee cursor actor fee then some fee else none

variable (made : Compilation cursor pricing n reference)
abbrev invoice (fee : Future.Recovery.Action cursor.model) := List.replicate (controlSteps cursor (checkedWork cursor pricing n made)) fee
abbrev path (fee : Future.Recovery.Action cursor.model) := Mandate.Replay.compile cursor.model.base cursor.model.scope
  cursor.state.current (invoice cursor pricing n reference made fee)

inductive Bill (actor : Party) (position : Nat) where
  | unpriced (absent : feeAt cursor actor position = none)
  | paid (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee)
      (accepted : (path cursor pricing n reference made fee).succeeded = true)
  | refused (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee)
      (broken : (path cursor pricing n reference made fee).succeeded = false)

def bill (actor : Party) (position : Nat) : Bill cursor pricing n reference made actor position :=
  match registered : feeAt cursor actor position with
  | none => .unpriced registered
  | some fee => if paid : (path cursor pricing n reference made fee).succeeded = true then .paid fee registered paid
      else .refused fee registered (Bool.eq_false_iff.mpr paid)

namespace Bill
variable {cursor pricing n reference made} {actor : Party} {position : Nat}
  (receipt : Bill cursor pricing n reference made actor position)
def endpoint : Cursor seed driver := match receipt with
  | .unpriced _ => cursor
  | .paid fee .. | .refused fee .. => cursor.submit (path cursor pricing n reference made fee).output

def status : Nat := match receipt with | .unpriced _ => 0 | .paid .. => 1 | .refused .. => 2
end Bill

variable {cursor pricing n reference}
structure Settlement (cursor : Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (n : Nat) (reference : Term cursor) (actor : Party) (position : Nat) where
  private mk ::
  compilation : Compilation cursor pricing n reference
  compiled : compilation = compile cursor pricing n reference
  receipt : Bill cursor pricing n reference compilation actor position
  charged : receipt = bill cursor pricing n reference compilation actor position

def settle (cursor : Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (n : Nat) (reference : Term cursor) (actor : Party) (position : Nat) : Settlement cursor pricing n reference actor position :=
  let compiled := compile cursor pricing n reference
  ⟨compiled,rfl,bill cursor pricing n reference compiled actor position,rfl⟩

namespace Settlement
variable {actor : Party} {position : Nat} (settled : Settlement cursor pricing n reference actor position)
abbrev endpoint := settled.receipt.endpoint
abbrev nativePending := nativeObligations cursor (checkedWork cursor pricing n settled.compilation)

theorem an_actual_bill_does_not_erase_its_native_computation_obligations :
    settled.nativePending = nativeObligations cursor (checkedWork cursor pricing n settled.compilation) := rfl

theorem every_paid_control_invoice_is_the_actual_source_event
    (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee)
    (paid : (path cursor pricing n reference settled.compilation fee).succeeded = true)
    (same : settled.receipt = .paid fee registered paid) :
    (settled.endpoint.source.val.actualExecution cursor.depth).submitted = (path cursor pricing n reference settled.compilation fee).output ∧
    (path cursor pricing n reference settled.compilation fee).consumed = invoice cursor pricing n reference settled.compilation fee := by
  have split := (path cursor pricing n reference settled.compilation fee).original_split
  have empty := Future.Recovery.Search.no_residual_after_success cursor.model (path cursor pricing n reference settled.compilation fee) paid
  rw [empty,List.append_nil] at split
  refine ⟨?_,split⟩
  change ((settled.receipt.endpoint).source.val.actualExecution cursor.depth).submitted = _
  rw [same]
  exact cursor.submit_is_the_actual_word _
end Settlement
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution

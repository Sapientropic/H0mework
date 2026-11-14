import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.BirthAction
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.RequestRelay
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.BirthReceipt

open SourceOperationEffects SourceOperationScalarInventoryLift
open SourceInventoryExecutionFeed (Inventory eventItems requests)
open ActualNativeRelationTransport (OccurrenceBlock)
namespace Stock
export ActualNativeRelationTransport.AS (stockScalar stockDecodedEnvironment)
export ActualNativeRelationTransport.SourceInventoryBlock (source)
end Stock

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
attribute [local instance] familyGroups
variable (factory : SF.Factory W X s)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (prior : Inventory (V := L.Value W packet.1) (X := X) (s := s))
variable (present : packet.2.1.1.inventory = some prior)
variable (event : Fin prior.trace.length)

local notation "selectedFrame" => selected factory packet
set_option quotPrecheck false in
local notation "nativeCfg" => (nativePacket factory packet).2.2.1
set_option quotPrecheck false in
local notation "carriedEvents" => prior.trace.map (sourceLiftEvent packet)
local notation "writtenSource" => Stock.stockScalar (selectedFrame) (nativeCfg)

include present in
/-- The carried event selects its original Feed execution before the birth stock is appended. -/
def birthRequest (item : Fin (eventItems ((carriedEvents).get (Fin.cast (List.length_map _).symm event))).length) :
    SourceReceiptOccurrence.ExecutionAt (sourceBorn factory packet) := by
  let source : Inventory (V := L.Value W (packet.1+1)) (X := packet.2.2.1.LowVar) (s := s) :=
    writtenSource
  let environment : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar :=
    Stock.stockDecodedEnvironment (selectedFrame) (nativeCfg)
  let block := Stock.source factory packet prior present
  let location : Fin (requests source).length := block.requestIndex 0 (Fin.cast (List.length_map _).symm event) item
  let all := requests source
  let request := all.get location
  have split : requests source = all.take location.val ++ request :: all.drop (location.val+1) :=
    (List.take_append_drop location.val all).symm.trans
      (congrArg (all.take location.val ++ ·) (List.drop_eq_getElem_cons location.isLt))
  exact {
    stock := bornStock factory packet
    installed := born_inventory factory packet
    decoder := environment
    decoder_source := ActualNativeRelationTransport.decoded_environment (selectedFrame) (nativeCfg)
    request := request
    paid := SourceInventoryExecutionFeed.receipt environment request
    segment := SourceInventoryExecutionFeed.ReceiptOccurrence.fromSplit
      environment source (all.take location.val) (all.drop (location.val+1)) request split }

/-- The literal executed request uses the same signed support address of the carried event. -/
theorem birth_request_read (item : Fin (eventItems ((carriedEvents).get (Fin.cast (List.length_map _).symm event))).length) :
    (birthRequest factory packet prior present event item).request =
      ⟨(Stock.source factory packet prior present).before.length+event.val,
        (carriedEvents).get (Fin.cast (List.length_map _).symm event),
        ((eventItems ((carriedEvents).get (Fin.cast (List.length_map _).symm event))).get item).1,
        ((eventItems ((carriedEvents).get (Fin.cast (List.length_map _).symm event))).get item).2⟩ := by
  simpa only [birthRequest, requests, Nat.zero_add, Fin.val_cast] using
    (Stock.source factory packet prior present).request_index_read 0 (Fin.cast (List.length_map _).symm event) item

/-- The actual birth action, before the first newborn micro-step, supplies both paid coordinates. -/
def birthRequestAction (item : Fin (eventItems ((carriedEvents).get (Fin.cast (List.length_map _).symm event))).length) : PairValue (L.Value W (packet.1+1)) s :=
  let request := (birthRequest factory packet prior present event item).request
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selectedFrame).activeEnvironment
  request.coefficient • (liftExpr request.expression).eval (pairEnvironment before (birthIncrement factory packet))

theorem birth_request_action_paid (item : Fin (eventItems ((carriedEvents).get (Fin.cast (List.length_map _).symm event))).length) :
    let execution := birthRequest factory packet prior present event item
    let action := birthRequestAction factory packet prior present event item
    execution.request.coefficient • execution.request.expression.eval execution.decoder = action.1+action.2 := by
  intro execution action
  let before : Env (L.Value W (packet.1+1)) packet.2.2.1.LowVar := (selectedFrame).activeEnvironment
  let increment := birthIncrement factory packet
  have decoded : before+increment = execution.decoder :=
    (birth_decoded_environment factory packet).trans execution.decoder_source
  change execution.request.coefficient • execution.request.expression.eval execution.decoder =
    (execution.request.coefficient •
      (liftExpr execution.request.expression).eval (pairEnvironment before increment)).1 +
    (execution.request.coefficient •
      (liftExpr execution.request.expression).eval (pairEnvironment before increment)).2
  rw [eval_liftExpr, Prod.smul_mk, ← smul_add, ← Expr.eval_update, decoded]

end ActualCofinalSourceAction.BirthReceipt
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

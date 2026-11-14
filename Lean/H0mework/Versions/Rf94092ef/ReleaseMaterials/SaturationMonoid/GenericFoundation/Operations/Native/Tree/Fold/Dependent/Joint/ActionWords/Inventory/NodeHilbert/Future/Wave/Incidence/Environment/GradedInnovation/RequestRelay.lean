import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.ColumnWriteback
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory.Born
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Origin.Index

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport.OccurrenceBlock

variable {A : Type u} {chunk target : List A}

def slot (block : OccurrenceBlock chunk target) (index : Fin chunk.length) : Fin target.length :=
  ⟨block.before.length+index.val, by
    have length := congrArg List.length block.trace_eq
    simp only [List.length_append] at length
    have bound := index.isLt
    omega⟩

theorem slot_read (block : OccurrenceBlock chunk target) (index : Fin chunk.length) :
    target.get (block.slot index) = chunk.get index := by
  apply Option.some.inj
  refine (List.getElem?_eq_getElem (block.slot index).isLt).symm.trans ?_
  let position := block.before.length+index.val
  refine (congrArg (fun events : List A => events[position]?) block.trace_eq).trans ?_
  change (block.before ++ chunk ++ block.after)[block.before.length+index.val]? = _
  rw [List.append_assoc,
    List.getElem?_append_right (Nat.le_add_right block.before.length index.val), Nat.add_sub_cancel_left,
    List.getElem?_append_left index.isLt, List.getElem?_eq_getElem index.isLt]
  rfl

open SourceOperationEffects
namespace F
export SourceInventoryExecutionFeed (Event eventItems requestsFrom requestIndexAt request_index_at_read)
end F

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable {source targetEvents : List (F.Event (V := V) (X := X) (s := s))}
variable (block : OccurrenceBlock source targetEvents) (start : Nat)
variable (event : Fin source.length) (item : Fin (F.eventItems (source.get event)).length)

/-- Exact event addresses, with local support addresses, survive an enclosing occurrence block. -/
def requestIndex : Fin (F.requestsFrom start targetEvents).length :=
  F.requestIndexAt start targetEvents (block.slot event)
    (Fin.cast (congrArg (fun e => (F.eventItems e).length) (block.slot_read event).symm) item)

private theorem event_item_read {a b : F.Event (V := V) (X := X) (s := s)}
    (same : a = b) (index : Fin (F.eventItems a).length) :
    (F.eventItems b).get (Fin.cast (congrArg (fun e => (F.eventItems e).length) same) index) =
      (F.eventItems a).get index := by
  cases same
  rfl

theorem request_index_read :
    (F.requestsFrom start targetEvents).get (block.requestIndex start event item) =
      ⟨start+(block.before.length+event.val), source.get event,
        ((F.eventItems (source.get event)).get item).1,
        ((F.eventItems (source.get event)).get item).2⟩ := by
  rw [requestIndex, F.request_index_at_read, event_item_read (block.slot_read event).symm]
  rw [block.slot_read event]
  rfl

end ActualNativeRelationTransport.OccurrenceBlock

namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated

open SourceOperationEffects SourceOperationScalarInventoryLift CofinalHistorySettlement
open ActualNativeRelationTransport (OccurrenceBlock)
namespace Feed
export SourceInventoryExecutionFeed (Event eventItems)
end Feed
namespace Block
export ActualNativeRelationTransport.SourceInventoryBlock (born)
end Block
namespace Action
export ActualCofinalSourceAction (sourceLiftEvent sourceBorn bornStock born_inventory packetTransport)
end Action

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups

abbrev RelayPacket (Y : J.Slot → Type u) := AS.AdmissionPacket (W := W K) (X := Y) (s := .joint)
abbrev RelayEvent {Y : J.Slot → Type u} (packet : RelayPacket (K := K) Y) :=
  Feed.Event (V := L.Value (W K) packet.1) (X := Y) (s := .joint)

private def packetStock {Y : J.Slot → Type u} (packet : RelayPacket (K := K) Y) :
    SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := Y) (s := .joint) :=
  T.preserve packet.2.1.1.inventory (RootedAccountedUnfolding.zero
    (PresentedRelationEventAt.generator packet.2.1.1.registered.input.expression))

variable (read : J.Orbit →ₗ[ℤ] K)
private def bornStockBlock (packet : RelayPacket (K := K) X)
    (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint))
    (present : packet.2.1.1.inventory = some prior) :
    OccurrenceBlock (prior.trace.map (Action.sourceLiftEvent packet))
      (packetStock (Action.sourceBorn (factory read) packet)).trace := by
  let native := Action.sourceBorn (factory read) packet
  let installed : SourceInventoryExecutionFeed.Inventory
      (V := L.Value (W K) (packet.1+1)) (X := packet.2.2.1.LowVar) (s := .joint) :=
    Action.bornStock (factory read) packet
  let block := Block.born (factory read) packet prior present
  let anchor : Feed.Event (V := L.Value (W K) (packet.1+1)) (X := packet.2.2.1.LowVar) (s := .joint) :=
    .generator native.2.1.1.registered.input.expression
  refine ⟨installed.root :: block.before, block.after ++ [anchor], ?_⟩
  have written := Action.born_inventory (factory read) packet
  change native.2.1.1.inventory = some installed at written
  change (packetStock native).trace = _
  unfold packetStock
  rw [written]
  change installed.root :: (installed.trace ++ [anchor]) = _
  refine (congrArg (fun trace : List (Feed.Event (V := L.Value (W K) (packet.1+1))
    (X := packet.2.2.1.LowVar) (s := .joint)) => installed.root :: (trace ++ [anchor])) block.trace_eq).trans ?_
  simp only [List.cons_append, List.append_assoc]

private def transportStockBlock {Y Z : J.Slot → Type u} {C : Type u}
    (packet : RelayPacket (K := K) Y) (next : RelayPacket (K := K) Z)
    (language : Y = Z) (literal : Action.packetTransport language packet = next)
    (source : List C) (lift : C → RelayEvent (K := K) packet)
    (block : OccurrenceBlock (source.map lift) (packetStock packet).trace) :
    Σ mapEvent : C → RelayEvent (K := K) next, OccurrenceBlock (source.map mapEvent) (packetStock next).trace := by
  cases language
  cases literal
  exact ⟨lift, block⟩

omit [InnerProductSpace ℂ K] in
private theorem transport_stock_event {Y Z : J.Slot → Type u} {C : Type u}
    (packet : RelayPacket (K := K) Y) (next : RelayPacket (K := K) Z)
    (language : Y = Z) (literal : Action.packetTransport language packet = next)
    (source : List C) (lift : C → RelayEvent (K := K) packet)
    (block : OccurrenceBlock (source.map lift) (packetStock packet).trace)
    (event : C) :
    HEq ((transportStockBlock packet next language literal source lift block).1 event) (lift event) := by
  cases language
  cases literal
  rfl

variable (packet next : RelayPacket (K := K) X)
variable (literal : next = Action.packetTransport packet.2.2.2.down (Action.sourceBorn (factory read) packet))
variable (prior : SourceInventoryExecutionFeed.Inventory (V := L.Value (W K) packet.1) (X := X) (s := .joint))
variable (present : packet.2.1.1.inventory = some prior)

/-- The old installed block is located in the literal next graded stock. -/
def nextInventoryBlock :
    Σ mapEvent : RelayEvent (K := K) packet → RelayEvent (K := K) next,
      OccurrenceBlock (prior.trace.map mapEvent) (stock (K := K) next.1 (A.epoch next.2.1.1)).trace :=
  transportStockBlock (Action.sourceBorn (factory read) packet) next packet.2.2.2.down
    literal.symm prior.trace
    (Action.sourceLiftEvent packet) (bornStockBlock read packet prior present)

theorem next_inventory_event (event : RelayEvent (K := K) packet) :
    HEq ((nextInventoryBlock read packet next literal prior present).1 event)
      (Action.sourceLiftEvent packet event) :=
  transport_stock_event _ _ _ _ _ _ _ event

private def blockEventIndex (event : Fin prior.trace.length) :
    Fin (prior.trace.map (nextInventoryBlock read packet next literal prior present).1).length :=
  Fin.cast (List.length_map _).symm event

/-- The local item belongs to the carried event in the actual next stock. -/
def relayedEvent (event : Fin prior.trace.length) : RelayEvent (K := K) next :=
  (prior.trace.map (nextInventoryBlock read packet next literal prior present).1).get
    (blockEventIndex read packet next literal prior present event)

theorem relayed_event_lift (event : Fin prior.trace.length) :
    HEq (relayedEvent read packet next literal prior present event)
      (Action.sourceLiftEvent packet (prior.trace.get event)) := by
  change HEq ((prior.trace.map (nextInventoryBlock read packet next literal prior present).1).get
    (blockEventIndex read packet next literal prior present event)) _
  simp only [List.get_eq_getElem, List.getElem_map, blockEventIndex, Fin.val_cast]
  exact next_inventory_event read packet next literal prior present (prior.trace.get event)

variable (event : Fin prior.trace.length)
variable (item : Fin (Feed.eventItems (relayedEvent read packet next literal prior present event)).length)

def relayedRequest : Index (K := K) next.1 (A.epoch next.2.1.1) :=
  (nextInventoryBlock read packet next literal prior present).2.requestIndex 0
    (blockEventIndex read packet next literal prior present event) item

theorem relayed_request_read :
    (requests (K := K) next.1 (A.epoch next.2.1.1)).get (relayedRequest read packet next literal prior present event item) =
      ⟨(nextInventoryBlock read packet next literal prior present).2.before.length+event.val,
        relayedEvent read packet next literal prior present event,
        ((Feed.eventItems (relayedEvent read packet next literal prior present event)).get item).1,
        ((Feed.eventItems (relayedEvent read packet next literal prior present event)).get item).2⟩ := by
  simpa only [requests, SourceInventoryExecutionFeed.requests, relayedRequest, relayedEvent,
    Nat.zero_add, blockEventIndex, Fin.val_cast] using
    (nextInventoryBlock read packet next literal prior present).2.request_index_read 0
      (blockEventIndex read packet next literal prior present event) item

end PaidSourceContentEnvironment.GradedInnovation.Integrated
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFirstFullSourceDynamics
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKBFiniteCalculation.BornInventory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace C
export OriginalKCombReceiptFeedback
  (bFiniteSourceBinding bFiniteSourceTrace arithmeticSourceBinding arithmeticSourceTrace arithmeticSourceInventory
   sourceCalculationInventory sourcePaidInventory frame receipt)
end C
namespace Q
export OriginalKCombFirstFullSource
  (factory data configuration initial born all_inventories)
end Q
namespace D
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg packet)
end D
namespace IC
export ActualCofinalSourceAction
  (AS.AdmissionPacket L.Value L.groups T.liftEvent T.mapped_trace packetTransport sourceLiftEvent
   sourceWordAction source_word_action_relation source_word_action_in_born bornStock born_inventory
   old_event_in_born sourceBorn actual_next_packet D.packetAt selected nativePacket)
end IC
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
  (Value groups)
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock
  (carried_scalar)
end Stock
end L
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor (seed scalar selected)
end SS
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
  (updatedSeed supplied_seed_preserved)
end IP
namespace Pair
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
  (relationWrite disposition relation_write_preserves)
end Pair
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Shared
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end A
namespace PTrace
export SourceOperationPaidRelations (exposure prefixHistory relations_next generators_next)
end PTrace
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue Value) grade target) := L.groups (PairValue Value) grade target

local instance firstPairGroups : ∀ target, AddCommGroup (PairValue (L.Value Value 0) target) :=
  L.groups Value 1

abbrev Packet (Y : Unit → Type) := IC.AS.AdmissionPacket (W := PairValue Value) (X := Y) (s := ())
abbrev StockAt {Y : Unit → Type} (packet : Packet Y) :=
  RootedAccountedUnfolding (PresentedRelationEventAt (Expr (L.Value (PairValue Value) packet.1) Y ()))

/-- Only the actual receiver-language equality transports the complete event tree. -/
def stockTransport {Y Z : Unit → Type} (same : Y = Z) (packet : Packet Y)
    (stock : StockAt packet) : StockAt (IC.packetTransport same packet) := by
  cases same
  exact stock

private theorem transport_inventory {Y Z : Unit → Type} (same : Y = Z) (packet : Packet Y)
    (stock : StockAt packet) (present : packet.2.1.1.inventory = some stock) :
    (IC.packetTransport same packet).2.1.1.inventory = some (stockTransport same packet stock) := by
  cases same
  exact present

private theorem transport_inclusion {Y Z : Unit → Type} (same : Y = Z) (packet : Packet Y)
    (first second : StockAt packet) (preserved : ∀ event ∈ first.trace, event ∈ second.trace) :
    ∀ event ∈ (stockTransport same packet first).trace, event ∈ (stockTransport same packet second).trace := by
  cases same
  exact preserved

private def reindexStock {left right : Packet Var} (same : left = right) (stock : StockAt left) :
    StockAt right := same ▸ stock

private theorem reindex_preserved {left right : Packet Var} (same : left = right) (stock : StockAt left)
    (preserved : ∃ actual, left.2.1.1.inventory = some actual ∧
      ∀ event ∈ stock.trace, event ∈ actual.trace) :
    ∃ actual, right.2.1.1.inventory = some actual ∧
      ∀ event ∈ (reindexStock same stock).trace, event ∈ actual.trace := by
  cases same
  exact preserved

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

abbrev boundSourceExposure := C.sourceCalculationInventory observation nontrivial depth half
abbrev initialSourceExposure := (boundSourceExposure observation nontrivial half depth).map
  (IC.T.liftEvent (W := Value) (X := Var) (s := ()))

private abbrev firstSeed := SS.seed Q.factory 0 (Q.data observation nontrivial half depth)
  (Q.configuration observation nontrivial half) rfl
private abbrev firstSelected := SS.selected Q.factory 0 (Q.data observation nontrivial half depth)
  (Q.configuration observation nontrivial half) rfl

def initialStock := Pair.relationWrite (firstSeed observation nontrivial half depth)
  (A.epoch (firstSelected observation nontrivial half depth))
  (Shared.actualOccurrence (firstSelected observation nontrivial half depth))
  (Pair.disposition (firstSeed observation nontrivial half depth)
    (A.epoch (firstSelected observation nontrivial half depth))
    (Shared.actualOccurrence (firstSelected observation nontrivial half depth)))

theorem initial_inventory : (D.initial observation nontrivial half depth).inventory =
    some (initialStock observation nontrivial half depth) :=
  (Q.all_inventories observation nontrivial half depth).1

/-- The entire bound B execution is carried through the first original source birth. -/
theorem initial_source_exposure_preserved (event)
    (present : event ∈ (initialSourceExposure observation nontrivial half depth).trace) :
    event ∈ (initialStock observation nontrivial half depth).trace := by
  rw [IC.T.mapped_trace] at present
  obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp present
  have inFrame : original ∈ (C.sourcePaidInventory observation nontrivial depth half).trace :=
    (SourceHistoryCommon.parallel_right _ _ _).1 original belongs
  have carried := L.Stock.carried_scalar (Q.initial observation nontrivial half depth)
    (Q.configuration observation nontrivial half) rfl
    (C.sourcePaidInventory observation nontrivial depth half) rfl original inFrame
  have inScalar : IC.T.liftEvent original ∈
      (SS.scalar Q.factory 0 (Q.data observation nontrivial half depth)
        (Q.configuration observation nontrivial half) rfl).trace := carried
  have inSeed : IC.T.liftEvent original ∈ (firstSeed observation nontrivial half depth).trace :=
    (SourceHistoryCommon.parallel_left _ _ _).1 _ inScalar
  exact Pair.relation_write_preserves _ _ _ _ _
    (IP.supplied_seed_preserved (firstSeed observation nontrivial half depth)
      (firstSelected observation nontrivial half depth) _ inSeed)

abbrev packetAt (tick : Nat) := IC.D.packetAt (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl tick

private def advancedStock (packet : Packet Var) (stock : StockAt packet) :=
  stockTransport packet.2.2.2.down (IC.sourceBorn (D.factory observation nontrivial half) packet)
    (stock.map (IC.sourceLiftEvent packet))

private theorem advanced_preserved (packet : Packet Var) (stock : StockAt packet)
    (preserved : ∃ actual, packet.2.1.1.inventory = some actual ∧
      ∀ event ∈ stock.trace, event ∈ actual.trace) :
    ∃ actual, (IC.packetTransport packet.2.2.2.down
      (IC.sourceBorn (D.factory observation nontrivial half) packet)).2.1.1.inventory = some actual ∧
      ∀ event ∈ (advancedStock observation nontrivial half packet stock).trace, event ∈ actual.trace := by
  obtain ⟨actual, inventory, members⟩ := preserved
  refine ⟨stockTransport packet.2.2.2.down _ (IC.bornStock (D.factory observation nontrivial half) packet),
    transport_inventory _ _ _ (IC.born_inventory _ _), ?_⟩
  apply transport_inclusion
  intro event present
  rw [IC.T.mapped_trace] at present
  obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp present
  exact IC.old_event_in_born (D.factory observation nontrivial half) packet actual inventory original
    (members original belongs)

/-- Successor transport is the actual cofinal packet equality, never a value identification. -/
def sourceExposureAt : (tick : Nat) → StockAt (packetAt observation nontrivial half depth tick)
  | 0 => initialSourceExposure observation nontrivial half depth
  | tick+1 => reindexStock
      (IC.actual_next_packet (D.factory observation nontrivial half)
        (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl tick).symm
      (advancedStock observation nontrivial half (packetAt observation nontrivial half depth tick)
        (sourceExposureAt tick))

theorem source_exposure_at_preserved (tick : Nat) :
    ∃ actual, (packetAt observation nontrivial half depth tick).2.1.1.inventory = some actual ∧
      ∀ event ∈ (sourceExposureAt observation nontrivial half depth tick).trace, event ∈ actual.trace := by
  induction tick with
  | zero => exact ⟨initialStock observation nontrivial half depth, initial_inventory observation nontrivial half depth,
      initial_source_exposure_preserved observation nontrivial half depth⟩
  | succ tick previous =>
    exact reindex_preserved _ _
      (advanced_preserved observation nontrivial half _ _ previous)

abbrev sourceBornExposure (ordinal : Nat) :=
  (sourceExposureAt observation nontrivial half depth (ordinal+1)).map
    (IC.sourceLiftEvent (D.packet observation nontrivial half depth ordinal))

/-- All literal B generators and every coefficient relation enter this actual macro born stock. -/
theorem actual_source_exposure_in_born (ordinal : Nat) (event)
    (present : event ∈ (sourceBornExposure observation nontrivial half depth ordinal).trace) :
    event ∈ (IC.bornStock (D.factory observation nontrivial half)
      (D.packet observation nontrivial half depth ordinal)).trace := by
  obtain ⟨actual, inventory, members⟩ := source_exposure_at_preserved observation nontrivial half depth (ordinal+1)
  rw [IC.T.mapped_trace] at present
  obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp present
  cases original with
  | generator expression =>
    exact IC.old_event_in_born (D.factory observation nontrivial half)
      (D.packet observation nontrivial half depth ordinal) actual inventory _ (members _ belongs)
  | relation word =>
    rw [IC.source_word_action_relation]
    exact IC.source_word_action_in_born (D.factory observation nontrivial half)
      (D.packet observation nontrivial half depth ordinal) actual inventory word (members _ belongs)

abbrev sourceOccurrence := (boundSourceExposure observation nontrivial half depth).map
  (fun event => ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence, event))
abbrev sourceBornHistory (ordinal : Nat) := PTrace.prefixHistory
  (sourceOccurrence observation nontrivial half depth) (sourceBornExposure observation nontrivial half depth ordinal)
abbrev actualBornHistory (ordinal : Nat) := ActualNativeRelationTransport.bornHistory
  (IC.selected (D.factory observation nontrivial half) (D.packet observation nontrivial half depth ordinal))
  (IC.nativePacket (D.factory observation nontrivial half) (D.packet observation nontrivial half depth ordinal)).2.2.1

theorem actual_source_relations_in_born (ordinal : Nat) :
    (sourceBornHistory observation nontrivial half depth ordinal).relationClosure ≤
      (actualBornHistory observation nontrivial half depth ordinal).relationClosure :=
  PTrace.relations_next (sourceOccurrence observation nontrivial half depth)
    (sourceBornExposure observation nontrivial half depth ordinal) _ _
    (actual_source_exposure_in_born observation nontrivial half depth ordinal)

theorem actual_source_generators_in_born (ordinal : Nat) :
    (sourceBornHistory observation nontrivial half depth ordinal).generatorClosure ≤
      (actualBornHistory observation nontrivial half depth ordinal).generatorClosure :=
  PTrace.generators_next (sourceOccurrence observation nontrivial half depth)
    (sourceBornExposure observation nontrivial half depth ordinal) _ _
    (actual_source_exposure_in_born observation nontrivial half depth ordinal)

end OriginalKBFiniteCalculation.BornInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

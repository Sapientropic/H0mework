import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Writeback
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export OriginalKFiniteWard.SF (Factory)
end SF
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve physicalPrior)
end T
namespace Cfg
export SourceGeneratedInquiryReceiptAction.Configured (lowWritten)
end Cfg
namespace FF
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace (boundary sourceOccurrence actualRelation)
end FF
namespace AN
export ActualNativeRelationTransport (bornHistory)
end AN
namespace Native
export ActualCofinalSourceAction (bornStock born_inventory paid_prefix_stocks sourceWordAction source_word_action_in_born source_word_action_inventory)
end Native
namespace L.Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock (scalar)
end L.Stock
local instance inventoryGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

private theorem preserve_generated {α : Type} (prior : Option (RootedAccountedUnfolding α))
    (generated : RootedAccountedUnfolding α) (event : α) (present : event ∈ generated.trace) :
    event ∈ (T.preserve prior generated).trace := by
  cases prior with
  | none => exact present
  | some carried => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem math_trace_in_born_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (event) (present : event ∈ (SourceOperationPaidRelations.exposure
      (R.actualMaterial packet.2.1.1 packet.2.2.1).state.2).trace) :
    event ∈ (Native.bornStock factory packet).trace := by
  have low : event ∈ (Cfg.lowWritten packet.2.1.1 packet.2.2.1).trace :=
    (SourceHistoryCommon.parallel_left _ _ _).1 event present
  have lower : event ∈ (L.Stock.scalar packet.2.1.1 packet.2.2.1 packet.2.2.2.down).trace :=
    preserve_generated _ _ event low
  have scalar : event ∈ (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).trace :=
    preserve_generated _ _ event lower
  change event ∈ (T.preserve (Native.selected factory packet).inventory _).trace
  rw [(Native.paid_prefix_stocks factory packet _ (Nat.le_refl _)).1]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event scalar

private theorem math_boundary_in_born_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
    FF.boundary (R.actualMaterial packet.2.1.1 packet.2.2.1) ∈
      (AN.bornHistory (Native.selected factory packet) (Native.nativePacket factory packet).2.2.1).relationClosure :=
  SourceOperationPaidRelations.relations_next
    (FF.sourceOccurrence (R.actualMaterial packet.2.1.1 packet.2.2.1))
    (SourceOperationPaidRelations.exposure (R.actualMaterial packet.2.1.1 packet.2.2.1).state.2)
    _ (Native.bornStock factory packet) (math_trace_in_born_at factory packet)
    (FF.actualRelation (R.actualMaterial packet.2.1.1 packet.2.2.1)).property

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_math_trace_in_born (ordinal : Nat) (event)
    (present : event ∈ (SourceOperationPaidRelations.exposure (material observation nontrivial half depth ordinal).state.2).trace) :
    event ∈ (Native.bornStock (reactionFactory observation nontrivial half)
      (reactionPacket observation nontrivial half depth ordinal)).trace :=
  math_trace_in_born_at (reactionFactory observation nontrivial half) _ event present

theorem actual_math_boundary_in_born (ordinal : Nat) : type_of%
    (math_boundary_in_born_at (reactionFactory observation nontrivial half) (reactionPacket observation nontrivial half depth ordinal)) :=
  math_boundary_in_born_at (reactionFactory observation nontrivial half) _

theorem actual_math_born_inventory (ordinal : Nat) : type_of%
    (Native.born_inventory (reactionFactory observation nontrivial half)
      (reactionPacket observation nontrivial half depth ordinal)) :=
  Native.born_inventory (reactionFactory observation nontrivial half) _

private theorem word_inventory_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (Native.source_word_action_inventory factory packet) := Native.source_word_action_inventory factory packet

theorem actual_source_word_inventory (ordinal : Nat) : type_of%
    (word_inventory_at (reactionFactory observation nontrivial half)
      (reactionPacket observation nontrivial half depth ordinal)) :=
  word_inventory_at (reactionFactory observation nontrivial half) _

theorem actual_input_stage_trace_in_born (ordinal : Nat) (event)
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (R.actualMaterial (reactionParent observation nontrivial half depth ordinal).2.1.1
        (reactionParent observation nontrivial half depth ordinal).2.2.1).state.2).trace) :
    event ∈ (Native.bornStock (reactionFactory observation nontrivial half)
      (reactionParent observation nontrivial half depth ordinal)).trace :=
  math_trace_in_born_at (reactionFactory observation nontrivial half) _ event present

theorem actual_input_stage_boundary_in_born (ordinal : Nat) : type_of%
    (math_boundary_in_born_at (reactionFactory observation nontrivial half)
      (reactionParent observation nontrivial half depth ordinal)) :=
  math_boundary_in_born_at (reactionFactory observation nontrivial half) _

theorem actual_input_stage_word_inventory (ordinal : Nat) : type_of%
    (word_inventory_at (reactionFactory observation nontrivial half)
      (reactionParent observation nontrivial half depth ordinal)) :=
  word_inventory_at (reactionFactory observation nontrivial half) _

theorem actual_source_word_substitution (ordinal : Nat)
    (binding : ∀ target, C.Var target → Expr (L.Value (PairValue C.Value)
      (reactionPacket observation nontrivial half depth ordinal).1) C.Var target) : type_of%
    (ActualCofinalSourceAction.source_word_action_substitution
      (reactionPacket observation nontrivial half depth ordinal) binding) :=
  ActualCofinalSourceAction.source_word_action_substitution
    (reactionPacket observation nontrivial half depth ordinal) binding

theorem actual_input_stage_word_substitution (ordinal : Nat)
    (binding : ∀ target, C.Var target → Expr (L.Value (PairValue C.Value)
      (reactionParent observation nontrivial half depth ordinal).1) C.Var target) : type_of%
    (ActualCofinalSourceAction.source_word_action_substitution
      (reactionParent observation nontrivial half depth ordinal) binding) :=
  ActualCofinalSourceAction.source_word_action_substitution
    (reactionParent observation nontrivial half depth ordinal) binding

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

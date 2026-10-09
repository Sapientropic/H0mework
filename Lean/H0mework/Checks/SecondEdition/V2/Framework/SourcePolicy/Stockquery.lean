import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Stock

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyStockQueryControls
open SourceOperationEffects SourceOperationScalarInventoryLift
namespace K
export SourceOperationInquiry.Context.Native.Frame.Stock
  (frameAt full_model_next sealed_query source_query source_value source_trace born_stock source_decoder
   registered_raw registered_state calculation_effect calculation_inverse calculation_whole calculation_next
   same_ledger canonical_stock canonical_next)
end K
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (datum nextBorn actualOccurrence resultFace actual_next)
end A
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme lowResult decoder_preserved migrated_charge)
end I
namespace S
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source
  (dynamicFeed Values Vars)
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Source
  (continuous Frame sourceRaw environmentAt)
end S
namespace C
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Consumer
  (born_source_action)
end C
namespace N
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action (actualAction)
end N

theorem actor_decoder (depth count stage : Nat) :
    (A.epoch (A.nextBorn (K.frameAt (S.dynamicFeed depth count) (S.continuous depth count) stage)
      (I.programme (S.continuous depth count)))).activeEnvironment false Unit.unit =
    N.actualAction depth count
      ((A.epoch (K.frameAt (S.dynamicFeed depth count) (S.continuous depth count) stage)).activeEnvironment false Unit.unit) :=
  NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Stock.actor_decoder depth count stage

theorem all_query_outputs (depth count stage : Nat) (pair : PairValue (S.Values depth count) true) : type_of%
    (K.source_decoder (S.dynamicFeed depth count) (S.continuous depth count) stage pair) :=
  K.source_decoder (S.dynamicFeed depth count) (S.continuous depth count) stage pair
theorem exact_query_charge (depth count stage : Nat) : type_of%
    (I.migrated_charge (A.epoch (K.frameAt (S.dynamicFeed depth count) (S.continuous depth count) stage))
      (S.continuous depth count) (A.actualOccurrence (K.frameAt (S.dynamicFeed depth count) (S.continuous depth count) stage))) :=
  I.migrated_charge (A.epoch (K.frameAt (S.dynamicFeed depth count) (S.continuous depth count) stage))
    (S.continuous depth count) (A.actualOccurrence (K.frameAt (S.dynamicFeed depth count) (S.continuous depth count) stage))
theorem low_raw_ignores_stock (depth count : Nat) (frame other : S.Frame depth count) :
    S.sourceRaw depth count {frame with inventory := other.inventory, pairInventory := other.pairInventory} =
      S.sourceRaw depth count frame := rfl
theorem same_runtime_next (depth count stage : Nat) : type_of%
    (A.actual_next (S.dynamicFeed depth count) (I.programme (S.continuous depth count)) stage) :=
  A.actual_next (S.dynamicFeed depth count) (I.programme (S.continuous depth count)) stage

#print axioms K.full_model_next
#print axioms K.sealed_query
#print axioms K.source_query
#print axioms K.source_value
#print axioms K.source_trace
#print axioms K.born_stock
#print axioms K.registered_raw
#print axioms K.registered_state
#print axioms K.calculation_effect
#print axioms K.calculation_inverse
#print axioms K.calculation_whole
#print axioms K.calculation_next
#print axioms K.same_ledger
#print axioms K.canonical_stock
#print axioms K.canonical_next
#print axioms actor_decoder
#print axioms all_query_outputs
#print axioms exact_query_charge
#print axioms low_raw_ignores_stock
#print axioms same_runtime_next
end SourcePolicyStockQueryControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

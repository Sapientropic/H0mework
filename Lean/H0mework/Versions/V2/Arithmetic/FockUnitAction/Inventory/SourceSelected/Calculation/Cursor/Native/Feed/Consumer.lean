import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Source

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Consumer

open SourceOperationEffects
open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source

noncomputable section

namespace B
export SourceGeneratedInquiryReceiptAction.Inventory.Born
  (stock_source original_physical_inventory physical_event next_inventory actual_disposition
   whole_first literal_next actual_update actual_inverse noetherian bornFrame consumer inventory)
end B
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (original_material endpointCount)
end I

abbrev liftEvent (depth count : Nat) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent
    (PhysicalValue := Values depth count) (PhysicalVar := Vars) (sort := true)

abbrev migratedEvent (depth count : Nat)
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Values depth count) Vars true)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.migratedEvent
    (dynamicFeed depth count) (configuration depth count) (liftEvent depth count event)

/-- Every event in the new AST's complete paid trace enters the actual born stock. -/
theorem paid_event_in_born (depth count : Nat)
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Values depth count) Vars true))
    (present : event ∈ (paidInventory depth count).trace) :
    migratedEvent depth count event ∈
      (B.inventory (dynamicFeed depth count) (configuration depth count)).trace := by
  apply B.physical_event
  rw [B.original_physical_inventory]
  exact SourceGeneratedInquiryReceiptAction.Inventory.Carried.input_carried_written
    (dynamicFeed depth count) (paidInventory depth count) rfl event present

theorem paid_event_in_canonical_next (depth count : Nat)
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Values depth count) Vars true))
    (present : event ∈ (paidInventory depth count).trace) : type_of%
      (B.next_inventory (dynamicFeed depth count) (configuration depth count)
        (migratedEvent depth count event) (paid_event_in_born depth count event present)) :=
  B.next_inventory (dynamicFeed depth count) (configuration depth count)
    (migratedEvent depth count event) (paid_event_in_born depth count event present)

/-- Original differently typed material stays inherited, rather than being cast
into the new AST's relation inventory. -/
theorem inherited_source_material (depth count : Nat) : type_of%
    (I.original_material (sourceRoot depth count) (sourceVisit depth count)
      (sourceU7 depth) (sourceCalculus depth) (reader depth count)
      (I.endpointCount (sourceRoot depth count) (sourceVisit depth count) (reader depth count))) :=
  I.original_material (sourceRoot depth count) (sourceVisit depth count)
    (sourceU7 depth) (sourceCalculus depth) (reader depth count)
    (I.endpointCount (sourceRoot depth count) (sourceVisit depth count) (reader depth count))

abbrev OldProjection (depth count : Nat) :=
  (SourceGeneratedInquiryReceiptAction.old
    (B.bornFrame (dynamicFeed depth count) (configuration depth count))
    (B.consumer (dynamicFeed depth count) (configuration depth count))).root.toAuthoritativeRoot.source.projectionLaw.Projection

theorem inherited_projection (depth count : Nat) (projection : OldProjection depth count) : type_of%
    (SourceGeneratedInquiryReceiptAction.all_old_projection
      (B.bornFrame (dynamicFeed depth count) (configuration depth count))
      (B.consumer (dynamicFeed depth count) (configuration depth count)) projection) :=
  SourceGeneratedInquiryReceiptAction.all_old_projection
    (B.bornFrame (dynamicFeed depth count) (configuration depth count))
    (B.consumer (dynamicFeed depth count) (configuration depth count)) projection

/-- The source AST's actual result, updated environment and every paid event
are consumed by the original disposition, whole-ledger write and literal next. -/
theorem written_event_and_next (depth count : Nat)
    (event : CofinalHistorySettlement.PresentedRelationEventAt (Expr (Values depth count) Vars true))
    (present : event ∈ (paidInventory depth count).trace) :
    type_of% (computed_value depth count) ∧
    type_of% (updated_source_is_literal_next depth count) ∧
    type_of% (feed_has_complete_new_trace depth count) ∧
    type_of% (feed_has_actual_update depth count) ∧
    migratedEvent depth count event ∈ (B.inventory (dynamicFeed depth count) (configuration depth count)).trace ∧
    type_of% (paid_event_in_canonical_next depth count event present) ∧
    type_of% (B.stock_source (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (B.actual_disposition (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (B.whole_first (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (B.literal_next (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (B.actual_update (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (B.actual_inverse (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (B.noetherian (dynamicFeed depth count) (configuration depth count)) ∧
    type_of% (inherited_source_material depth count) ∧
    ∀ projection : OldProjection depth count, type_of% (inherited_projection depth count projection) :=
  ⟨computed_value depth count, updated_source_is_literal_next depth count,
   feed_has_complete_new_trace depth count, feed_has_actual_update depth count,
   paid_event_in_born depth count event present, paid_event_in_canonical_next depth count event present,
   B.stock_source (dynamicFeed depth count) (configuration depth count),
   B.actual_disposition (dynamicFeed depth count) (configuration depth count),
   B.whole_first (dynamicFeed depth count) (configuration depth count),
   B.literal_next (dynamicFeed depth count) (configuration depth count),
   B.actual_update (dynamicFeed depth count) (configuration depth count),
   B.actual_inverse (dynamicFeed depth count) (configuration depth count),
   B.noetherian (dynamicFeed depth count) (configuration depth count),
   inherited_source_material depth count, inherited_projection depth count⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

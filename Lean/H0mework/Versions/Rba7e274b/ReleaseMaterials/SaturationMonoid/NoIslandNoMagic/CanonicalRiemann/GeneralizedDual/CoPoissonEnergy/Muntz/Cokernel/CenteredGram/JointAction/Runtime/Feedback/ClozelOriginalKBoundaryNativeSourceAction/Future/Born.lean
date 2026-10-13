import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Future.Seed
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Birth
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction.Future
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Native
export ActualCofinalSourceAction (sourceBorn nativePacket)
end Native
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (root current)
end SO
variable {Sorts : Type u} (W X : Sorts → Type u) [∀ t, AddCommGroup (W t)] (slot : Sorts)
local instance bornReceiptGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (producer : SF.Factory W X slot)
variable (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W := W) (X := X) (s := slot))

theorem born_source_origin :
 bornInitial W X slot producer packet = (Native.sourceBorn producer packet).2.1.1 ∧
 bornProgramme W X slot producer packet = AS.stockCfg (Native.nativePacket producer packet).2.2.1 ∧
 SO.current (bornInitial W X slot producer packet) (bornProgramme W X slot producer packet) =
 SO.current (Native.sourceBorn producer packet).2.1.1 (AS.stockCfg (Native.nativePacket producer packet).2.2.1) ∧
 SO.root (bornInitial W X slot producer packet) (bornProgramme W X slot producer packet) =
 SO.root (Native.sourceBorn producer packet).2.1.1 (AS.stockCfg (Native.nativePacket producer packet).2.2.1) :=
 ⟨rfl,rfl,rfl,rfl⟩

/-- The auxiliary start seed cannot displace the actual born history in the first source calculation or inventory callbacks. -/
theorem born_source_seed_successor (suppliedSeed : SF.Seed (L.Value W (packet.1+1)) packet.2.2.1.LowVar slot 0) : type_of%
 (source_seed_successor (L.Value W (packet.1+1)) packet.2.2.1.LowVar slot
  (continuationFactory W packet.2.2.1.LowVar slot
   (packet.2.2.2.down.symm ▸ producer : SF.Factory W packet.2.2.1.LowVar slot) (packet.1+1))
  (Native.sourceBorn producer packet).2.1.2 suppliedSeed
  (bornInitial W X slot producer packet) (bornProgramme W X slot producer packet) rfl) :=
 source_seed_successor _ _ _ _ _ _ _ _ _

/-- Every grade after the source-seeded entry keeps the original continuation callbacks. -/
theorem continuation_callbacks_after_entry (stages : Nat)
 (seed : SF.Seed (L.Value W (packet.1+1)) packet.2.2.1.LowVar slot (stages+1))
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := L.Value (L.Value W (packet.1+1)) (stages+1)) (Var := packet.2.2.1.LowVar) (sort := slot)) :
 let base := continuationFactory W packet.2.2.1.LowVar slot
  (packet.2.2.2.down.symm ▸ producer : SF.Factory W packet.2.2.1.LowVar slot) (packet.1+1)
 (bornContinuation W X slot packet producer).datum (stages+1) seed frame = base.datum (stages+1) seed frame ∧
 (bornContinuation W X slot packet producer).nextInventory (stages+1) seed frame = base.nextInventory (stages+1) seed frame ∧
 (bornContinuation W X slot packet producer).nextPairInventory (stages+1) seed frame = base.nextPairInventory (stages+1) seed frame ∧
 (bornContinuation W X slot packet producer).extraScalar (stages+1) seed frame = base.extraScalar (stages+1) seed frame ∧
 (bornContinuation W X slot packet producer).extraPair (stages+1) seed frame = base.extraPair (stages+1) seed frame :=
 ⟨rfl,rfl,rfl,rfl,rfl⟩

def consume_born_future {Result : Sort v} (ordinal : Nat)
 (consumer : type_of% (born_source_origin W X slot producer packet) →
  ((suppliedSeed : SF.Seed (L.Value W (packet.1+1)) packet.2.2.1.LowVar slot 0) → type_of%
   (born_source_seed_successor W X slot producer packet suppliedSeed)) →
  type_of% (born_future_model W X slot producer packet ordinal) →
  ((history : List PUnit.{u+1}) → (target : Nat) → type_of%
   (born_actual_future W X slot producer packet ordinal history target)) → Result) : Result :=
 consumer (born_source_origin W X slot producer packet)
  (born_source_seed_successor W X slot producer packet)
  (born_future_model W X slot producer packet ordinal)
  (born_actual_future W X slot producer packet ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

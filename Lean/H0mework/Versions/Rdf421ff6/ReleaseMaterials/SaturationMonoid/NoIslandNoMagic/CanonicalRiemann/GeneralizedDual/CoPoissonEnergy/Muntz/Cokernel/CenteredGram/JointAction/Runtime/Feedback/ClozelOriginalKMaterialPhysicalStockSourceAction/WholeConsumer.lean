import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Material
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.WholeEffect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.PhysicalEffect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState
open scoped InnerProductSpace
namespace NativeRequest
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression expression_eval)
end NativeRequest
namespace PaidMaterial
export ActualNativeRelationTransport (paid)
end PaidMaterial
local instance wholeCurrentGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) (N : ℕ)
local notation "selected" => physicalSelectedAt factory packet N
local notation "base" => physicalBaseAt factory packet N
local notation "sourceBorn" => physicalStockBorn factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N
local notation "whole" => physicalWholeAt factory packet N

/-- These are the actual whole current's registered native source bytes, separate from its decoder-written active environment. -/
def actualWholeRegisteredValue : L.Value (PairValue C.Value) (packet.1+1) () :=
 (sourceBorn).registered.input.expression.eval (sourceBorn).registered.input.environment

/-- The whole callback pays the registered native material effect, independently of the decoder-written active stock. -/
theorem actual_whole_registered_source_effect :
 actualWholeRegisteredValue factory packet N =
 (PaidMaterial.paid selected).raw.effect (PaidMaterial.paid selected).environment (PaidMaterial.paid selected).increment := by
 have endpoint : (PaidMaterial.paid selected).state.1 = .const
   ((physicalStockReceipt factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N).2.1.1) := by
  exact (physicalStockReceipt factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N).2.1.2.down
 exact whole_registered_native_effect selected base (physicalWholeAt factory packet N) _ endpoint

/-- Reading the native whole expression at the registered source environment recovers the actual updated source value used by this decoder. -/
theorem actual_whole_native_update_receipt :
 CF.collapseValue packet.1 (WB.oldPaid packet.2.1.1 packet.2.2.1 +
   (show PairValue (L.Value (PairValue C.Value) packet.1) () from (PaidMaterial.paid selected).state.1.eval (PaidMaterial.paid selected).environment)) =
 actualMaterialStockSourceTotal factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N := by
 have endpoint : (PaidMaterial.paid selected).state.1 = .const
   ((physicalStockReceipt factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N).2.1.1) := by
  exact (physicalStockReceipt factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N).2.1.2.down
 rw [endpoint]
 rfl

/-- The current registered residual and the original endpoint generate the same updated source field; neither is dropped. -/
theorem actual_whole_current_keeps_endpoint_and_effect :
 (PaidMaterial.paid selected).state.1.eval (PaidMaterial.paid selected).environment +
   actualWholeRegisteredValue factory packet N =
 (PaidMaterial.paid selected).raw.eval ((PaidMaterial.paid selected).environment + (PaidMaterial.paid selected).increment) := by
 rw [actual_whole_registered_source_effect,Expr.eval_update]
 have old := (PaidMaterial.paid selected).state.2.sound
 rw [old]

/-- The independent physical consumer reads this actual whole's native current, then the same decoder's born active write. -/
theorem actual_whole_current_physical_write (name : packet.2.2.1.LowVar ()) (test : BurnolPaAmbientCarrier) :
 inner ℂ (OriginalKFullSourceRAction.originalField
  (actualMaterialStockCompleteChange factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N name -
   actualMaterialStockInheritedChange factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N name)) (test : BurnolL2) =
 inner ℂ (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
  (CF.collapseValue packet.1 (WB.oldPaid packet.2.1.1 packet.2.2.1 +
   (show PairValue (L.Value (PairValue C.Value) packet.1) () from
    (PaidMaterial.paid selected).raw.eval ((PaidMaterial.paid selected).environment + (PaidMaterial.paid selected).increment) -
    actualWholeRegisteredValue factory packet N)))) : BurnolL2) (test : BurnolL2) := by
 have current := actual_whole_current_keeps_endpoint_and_effect factory packet N
 have endpoint : (PaidMaterial.paid selected).raw.eval ((PaidMaterial.paid selected).environment + (PaidMaterial.paid selected).increment) -
    actualWholeRegisteredValue factory packet N = (PaidMaterial.paid selected).state.1.eval (PaidMaterial.paid selected).environment := by
  rw [←current,add_sub_cancel_right]
 rw [endpoint,actual_whole_native_update_receipt]
 exact actual_born_physical_read_consumes_source_write _ _ _ _ _ _ name test

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Whole
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance consumerFiniteGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (radius : ℝ) (source : Branches)

theorem consume_finite_source_receipt {Target : Prop}
 (consumer : (whole : type_of% (finiteWholeAt factory packet radius source)) →
 (write : type_of% (finite_stock_generated_source_delta factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source (packet.2.2.2.down.symm ▸ ()))) →
 (trace : type_of% (receivedWindowTrace factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source (packet.2.2.2.down.symm ▸ ()))) → Target) : Target :=
 consumer (finiteWholeAt _ _ _ _)
 (finite_stock_generated_source_delta _ _ _ _ _ _ _ _)
 (receivedWindowTrace _ _ _ _ _ _ _ _)

theorem received_finite_whole_window :
 ∃ whole : type_of% (finiteWholeAt factory packet radius source),
 (type_of% whole.actual_step) ∧ (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧
 (type_of% whole.entry) ∧ (type_of% whole.whole_destination) ∧ (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (received_full_window factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source
  (packet.2.2.2.down.symm ▸ ()) (receivedWindowTrace _ _ _ _ _ _ _ _))) ∧
 (type_of% (received_inverse_residual_source factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source
  (packet.2.2.2.down.symm ▸ ()) (finite_stock_generated_source_delta _ _ _ _ _ _ _ _))) ∧
 (type_of% (received_stock_update_cochain factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source
  (packet.2.2.2.down.symm ▸ ()) (finite_stock_generated_source_delta _ _ _ _ _ _ _ _))) := by
 exact consume_finite_source_receipt factory packet radius source fun whole write trace =>
  ⟨whole,whole.actual_step,whole.same_ledger,whole.same_visit,whole.entry,whole.whole_destination,
  whole.source_environment,whole.source_expression,received_full_window _ _ _ _ _ _ _ _ trace,
  received_inverse_residual_source _ _ _ _ _ _ _ _ write,received_stock_update_cochain _ _ _ _ _ _ _ _ write⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

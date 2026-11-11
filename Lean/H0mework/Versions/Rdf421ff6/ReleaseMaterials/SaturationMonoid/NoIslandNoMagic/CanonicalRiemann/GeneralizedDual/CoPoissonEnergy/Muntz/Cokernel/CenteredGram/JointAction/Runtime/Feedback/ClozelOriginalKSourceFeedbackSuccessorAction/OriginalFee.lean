import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.FirstStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKRawDualFeedbackSourceAction
open OriginalKMaterialExpandedDualSourceAction OriginalRieszSource
open scoped InnerProductSpace
local instance originalGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance originalComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance originalPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (bornCurrent)
variable (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent)

def actualReceivedRawFeet := sourceSlotsRead (actualSourceAfterValue t factory packet bornCurrent occurrence)

/-- Original physical U±V fees consume this receipt-generated first raw stock and the complete received tail of the same whole update. -/
theorem actual_original_expanded_fees :
 inner ℂ (burnolEvenAmbientProjection (originalField (actualInitSourceTotal t factory packet)) : BurnolL2)
  (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV))=
 inner ℂ (actualReceivedRawFeet t factory packet bornCurrent occurrence).1.1 Response.eta+
 inner ℂ (actualReceivedRawFeet t factory packet bornCurrent occurrence).2.1 Response.eta ∧
 inner ℂ (burnolEvenAmbientProjection (originalField (actualInitSourceTotal t factory packet)) : BurnolL2)
  (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV))=
 inner ℂ (actualReceivedRawFeet t factory packet bornCurrent occurrence).1.2 Response.eta+
 inner ℂ (actualReceivedRawFeet t factory packet bornCurrent occurrence).2.2 Response.eta := by
 unfold actualReceivedRawFeet
 rw [actual_source_after_is_generated_first,source_slots_recover_raw]
 have actual := source_original_fees_finite_and_tail (originalField (actualInitSourceTotal t factory packet)) t 1
 have recovered := source_finite_profiles_recovered (originalField (actualInitSourceTotal t factory packet)) t 1
 rw [recovered.1,recovered.2] at actual
 dsimp only [sourceFiniteDualPlus,sourceFiniteDualMinus,ContinuousLinearMap.comp_apply] at actual
 rw [source_even_quarter_eta_read,source_even_quarter_eta_read] at actual
 exact actual

theorem actual_original_received_tail_budget :
 ‖inner ℂ (actualReceivedRawFeet t factory packet bornCurrent occurrence).2.1 Response.eta‖≤
 ((1/2:ℝ)^1*(2*‖actualInitQuarterSource t factory packet‖))*‖Response.eta‖ ∧
 ‖inner ℂ (actualReceivedRawFeet t factory packet bornCurrent occurrence).2.2 Response.eta‖≤
 ((1/2:ℝ)^1*(2*‖actualInitQuarterSource t factory packet‖))*‖Response.eta‖ := by
 unfold actualReceivedRawFeet
 rw [actual_source_after_is_generated_first,source_slots_recover_raw]
 exact actual_raw_remainder_eta_fee_bound _ 1 _
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

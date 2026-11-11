import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaWindowCofinalSourceCompletion.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open CategoryTheory

/-- Every generated source-image point is read by its own decoder and the original evaluators. -/
theorem source_image_decoder_window (point : LinearMap.range sourceCompletionMap.hom) (stage : Nat) :
 windowRead stage (sourceDecoder point) =
 sourceData.stageRealization stage (sourceData.restriction source_data_compatible stage point.val) := by
 have read := ConcreteCategory.congr_hom (source_completion_window_readback stage) (sourceDecoder point)
 have origin : sourceCompletionMap (sourceDecoder point)=point.val :=
  LinearEquiv.ofInjective_symm_apply sourceCompletionMap.hom point
 change sourceData.stageRealization stage
  (sourceData.restriction source_data_compatible stage (sourceCompletionMap (sourceDecoder point))) =
  windowRead stage (sourceDecoder point) at read
 rw [origin] at read
 exact read.symm

local instance completionReceiverGroups (grade : Nat) (target : Unit) :
 AddCommGroup (OriginalKFinitePaWindowOperatorSourceAction.L.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
 OriginalKFinitePaWindowOperatorSourceAction.L.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

/-- This source-image point is generated from the complete family of actual current/residual receipts. -/
def generatedReceivedCompletion : {point : LinearMap.range sourceCompletionMap.hom // ∀ stage : Nat,
 sourceData.stageRealization stage (sourceData.restriction source_data_compatible stage point.val) =
 receivedCofinalWindow observation nontrivial half depth ordinal h H N stage} :=
 ⟨completedSource (actualPaSource observation nontrivial half depth ordinal h H N),fun stage =>
  by
   rw [completed_source_window_read,source_decoder_generated]
   exact (received_cofinal_window_source observation nontrivial half depth ordinal h H N stage
    (R.receivedResidualWindowTrace _ _ _ _ _ _ _ _ _)).symm⟩

/-- The independent decoder uses all received stage equations and the generated separated kernel. -/
theorem received_source_decoder_sound
 (point : LinearMap.range sourceCompletionMap.hom)
 (read : ∀ stage : Nat, sourceData.stageRealization stage
  (sourceData.restriction source_data_compatible stage point.val) =
  receivedCofinalWindow observation nontrivial half depth ordinal h H N stage) :
 sourceDecoder point = actualPaSource observation nontrivial half depth ordinal h H N := by
 apply complete_source_windows_determine
 intro stage
 exact (source_image_decoder_window point stage).trans ((read stage).trans
  (received_cofinal_window_source observation nontrivial half depth ordinal h H N stage
   (R.receivedResidualWindowTrace _ _ _ _ _ _ _ _ _)))

def receivedInverseSource := inverseSourceDecoder
 (generatedReceivedCompletion observation nontrivial half depth ordinal h H N).val

theorem received_inverse_source_decoder : receivedInverseSource observation nontrivial half depth ordinal h H N =
 OriginalKFullSourceRAction.originalField (Residual.actualNu observation nontrivial half depth ordinal h H N) := by
 have decoded := received_source_decoder_sound observation nontrivial half depth ordinal h H N
  (generatedReceivedCompletion observation nontrivial half depth ordinal h H N).val
  (generatedReceivedCompletion observation nontrivial half depth ordinal h H N).property
 change sourceNu (sourceDecoder (generatedReceivedCompletion observation nontrivial half depth ordinal h H N).val) = _
 rw [decoded]
 have source := actual_source_nu_receipt observation nontrivial half depth ordinal h H N
 exact (OriginalKBoundaryNativeSourceAction.source_fields_first _).symm.trans
  (congrArg OriginalKFullSourceRAction.originalField source).symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

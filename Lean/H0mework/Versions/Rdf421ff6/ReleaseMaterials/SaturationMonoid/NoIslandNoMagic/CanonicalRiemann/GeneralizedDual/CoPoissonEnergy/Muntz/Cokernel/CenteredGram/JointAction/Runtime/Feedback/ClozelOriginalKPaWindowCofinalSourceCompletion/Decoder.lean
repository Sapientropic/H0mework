import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaWindowCofinalSourceCompletion.Completion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open CategoryTheory

/-- The actual source embedding generates its own image; no completion coverage enters. -/
def sourceCompletionEquiv : PaSourceCarrier ≃ₗ[ℂ] LinearMap.range sourceCompletionMap.hom :=
 LinearEquiv.ofInjective sourceCompletionMap.hom source_completion_map_injective

def completedSource (value : PaSourceCarrier) : LinearMap.range sourceCompletionMap.hom :=
 sourceCompletionEquiv value

def sourceDecoder : LinearMap.range sourceCompletionMap.hom →ₗ[ℂ] PaSourceCarrier :=
 sourceCompletionEquiv.symm.toLinearMap

def inverseSourceDecoder : LinearMap.range sourceCompletionMap.hom →ₗ[ℂ] BurnolL2 :=
 sourceNu.toLinearMap.comp sourceDecoder

theorem source_decoder_generated (value : PaSourceCarrier) : sourceDecoder (completedSource value)=value :=
 sourceCompletionEquiv.symm_apply_apply value

theorem inverse_source_decoder_generated (value : PaSourceCarrier) :
 inverseSourceDecoder (completedSource value)=sourceNu value := by
 change sourceNu (sourceDecoder (completedSource value))=sourceNu value
 rw [source_decoder_generated]

theorem completed_source_window_read (value : PaSourceCarrier) (stage : Nat) :
 sourceData.stageRealization stage
  (sourceData.restriction source_data_compatible stage (completedSource value).val) =
 windowRead stage (sourceDecoder (completedSource value)) := by
 rw [source_decoder_generated]
 exact ConcreteCategory.congr_hom (source_completion_window_readback stage) value

/-- All source windows determine the actual source, using the generated separated kernel. -/
theorem complete_source_windows_determine (left right : PaSourceCarrier)
 (reads : ∀ stage, windowRead stage left=windowRead stage right) : left=right := by
 apply sub_eq_zero.mp
 apply source_data_kernel_separated
 intro stage
 change windowRead stage (left-right)=0
 rw [map_sub,reads stage,sub_self]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

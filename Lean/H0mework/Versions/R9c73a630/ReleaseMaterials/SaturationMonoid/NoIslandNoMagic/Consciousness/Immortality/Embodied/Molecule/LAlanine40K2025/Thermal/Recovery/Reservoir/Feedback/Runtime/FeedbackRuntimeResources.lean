import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackRuntimeAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem feedbackRuntime_resources_is_installed (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    feedbackRuntimeFacade.readoutAt runtime .resources =
      (.inl ⟨PUnit.unit, (Resource.values (feedbackCurrentState runtime.state.current),
        Resource.values (feedbackCurrentState (feedbackNext runtime.state.current)),
        (Resource.donorRemainingOf (Resource.suppliedBlock (feedbackCurrentState runtime.state.current)),
          Resource.donorRemainingOf (Resource.suppliedBlock (feedbackCurrentState (feedbackNext runtime.state.current)))),
        ⟨Resource.current_total _, Resource.current_total _, Resource.remaining_range _, Resource.remaining_range _,
          feedbackNext_resourceBalance runtime.state.current⟩)⟩ :
        SourceNativeProjectionFiberAt feedbackProjectionLaw .resources (feedbackEmitted runtime.state.current)) := rfl

theorem feedbackRuntime_resourceCertificate :
    type_of% (feedbackRuntimeFace_factorizes feedbackRuntimeSeed .firstResponse) ∧
      type_of% Resource.sourceGeneratedFeedbackResources := by
  refine ⟨feedbackRuntimeFace_factorizes feedbackRuntimeSeed .firstResponse, ?_⟩
  rcases feedbackRuntimeFacade.readoutAt feedbackRuntimeSeed .firstResponse with ⟨_, delivered⟩ | inactive
  · exact delivered.down.2.1
  · exact PEmpty.elim inactive

theorem feedbackRuntime_resourceReceipt : type_of% Resource.sourceGeneratedFeedbackResources :=
  generatedFeedbackAction_receipt.resourceClosure

theorem feedbackRuntime_supplyPaid : type_of% Resource.received_supply_paid := by
  rcases feedbackRuntime_resourceCertificate.2 with ⟨_, _, _, paid, _⟩
  exact paid

theorem feedbackRuntime_PC_after_load_paid : type_of% Resource.received_pc_paid_after_load := by
  rcases feedbackRuntime_resourceCertificate.2 with ⟨_, _, _, _, _, _, _, _, _, _, paid, _⟩
  exact paid

theorem feedbackRuntime_sourceGeneratedFeedbackResources :
    type_of% feedbackRuntime_sourceGeneratedPointerFeedback ∧
    (∀ runtime, type_of% (feedbackRuntimeFace_factorizes runtime .resources)) ∧
    (∀ runtime, type_of% (feedbackRuntime_resources_is_installed runtime)) ∧
    type_of% feedbackRuntime_resourceCertificate ∧ type_of% feedbackRuntime_resourceReceipt ∧
    type_of% feedbackRuntime_supplyPaid ∧ type_of% feedbackRuntime_PC_after_load_paid :=
  ⟨feedbackRuntime_sourceGeneratedPointerFeedback, fun runtime => feedbackRuntimeFace_factorizes runtime .resources,
    feedbackRuntime_resources_is_installed, feedbackRuntime_resourceCertificate, feedbackRuntime_resourceReceipt,
    feedbackRuntime_supplyPaid, feedbackRuntime_PC_after_load_paid⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

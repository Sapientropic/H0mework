import H0mework.Fock.HistoryConditional.MergeLossConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem information_count (runtime : LivingRuntimeState process) (read : Nat → Fine) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) =
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        Real.log ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read actor.val)).1 : ℝ) := by
  rw [SourceInformationReadback.model_information]
  rw [← SourceUniformFibreInformation.source_entropy_average (inventoryBound runtime) (fun actor : Actors runtime => read actor.val) (positive runtime)]
  simp only [SourceUniformFibreInformation.fibre_entropy, SourceConditionalNativePosterior.count_fibre]

theorem gap_zero_iff_information (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    SourceConditionalMergeLoss.gap runtime read forget = 0 ↔
      SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
        (fun actor : Actors runtime => forget (read actor.val))
        (SourceConditionalNext.Image.actual (fun actor : Actors runtime => read actor.val)) (positive runtime) = 0 := by
  rw [SourceConditionalMergeLoss.lossless_iff, SourceConditionalNext.Image.entropy_zero_iff]

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

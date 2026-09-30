import H0mework.Fock.HistoryConditional.PosteriorUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorReadback

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors dynamicRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

theorem entropy_recovered (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) :
    -(∑ actor : Actors runtime,
      (readWeight runtime (SourceConditionalVector.estimate runtime query value supported) actor).toReal *
        Real.log (readWeight runtime (SourceConditionalVector.estimate runtime query value supported) actor).toReal) =
      entropy (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported) := by
  rw [posterior_recovered]
  rfl

theorem dynamic_information_recovered (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalModel.dynamicInformation runtime depth =
      ∑ index : Actors runtime, (historyPMF (inventoryBound runtime) index).toReal *
        -(∑ actor : Actors runtime,
          (readWeight runtime (SourceConditionalVector.dynamicEstimate runtime depth index) actor).toReal *
            Real.log (readWeight runtime (SourceConditionalVector.dynamicEstimate runtime depth index) actor).toReal) := by
  rw [SourceInformationReadback.dynamic_information,
    ← SourceUniformFibreInformation.source_entropy_average _ _ (positive runtime)]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  exact (entropy_recovered runtime (dynamicRead runtime depth) _
    (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index))).symm

theorem updated_information_recovered (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalModel.dynamicInformation runtime.tick.next depth =
      ∑ index : Actors runtime.tick.next, (historyPMF (inventoryBound runtime.tick.next) index).toReal *
        -(∑ actor : Actors runtime.tick.next,
          (readWeight runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth (dynamicRead runtime.tick.next depth index)) actor).toReal *
            Real.log (readWeight runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth (dynamicRead runtime.tick.next depth index)) actor).toReal) := by
  rw [SourceInformationReadback.dynamic_information,
    ← SourceUniformFibreInformation.source_entropy_average _ _ (positive runtime.tick.next)]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  rw [updated_posterior runtime depth _
    (SourceWeightedRecovery.observed_supported _ _ index (positive runtime.tick.next index))]
  rfl

end
end SourcePosteriorReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

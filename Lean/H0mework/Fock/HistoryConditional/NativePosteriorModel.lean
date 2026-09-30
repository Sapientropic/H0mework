import H0mework.Fock.HistoryConditional.NativePosteriorWeight
import H0mework.Fock.HistoryConditional.StabilityMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativePosterior

open SourceConditionalNativeObservers (generate)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Key : Type*} [DecidableEq Key]

def model (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) : NextModel runtime :=
  ∑ actor : Actors runtime, ((generate read (inventoryBound runtime) value).2 actor : ℂ) • nextRead runtime actor

def decoder (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) : SourceJointClockGraph.Carrier :=
  SourceConditionalVector.realizeModel runtime (model runtime read value)

theorem model_original (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    model runtime read value = SourceConditionalVector.estimate runtime (fun actor => read actor.val) value supported := by
  rw [model, SourceConditionalVector.estimate]
  apply Finset.sum_congr rfl
  intro actor _
  have weight : ((generate read (inventoryBound runtime) value).2 actor : ℂ) =
      ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (fun index => read index.val)
        value supported actor).toReal : ℂ) := by
    exact_mod_cast posterior read (inventoryBound runtime) value supported actor
  rw [weight]

theorem decoder_original (runtime : LivingRuntimeState process) (read : Nat → Key) :
    decoder runtime read = SourceConditionalVector.vectorDecoder runtime (fun actor => read actor.val) := by
  classical
  funext value
  by_cases supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support
  · rw [decoder, SourceConditionalVector.vectorDecoder, dif_pos supported, model_original _ _ _ supported]
  · have absent (actor : Actors runtime) : read actor.val ≠ value := by
      intro same
      exact supported ((PMF.mem_support_map_iff _ _ _).mpr ⟨actor, SourceUniformFibreVariance.source_positive _ _, same⟩)
    rw [decoder, SourceConditionalVector.vectorDecoder, dif_neg supported, model]
    simp only [weight_fibre, if_neg (absent _), Rat.cast_zero, zero_smul, Finset.sum_const_zero, map_zero]

theorem complete_posterior (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    SourcePosteriorReadback.readWeight runtime (model runtime read value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
        (fun index => read index.val) value supported actor) := by
  rw [model_original _ _ _ supported]
  exact SourcePosteriorReadback.posterior_recovered _ _ _ _

theorem support_restored (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (candidate : NextModel runtime)
    (small : ‖SourceConditionalVector.realizeModel runtime candidate - decoder runtime read value‖ < SourcePosteriorStability.threshold runtime) :
    SourcePosteriorStability.restoredSupport runtime candidate =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) value := by
  rw [decoder, model_original _ _ _ supported] at small
  with_reducible exact SourcePosteriorStability.support_restored runtime (fun actor => read actor.val) value supported candidate small

theorem information_iff_recovers (runtime : LivingRuntimeState process) (read : Nat → Key) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (SourceConditionalModel.positive runtime) = 0 ↔
    ∀ actor : Actors runtime, decoder runtime read (read actor.val) = SourceConditionalInventory.values (inventoryBound runtime) actor := by
  rw [decoder_original]
  exact SourceActualImageStep.information_zero_iff_recovers runtime _

end
end SourceConditionalNativePosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Fock.HistoryConditional.NativePosteriorWeight
import H0mework.Fock.HistoryConditional.NativeKeysEmbedding

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeKeys

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceGeneratedActionObservationHistory (projection)
open SourceConditionalModel (Actors NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (count bornObservation)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

def decoder (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (embed (inventoryBound runtime) depth (generate (inventoryBound runtime)) value).2)

def model (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : NextModel runtime :=
  projection SourceJointClockGraph.action.toLinearMap (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next) (decoder runtime depth value)

theorem decoder_original (runtime : LivingRuntimeState process) (depth : Nat) :
    decoder runtime depth = SourceConditionalRationalStream.decoder runtime depth := by
  funext value
  rw [decoder, generated_embed]
  rfl

theorem model_original (runtime : LivingRuntimeState process) (depth : Nat) :
    model runtime depth = SourceConditionalRationalStream.model runtime depth := by
  funext value
  rw [model, decoder_original]
  rfl

theorem posterior (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support) :
    SourcePosteriorReadback.readWeight runtime (model runtime depth value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) value supported actor) := by
  rw [model_original]
  exact SourceConditionalRationalStream.posterior _ _ _ _

theorem key_count (bound depth : Nat) (key : ZMod 2) :
    (generate bound key).1 = (SourceUniformFibreVariance.fibre bound (SourceConditionalInventory.observation bound depth) (observed depth key)).card := by
  change (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) bound key).1 = _
  rw [SourceConditionalNativePosterior.count_fibre]
  congr 1
  ext index
  simp only [SourceUniformFibreVariance.fibre_mem, source_observed, (observed_injective depth).eq_iff]

theorem key_posterior (bound depth : Nat) (key : ZMod 2)
    (supported : observed depth key ∈ ((historyPMF bound).map (SourceConditionalInventory.observation bound depth)).support)
    (actor : Fin (bound + 1)) :
    ((generate bound key).2 actor : ℝ) =
      (SourceConditionalInventory.conditional bound depth (observed depth key) supported actor).toReal := by
  have nativeSupported : key ∈ ((historyPMF bound).map (fun index : Fin (bound + 1) => (index.val : ZMod 2))).support := by
    obtain ⟨index, positive, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨index, positive, ?_⟩
    apply observed_injective depth
    simpa only [source_observed] using same
  have same := SourceConditionalHistory.conditional_eq_of_fibre (historyPMF bound)
    (fun index : Fin (bound + 1) => (index.val : ZMod 2)) (SourceConditionalInventory.observation bound depth)
    key (observed depth key) nativeSupported supported
    (fun index => by rw [source_observed, (observed_injective depth).eq_iff])
  have native := SourceConditionalNativePosterior.posterior (fun index : Nat => (index : ZMod 2)) bound key nativeSupported actor
  rw [same] at native
  exact native

theorem error_next (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth (decoder runtime.tick.next depth) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next - decoder runtime depth (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  rw [decoder_original, decoder_original]
  exact SourceConditionalRationalStream.error_next runtime depth

theorem information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (decoder runtime depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem support_restored (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support)
    (candidate : NextModel runtime)
    (small : ‖SourceConditionalVector.realizeModel runtime candidate - decoder runtime depth value‖ < SourcePosteriorStability.threshold runtime) :
    SourcePosteriorStability.restoredSupport runtime candidate =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (dynamicRead runtime depth) value := by
  rw [decoder_original] at small
  exact SourceConditionalRationalStream.support_restored runtime depth value supported candidate small

theorem table_current_next (runtime : LivingRuntimeState process) (depth : Nat) :
    embed (inventoryBound runtime.tick.next) depth (generate (inventoryBound runtime.tick.next)) =
      SourceConditionalRationalStream.advance (inventoryBound runtime) depth
        (embed (inventoryBound runtime) depth (generate (inventoryBound runtime))) := by
  rw [generated_embed, generated_embed]
  exact SourceConditionalRationalStream.table_current_next runtime depth

end
end SourceConditionalNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

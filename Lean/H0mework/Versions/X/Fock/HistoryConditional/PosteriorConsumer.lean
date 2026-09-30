import H0mework.Versions.X.Fock.HistoryConditional.PosteriorInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorReadback

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem recovered_information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    let information := ∑ index : Actors runtime.tick.next, (historyPMF (inventoryBound runtime.tick.next) index).toReal *
      -(∑ actor : Actors runtime.tick.next,
        (readWeight runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth (dynamicRead runtime.tick.next depth index)) actor).toReal *
          Real.log (readWeight runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth (dynamicRead runtime.tick.next depth index)) actor).toReal)
    SourceConditionalInventory.cost (inventoryBound runtime.tick.next) (dynamicRead runtime.tick.next depth) / (inventoryBound runtime.tick.next + 1 : ℝ) +
      (Real.exp (2 * information) - 1) / 12 ≤ SourceConditionalVector.dynamicError runtime.tick.next depth
        (fun value => SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalModelUpdate.updateModel runtime depth value)) := by
  dsimp only
  have paid := SourceConditionalModelUpdate.information_cost runtime depth
  rw [updated_information_recovered] at paid
  exact paid

end
end SourcePosteriorReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

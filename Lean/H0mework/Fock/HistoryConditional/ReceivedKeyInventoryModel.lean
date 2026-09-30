import H0mework.Fock.HistoryConditional.ReceivedKeyInventoryNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

variable {Key : Type*} [DecidableEq Key]

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key) : NextModel runtime :=
  SourceFibreExactState.model runtime nonunit
    (extend (inventoryBound runtime) (maximumIndex runtime).val keys samples key)

theorem reconstruction (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key) :
    SourceConditionalVector.realizeModel runtime (model runtime nonunit keys samples key) +
      SourceFibreExactState.residual runtime nonunit
        (extend (inventoryBound runtime) (maximumIndex runtime).val keys samples key) =
      SourceConditionalVector.realizeModel runtime (SourceFibreExactState.observed runtime nonunit
        (extend (inventoryBound runtime) (maximumIndex runtime).val keys samples key)) :=
  SourceFibreExactState.reconstruction runtime nonunit _

theorem model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    model runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples key =
      SourceConditionalNativePosterior.model runtime read key :=
  SourceFibreExactState.model_source runtime nonunit _ read key (extended_budgets runtime nonunit read samples budgets key)

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

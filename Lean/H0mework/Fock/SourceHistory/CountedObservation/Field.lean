import H0mework.Fock.SourceHistory.CountedObservation.Mixture

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (At)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceObservationInvariantControls (parity)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def observationTable (runtime : LivingRuntimeState process) (table : Table (ℤ × ℤ)) (depth : Nat) :
    Field parity →₀ SourceJointClockGraph.Carrier :=
  (Finsupp.onFinset Finset.univ (mixedValue runtime table forgetClock)
    (fun key _ => Finset.mem_univ key)).mapDomain (SourceConditionalNativeKeys.observed depth)

theorem observation_source (runtime : LivingRuntimeState process) (table : Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) : observationTable runtime table depth = SourceRetainedCoarsening.observationTable runtime frame depth := by
  unfold observationTable SourceRetainedCoarsening.observationTable
  congr 1
  apply Finsupp.ext
  intro key
  simp only [Finsupp.onFinset_apply]
  exact mixedValue_source runtime table frame (clockRead 0) source native keys forgetClock key

theorem field_balance (runtime : LivingRuntimeState process) (table : Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) :
    SourceConditionalVector.dynamicError runtime depth (observationTable runtime table depth) =
      SourceConditionalVector.dynamicVariance runtime depth +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖∑ key ∈ table.keys.toFinset, (weight table forgetClock (actor.val : ZMod 2) key : ℂ) •
          (readValue runtime table key - SourceConditionalVector.realizeModel runtime
            (SourceRetainedReceiver.model runtime frame key))‖ ^ 2 := by
  simp only [observation_source runtime table frame source native keys depth,
    inventory_source _ _ table frame source, weight_source runtime table frame source,
    readValue_source runtime table frame (clockRead 0) source native keys]
  exact SourceRetainedCoarsening.field_balance runtime frame depth native keys

theorem field_information (runtime : LivingRuntimeState process) (table : Table (ℤ × ℤ)) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (observationTable runtime table depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

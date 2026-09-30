import H0mework.Fock.HistoryModel.RecordedAtomicWitness
import H0mework.Probability.Empirical.ObservedAtomic
import H0mework.Fock.SourceHistory.ConditionalObserved
import H0mework.Fock.HistoryModel.RecordedConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation.Installed

open SourceGeneratedEmpiricalHilbert SourceGeneratedScalarDifferentialResidual
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B) (bound : Nat) (index : Fin (bound + 1))

local instance atomicClosed (current : LivingRuntimeState process) :
    IsClosed (LinearMap.ker (SourceGeneratedActionObservationHistory.Dependent.Runtime.source read bound
      (Runtime.cotestAt read bound index) current) : Set (Space read current bound)) :=
  SourceGeneratedActionObservationHistory.Dependent.kernel_closed
    (fun r : LivingRuntimeState process => r.tick.next) (fun r => transfer read r bound)
    (fun r => innerSL ℂ (Runtime.cotestAt read bound index r)) current

local instance atomicComplete (current : LivingRuntimeState process) :
    CompleteSpace (LinearMap.ker (SourceGeneratedActionObservationHistory.Dependent.Runtime.source read bound
      (Runtime.cotestAt read bound index) current)) :=
  (atomicClosed read bound index current).isComplete.completeSpace_coe

theorem atomic_runtime_consumed (value : Space read runtimeSeed bound)
    (decoder : ResidualCarrier (SourceGeneratedActionObservationHistory.Dependent.Runtime.source read bound
      (Runtime.cotestAt read bound index) runtimeSeed.tick.next)) :
    type_of% (Runtime.reader_original read bound index runtimeSeed) ∧
      type_of% (Runtime.next_conditional read bound index runtimeSeed value) ∧
      type_of% (SourceGeneratedActionObservationHistory.Dependent.Installed.runtime_observation_consumed read bound
        (Runtime.cotestAt read bound index) value decoder) :=
  ⟨Runtime.reader_original read bound index runtimeSeed, Runtime.next_conditional read bound index runtimeSeed value,
    SourceGeneratedActionObservationHistory.Dependent.Installed.runtime_observation_consumed read bound
      (Runtime.cotestAt read bound index) value decoder⟩

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeHistoryRecovery SourcePrimeCalculation
open SourceGeneratedActionWords.Fock.OriginalHilbert

local instance recordedConsumerMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem recorded_queries_consumed (actorBound : Nat) :
    let position := completionDepth sourceOwner actorBound + 1
    let depth := position + 1
    (∀ actor : Fin (actorBound + 1),
      type_of% (SourceGeneratedAtomicObservation.Recorded.recorded_mass depth actorBound actor) ∧
      type_of% (SourceGeneratedAtomicObservation.Recorded.query_norm depth actorBound actor) ∧
      type_of% (SourceGeneratedAtomicObservation.Recorded.query_witness depth actorBound actor) ∧
      type_of% (SourceGeneratedAtomicObservation.Recorded.witness_norm depth actorBound actor) ∧
      (∀ value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent actorBound,
        type_of% (SourceGeneratedAtomicObservation.Recorded.query_read depth actorBound actor value)) ∧
      (∀ left right : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent actorBound,
        type_of% (SourceGeneratedAtomicObservation.Recorded.recorded_error_bound depth actorBound actor left right))) ∧
      type_of% (SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded.recorded_word_calculation_consumed actorBound) := by
  dsimp only
  refine ⟨?_, SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded.recorded_word_calculation_consumed actorBound⟩
  intro actor
  exact ⟨SourceGeneratedAtomicObservation.Recorded.recorded_mass _ actorBound actor,
    SourceGeneratedAtomicObservation.Recorded.query_norm _ actorBound actor,
    SourceGeneratedAtomicObservation.Recorded.query_witness _ actorBound actor,
    SourceGeneratedAtomicObservation.Recorded.witness_norm _ actorBound actor,
    SourceGeneratedAtomicObservation.Recorded.query_read _ actorBound actor,
    SourceGeneratedAtomicObservation.Recorded.recorded_error_bound _ actorBound actor⟩

end
end SourceGeneratedAtomicObservation.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

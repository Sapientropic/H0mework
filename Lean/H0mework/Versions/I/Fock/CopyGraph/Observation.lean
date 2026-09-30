import H0mework.Fock.CopyGraph.Calculation
import H0mework.Fock.SourceHistory.CountedMerge.Information

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index sourceDepth scale)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyFutureUpdate.ObservationAt runtime index ∧
      type_of% (normal_cache_source runtime index) ∧ type_of% (next_cache_source runtime index) ∧
      ∀ steps : Nat, (∀ target : SourceJointClockGraph.Carrier,
        type_of% (advance_model_source runtime index steps target) ∧ type_of% (next_reconstruction runtime index steps target) ∧
        type_of% (advance_gain_budget runtime index steps target) ∧
        ∀ unit : scale (inventoryBound runtime) index = 1,
          type_of% (cached_advance_unit runtime index steps unit target) ∧ type_of% (unit_flow_zero runtime index steps unit target)) ∧
        (∀ nonunit : index.val ≠ 0, type_of% (no_cached_nonunit runtime index steps nonunit) ∧
          type_of% (flow_nonzero runtime index steps nonunit) ∧ type_of% (nonunit_tail_decreases runtime index steps nonunit)) ∧
        (∀ ticks : Nat, type_of% (native_model_next runtime index steps ticks)) ∧
        (let current := (calculationNormal runtime).targetRuntime
         let material := SourceGeneratedRuntimeMaterialStageAt.generate (current.advance steps)
          ∀ (nonunit : (maximumIndex current).val ≠ 0) (keys : List (ℤ × ℤ))
            (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
              (inventoryBound current) (fun actor => clockRead 0 actor.val))
            (samples : {key // key ∈ SourceUniformFibreVariance.outputs
              (inventoryBound current) (fun actor => clockRead 0 actor.val)} →
                SourceRationalWindowReadout.Samples (inventoryBound current)
                  ((maximumIndex current).val + 1))
            (budgets : ∀ key, SourceWindowPrecision.gain current (maximumIndex current)
              nonunit 0 * SourceWindowPrecision.sampleEnergy current (maximumIndex current)
                (SourceRationalWindowReadout.embed current (maximumIndex current) 0 (samples key) -
                  SourceCopyTemporalBoundary.recordedPrefix current (maximumIndex current) 0
                    ((maximumIndex current).val + 1)
                    (SourceConditionalNativePosterior.decoder current (clockRead 0) key.val)) <
              SourcePosteriorStability.threshold current ^ 2),
            HEq material.wholeLedgerWriteBack
              ((current.advance steps).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
                (current.advance steps).current.visit.current) ∧
              type_of% (SourceCountedMerge.continued_next_table_strict current nonunit
                keys inventory samples budgets steps))

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyFutureUpdate.observation_consumed runtime index,
    normal_cache_source runtime index, next_cache_source runtime index,
    fun steps => ⟨fun target => ⟨advance_model_source runtime index steps target, next_reconstruction runtime index steps target,
      advance_gain_budget runtime index steps target,
      fun unit => ⟨cached_advance_unit runtime index steps unit target, unit_flow_zero runtime index steps unit target⟩⟩,
      fun nonunit => ⟨no_cached_nonunit runtime index steps nonunit, flow_nonzero runtime index steps nonunit,
        nonunit_tail_decreases runtime index steps nonunit⟩,
      native_model_next runtime index steps,
      (by
        intro nonunit keys inventory samples budgets
        let current := (calculationNormal runtime).targetRuntime
        let material := SourceGeneratedRuntimeMaterialStageAt.generate (current.advance steps)
        exact ⟨material.factorizes.2.2.1,
          SourceCountedMerge.continued_next_table_strict current nonunit
            keys inventory samples budgets steps⟩)⟩⟩

def ActualRecovery : Prop :=
    SourceCopyFutureUpdate.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, type_of% (calculation_consumed runtime) ∧
        ∀ index : Index (inventoryBound runtime), ∀ steps : Nat,
          (∀ unit : scale (inventoryBound runtime) index = 1, ∀ target : SourceJointClockGraph.Carrier,
            type_of% (cached_advance_unit runtime index steps unit target)) ∧
          ∀ nonunit : index.val ≠ 0, type_of% (flow_hidden_coordinate runtime index steps nonunit) ∧
            type_of% (no_cached_nonunit runtime index steps nonunit)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyFutureUpdate.actual_recovery_consumed,
    fun runtime => ⟨calculation_consumed runtime,
      fun index steps => ⟨fun unit target => cached_advance_unit runtime index steps unit target,
        fun nonunit => ⟨flow_hidden_coordinate runtime index steps nonunit, no_cached_nonunit runtime index steps nonunit⟩⟩⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyFutureUpdate.RoundAt round ∧ ActualRecovery ∧ type_of% (calculation_consumed (roundRuntime round)) ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceCopyFutureUpdate.round_consumed round, actual_recovery_consumed, calculation_consumed (roundRuntime round),
    observation_consumed (roundRuntime round)⟩

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

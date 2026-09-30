import H0mework.Fock.CopyGraph.Calculation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index sourceDepth scale)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
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
        ∀ ticks : Nat, type_of% (native_model_next runtime index steps ticks)

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
      native_model_next runtime index steps⟩⟩

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

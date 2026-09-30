import H0mework.Versions.X.Fock.CopyGraph.RecurrenceTrace
import H0mework.Versions.X.Fock.CopyGraph.RecurrenceNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceOwnedObservationHistory
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationRecurrenceMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceGraphFibreUpdate.ObservationAt runtime index ∧ type_of% (normal_history_consumed runtime index) ∧
      ∀ steps : Nat, type_of% (recovery_canonical runtime index steps) ∧
        type_of% (material_history_step runtime index steps) ∧
        type_of% (SourceGraphGrowth.source_read_written (inventoryBound runtime + steps)
          (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)) ∧
        ∀ value : SourceJointClockGraph.Carrier,
          type_of% (original_minimum runtime index steps value) ∧ type_of% (history_residual runtime index steps value) ∧
          type_of% (history_energy runtime index steps value) ∧ type_of% (recovery_improves_iff runtime index steps value) ∧
          type_of% (recovery_record runtime index steps value)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceGraphFibreUpdate.observation_consumed runtime index, normal_history_consumed runtime index,
    fun steps => ⟨recovery_canonical runtime index steps, material_history_step runtime index steps,
      SourceGraphGrowth.source_read_written _ _, fun value => ⟨original_minimum runtime index steps value,
        history_residual runtime index steps value, history_energy runtime index steps value,
        recovery_improves_iff runtime index steps value, recovery_record runtime index steps value⟩⟩⟩

def ActualRecovery : Prop :=
    SourceGraphFibreUpdate.ActualRecovery ∧ type_of% native_collision ∧ type_of% native_novel_step ∧
      type_of% native_novel_recovery ∧ type_of% actual_loss_dominates

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceGraphFibreUpdate.actual_recovery_consumed, native_collision, native_novel_step, native_novel_recovery, actual_loss_dominates⟩

def RoundAt (round : Nat) : Prop :=
    SourceGraphFibreUpdate.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index ∧
        ∀ steps : Nat,
          let depth := sourceDepth round + steps
          let retained := SourceGraphLoss.advancedIndex (sourceDepth round) index steps
          (∀ target : SourceJointClockGraph.Carrier,
            SourceCopyGraph.FieldAt round depth depth retained (recovery (roundRuntime round) index steps target)) ∧
          ∀ value : FieldSpace depth depth,
            let target := SourceCopyGraph.action depth retained (fieldRead depth depth value)
            type_of% (original_energy (roundRuntime round) index steps value) ∧
              type_of% (original_residual_realization round (roundRuntime round) index steps value) ∧
              SourceCopyGraph.FieldAt round depth depth retained (value - recovery (roundRuntime round) index steps target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceGraphFibreUpdate.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun steps => ⟨fun _target => SourceCopyGraph.original_field_consumed round _ _ _ _,
        fun value => ⟨original_energy (roundRuntime round) index steps value,
          original_residual_realization round (roundRuntime round) index steps value,
          SourceCopyGraph.original_field_consumed round _ _ _ _⟩⟩⟩⟩

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

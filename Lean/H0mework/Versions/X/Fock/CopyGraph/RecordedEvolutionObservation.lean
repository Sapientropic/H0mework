import H0mework.Versions.X.Fock.CopyGraph.RecordedEvolutionHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRecordedEvolution

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedAcquisitionJoint SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem recovery_realization (round : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime + steps
    let nextIndex := SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps
    let copied := SourceCopyGraph.complexAction depth nextIndex (word depth depth (recovery runtime index steps target))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (inventoryBound (sourceRound round copied)) (realizeWord round copied) + residual runtime index steps target = target := by
  dsimp only
  rw [SourceCopyGraph.original_copy_realization, residual]
  exact add_sub_cancel _ _

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% ((normal runtime).target_factorizes) ∧ type_of% (SourceGraphRecurrence.normal_depth runtime) ∧
      type_of% (SourceGraphRecurrence.next_depth runtime) ∧
      (∀ target : SourceJointClockGraph.Carrier,
        type_of% (history_energy runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (history_energy runtime index ((frontier runtime).stageCount + 2) target)) ∧
      type_of% (boundary_nonzero runtime index ((frontier runtime).stageCount + 2)) ∧
      type_of% (coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave) := by
  with_reducible exact ⟨(normal runtime).target_factorizes,
    SourceGraphRecurrence.normal_depth runtime, SourceGraphRecurrence.next_depth runtime,
    fun target => ⟨history_energy runtime index _ target, history_energy runtime index _ target⟩,
    boundary_nonzero runtime index _, coversAt_factorizes _ .particleWave⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceColumnForcing.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      ∀ steps : Nat,
        type_of% (SourceGraphRecurrence.material_history_step runtime index steps) ∧
        type_of% (innovation_nonzero runtime index steps) ∧ type_of% (boundary_nonzero runtime index steps) ∧
        (∀ value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps),
          type_of% (field_recovery runtime index steps value)) ∧
        ∀ target : SourceJointClockGraph.Carrier, type_of% (history_energy runtime index steps target) ∧
          type_of% (recovery_original 0 runtime index steps target) ∧ type_of% (residual_original 0 runtime index steps target)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceColumnForcing.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨SourceGraphRecurrence.material_history_step runtime index steps, innovation_nonzero runtime index steps,
      boundary_nonzero runtime index steps, field_recovery runtime index steps,
      fun target => ⟨history_energy runtime index steps target, recovery_original 0 runtime index steps target,
        residual_original 0 runtime index steps target⟩⟩⟩

def ActualRecovery : Prop :=
    SourceColumnForcing.ActualRecovery ∧
      type_of% (old_pulse_recovered (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2)))) ∧
      ∀ steps : Nat, type_of% (boundary_nonzero (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))) steps)

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceColumnForcing.actual_recovery_consumed, old_pulse_recovered (runtimeAt 2) 0, boundary_nonzero (runtimeAt 2) 0⟩

def RoundAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let depth := sourceDepth round
    SourceColumnForcing.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt runtime index ∧
        ∀ steps : Nat, ∀ target : SourceJointClockGraph.Carrier,
          type_of% (recovery_realization round runtime index steps target) ∧
            SourceCopyGraph.FieldAt round (depth + steps) (depth + steps)
              (SourceGraphLoss.advancedIndex depth index steps) (recovery runtime index steps target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceColumnForcing.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun steps target => ⟨recovery_realization round _ index steps target,
        SourceCopyGraph.original_field_consumed round _ _ _ _⟩⟩⟩

end
end SourceRecordedEvolution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

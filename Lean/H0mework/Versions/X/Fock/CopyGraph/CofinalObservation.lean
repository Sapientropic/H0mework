import H0mework.Versions.X.Fock.CopyGraph.CofinalEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCofinal

open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section

theorem residual_tail_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (offset : Nat) (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => SourceRecordedEvolution.residual runtime index (offset + steps) target) atTop
      (𝓝 (SourceCopyGraph.residual (inventoryBound runtime) index target)) := by
  have tail : Tendsto (fun steps : Nat => offset + steps) atTop atTop :=
    tendsto_atTop.mpr fun limit => eventually_atTop.mpr ⟨limit, fun steps reached =>
      reached.trans (Nat.le_add_left steps offset)⟩
  exact (residual_tendsto runtime index target).comp tail

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceRecordedEvolution.normal_consumed runtime index) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (residual_tail_tendsto runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (residual_tail_tendsto runtime index ((frontier runtime).stageCount + 2) target) :=
  ⟨SourceRecordedEvolution.normal_consumed runtime index, fun target =>
    ⟨residual_tail_tendsto runtime index _ target, residual_tail_tendsto runtime index _ target⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceRecordedEvolution.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      type_of% (boundary_residual_tendsto runtime index) ∧ type_of% (boundary_recovery_tendsto runtime index) ∧
      (∀ nonunit : index.val ≠ 0, type_of% (original_root_not_recovered runtime index nonunit)) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (recovery_tendsto runtime index target) ∧ type_of% (residual_tendsto runtime index target) ∧
        type_of% (cost_tendsto runtime index target)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index :=
  ⟨SourceRecordedEvolution.observation_consumed runtime index, normal_consumed runtime index,
    boundary_residual_tendsto runtime index, boundary_recovery_tendsto runtime index,
    original_root_not_recovered runtime index, fun target =>
      ⟨recovery_tendsto runtime index target, residual_tendsto runtime index target, cost_tendsto runtime index target⟩⟩

def ActualRecovery : Prop :=
    SourceRecordedEvolution.ActualRecovery ∧
      type_of% (boundary_residual_tendsto (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2)))) ∧
      type_of% (original_root_not_recovered (runtimeAt 2) (1 : Index (inventoryBound (runtimeAt 2))) (by decide))

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceRecordedEvolution.actual_recovery_consumed, boundary_residual_tendsto (runtimeAt 2) 0,
    original_root_not_recovered (runtimeAt 2) 1 (by decide)⟩

def RoundAt (round : Nat) : Prop :=
    SourceRecordedEvolution.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceRecordedEvolution.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

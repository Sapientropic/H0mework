import H0mework.Fock.CopyGraph.RecoveryBudgetEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecoveryBudget

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyCofinal.normal_consumed runtime index) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (complete_tail_budget runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (complete_tail_budget runtime index ((frontier runtime).stageCount + 2) target) :=
  ⟨SourceCopyCofinal.normal_consumed runtime index, fun target =>
    ⟨complete_tail_budget runtime index _ target, complete_tail_budget runtime index _ target⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyCofinal.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      (∀ steps : Nat, type_of% (boundary_budget_pos runtime index steps)) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (complete_budget runtime index target) ∧ type_of% (remaining_tendsto runtime index target) ∧
        ∀ steps : Nat, type_of% (actual_error runtime index steps target) ∧
          type_of% (history_budget runtime index steps target) ∧ type_of% (complete_tail_budget runtime index steps target) ∧
          type_of% (residual_stays runtime index steps target) ∧ type_of% (residual_budget_zero runtime index steps target) ∧
          type_of% (residual_birth_zero runtime index steps target)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index :=
  ⟨SourceCopyCofinal.observation_consumed runtime index, normal_consumed runtime index,
    boundary_budget_pos runtime index, fun target => ⟨complete_budget runtime index target, remaining_tendsto runtime index target,
      fun steps => ⟨actual_error runtime index steps target, history_budget runtime index steps target,
        complete_tail_budget runtime index steps target, residual_stays runtime index steps target,
        residual_budget_zero runtime index steps target, residual_birth_zero runtime index steps target⟩⟩⟩

def ActualRecovery : Prop :=
    SourceCopyCofinal.ActualRecovery ∧
      (∀ steps : Nat, type_of% (boundary_budget_pos (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))) steps)) ∧
      ∀ steps : Nat, ∀ target : SourceJointClockGraph.Carrier,
        type_of% (residual_stays (runtimeAt 2) (1 : Index (inventoryBound (runtimeAt 2))) steps target) ∧
        type_of% (residual_birth_zero (runtimeAt 2) (1 : Index (inventoryBound (runtimeAt 2))) steps target)

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceCopyCofinal.actual_recovery_consumed, boundary_budget_pos (runtimeAt 2) 0,
    fun steps target => ⟨residual_stays (runtimeAt 2) 1 steps target, residual_birth_zero (runtimeAt 2) 1 steps target⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyCofinal.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyCofinal.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyRecoveryBudget
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

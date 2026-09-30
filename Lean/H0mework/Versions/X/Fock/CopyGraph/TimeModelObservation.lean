import H0mework.Versions.X.Fock.CopyGraph.TimeModelError
import H0mework.Versions.X.Fock.CopyGraph.TimeModelEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index sourceDepth)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_packet_next (depth : Nat) (index : Index depth) (runtime : LivingRuntimeState process) :
    next depth index (phases depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) =
      phases depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) := by
  rw [next_source, SourceJointClockGraph.native_next]

theorem native_restore_next (depth : Nat) (index : Index depth) (runtime : LivingRuntimeState process) :
    restore depth index (next depth index (phases depth index
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next)) := by
  rw [native_packet_next, restore_source]

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyRecoveryBudget.normal_consumed runtime index) ∧
      type_of% (model_native_next (inventoryBound runtime) index (normal runtime).targetRuntime) ∧
      type_of% (native_restore_next (inventoryBound runtime) index (normal runtime).targetRuntime) ∧
      type_of% (native_restore_next (inventoryBound runtime) index (normal runtime).targetRuntime.tick.next) :=
  ⟨SourceCopyRecoveryBudget.normal_consumed runtime index, model_native_next _ index _, native_restore_next _ index _, native_restore_next _ index _⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    SourceCopyRecoveryBudget.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      (∀ phase : Fin (index.val + 1), type_of% (phase_native depth index runtime phase)) ∧
      (∀ value : SourceJointClockGraph.Carrier, type_of% (restore_source depth index value) ∧
        type_of% (next_source depth index value) ∧ type_of% (model_restore_source depth index value) ∧
        type_of% (finite_restore_tendsto runtime index value) ∧ type_of% (finite_future_tendsto runtime index value) ∧
        ∀ steps : Nat, type_of% (finite_error_source runtime index steps value) ∧
          type_of% (finite_next_error_source runtime index steps value) ∧
          ∀ phase : Fin (index.val + 1), type_of% (SourceCopyRecoveryBudget.actual_error runtime index steps (time phase.val value))) ∧
      (∀ value : ExistingModel depth index, type_of% (model_projection_restore depth index value) ∧
        type_of% (model_phases_next depth index value) ∧ type_of% (model_restore_next depth index value)) ∧
      type_of% (blind_read_zero depth index) ∧
      ∀ nonunit : index.val ≠ 0, type_of% (blind_later_nonzero depth index nonunit) ∧
        type_of% (bare_kernel_not_invariant depth index nonunit)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index :=
  ⟨SourceCopyRecoveryBudget.observation_consumed runtime index, normal_consumed runtime index, phase_native _ index runtime,
    fun value => ⟨restore_source _ index value, next_source _ index value, model_restore_source _ index value,
      finite_restore_tendsto runtime index value, finite_future_tendsto runtime index value,
      fun steps => ⟨finite_error_source runtime index steps value, finite_next_error_source runtime index steps value,
        fun phase => SourceCopyRecoveryBudget.actual_error runtime index steps (time phase.val value)⟩⟩,
    fun value => ⟨model_projection_restore _ index value, model_phases_next _ index value, model_restore_next _ index value⟩,
    blind_read_zero _ index, fun nonunit => ⟨blind_later_nonzero _ index nonunit, bare_kernel_not_invariant _ index nonunit⟩⟩

def ActualRecovery : Prop :=
    SourceCopyRecoveryBudget.ActualRecovery ∧
      type_of% (blind_read_zero (inventoryBound (runtimeAt 2)) (1 : Index (inventoryBound (runtimeAt 2)))) ∧
      type_of% (blind_later_nonzero (inventoryBound (runtimeAt 2)) (1 : Index (inventoryBound (runtimeAt 2))) (by decide)) ∧
      type_of% (finite_restore_tendsto (runtimeAt 2) (1 : Index (inventoryBound (runtimeAt 2)))
        (blind (inventoryBound (runtimeAt 2)) (1 : Index (inventoryBound (runtimeAt 2)))))

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceCopyRecoveryBudget.actual_recovery_consumed, blind_read_zero _ 1,
    blind_later_nonzero _ 1 (by decide), finite_restore_tendsto (runtimeAt 2) 1 (blind _ 1)⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyRecoveryBudget.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyRecoveryBudget.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

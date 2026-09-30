import H0mework.Versions.X.Fock.CopyGraph.TimeEnergyEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeEnergy

open SourceCopyProgram (Index sourceDepth)
open SourceCopyTimeModel (Packet phases)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_cost_next (depth : Nat) (index : Index depth) (runtime : LivingRuntimeState process) :
    copyCost depth index (phases depth index (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next)))) =
      copyCost depth index (phases depth index (SourceJointClockGraph.read
        (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) +
      clockWork depth index (phases depth index (SourceJointClockGraph.read
        (SourceClockComplex.ofNative (SourceOperationNative.point runtime))) 0) := by
  rw [← SourceCopyTimeModel.native_packet_next depth index runtime, next_cost]

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyTimeModel.normal_consumed runtime index) ∧
      type_of% (native_cost_next (inventoryBound runtime) index (normal runtime).targetRuntime) ∧
      type_of% (native_cost_next (inventoryBound runtime) index (normal runtime).targetRuntime.tick.next) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (finite_budget runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (finite_next_budget runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (finite_budget runtime index ((frontier runtime).stageCount + 2) target) ∧
        type_of% (finite_next_budget runtime index ((frontier runtime).stageCount + 2) target) :=
  ⟨SourceCopyTimeModel.normal_consumed runtime index, native_cost_next _ index _, native_cost_next _ index _,
    fun target => ⟨finite_budget runtime index _ target, finite_next_budget runtime index _ target,
      finite_budget runtime index _ target, finite_next_budget runtime index _ target⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    SourceCopyTimeModel.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      (∀ packet : Packet depth index, type_of% (restore_energy depth index packet) ∧
        type_of% (restore_budget depth index packet) ∧ type_of% (next_budget depth index packet)) ∧
      (∀ steps : Nat, ∀ target : SourceJointClockGraph.Carrier,
        type_of% (finite_budget runtime index steps target) ∧ type_of% (finite_next_budget runtime index steps target) ∧
        type_of% (history_budget runtime index steps target) ∧ type_of% (whole_residual_budget runtime index steps target)) ∧
      type_of% (native_cost_next depth index runtime) ∧ type_of% (root_unit_work depth index) ∧
      type_of% (signed_work depth index) ∧ type_of% clock_source ∧
      ∀ nonunit : index.val ≠ 0, type_of% (clock_gap depth index nonunit) ∧ type_of% (finite_amplification runtime index nonunit)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index :=
  ⟨SourceCopyTimeModel.observation_consumed runtime index, normal_consumed runtime index,
    fun packet => ⟨restore_energy _ index packet, restore_budget _ index packet, next_budget _ index packet⟩,
    fun steps target => ⟨finite_budget runtime index steps target, finite_next_budget runtime index steps target,
      history_budget runtime index steps target, whole_residual_budget runtime index steps target⟩,
    native_cost_next _ index runtime, root_unit_work _ index, signed_work _ index, clock_source,
    fun nonunit => ⟨clock_gap _ index nonunit, finite_amplification runtime index nonunit⟩⟩

def ActualRecovery : Prop :=
    SourceCopyTimeModel.ActualRecovery ∧ type_of% clock_source ∧
      type_of% (finite_amplification (runtimeAt 2) (1 : Index (inventoryBound (runtimeAt 2))) (by decide)) ∧
      type_of% (root_unit_work (inventoryBound (runtimeAt 2)) (1 : Index (inventoryBound (runtimeAt 2)))) ∧
      type_of% (signed_work (inventoryBound (runtimeAt 2)) (1 : Index (inventoryBound (runtimeAt 2))))

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceCopyTimeModel.actual_recovery_consumed, clock_source, finite_amplification (runtimeAt 2) 1 (by decide),
    root_unit_work _ 1, signed_work _ 1⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyTimeModel.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyTimeModel.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyTimeEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.X.Fock.CopyGraph.Effect
import H0mework.Versions.X.Fock.CopyGraph.CofinalHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCofinal

open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section

theorem cost_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => ‖SourceRecordedEvolution.residual runtime index steps target‖ ^ 2) atTop
      (𝓝 (‖SourceCopyGraph.residual (inventoryBound runtime) index target‖ ^ 2)) :=
  ((residual_tendsto runtime index target).norm).pow 2

theorem boundary_remaining (depth : Nat) (index : Index depth) :
    SourceCopyGraph.residual depth index SourceCompleteGraph.boundary = 0 := by
  rw [SourceCompleteGraph.boundary, SourceJointClockGraph.root_unit_recovery, SourceCopyGraph.residual_apply]
  change WithLp.toLp 2 (WithLp.toLp 2 (SourceCopyGraph.hilbertResidual depth index 0, (0 : ℂ)), (0 : ℂ)) = 0
  rw [map_zero]
  rfl

theorem boundary_recovered (depth : Nat) (index : Index depth) :
    SourceCopyGraph.recover depth index SourceCompleteGraph.boundary = SourceCompleteGraph.boundary := by
  rw [SourceCompleteGraph.boundary, SourceJointClockGraph.root_unit_recovery, SourceCopyGraph.recover_apply]
  change WithLp.toLp 2 (WithLp.toLp 2 (SourceCopyGraph.hilbertRecover depth index 0, (1 : ℂ)),
    (SourceCopyProgram.scale depth index : ℂ)⁻¹ * 0) = _
  rw [map_zero, mul_zero]

theorem boundary_residual_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    Tendsto (fun steps => SourceRecordedEvolution.residual runtime index steps SourceCompleteGraph.boundary) atTop (𝓝 0) := by
  simpa only [boundary_remaining] using residual_tendsto runtime index SourceCompleteGraph.boundary

theorem boundary_recovery_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    Tendsto (fun steps => fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceRecordedEvolution.recovery runtime index steps SourceCompleteGraph.boundary)) atTop
      (𝓝 SourceCompleteGraph.boundary) := by
  simpa only [boundary_recovered] using recovery_tendsto runtime index SourceCompleteGraph.boundary

theorem original_root_nonzero (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    SourceCopyGraph.residual depth index
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCyclicModule.program 1))) ≠ 0 := by
  intro vanished
  have source := SourceCopyGraph.native_residual_moments_retained depth index nonunit
  rw [vanished, zero_add] at source
  have coordinate := congrArg (fun value : SourceJointClockGraph.Carrier =>
    SourceMassCompletion.firstRead (SourceJointClockGraph.joint value) 0) source
  change (0 : ℂ) = SourceMassCompletion.firstRead
    (SourceJointClockGraph.joint (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCyclicModule.program 1)))) 0 at coordinate
  rw [SourceJointClockGraph.joint_source, SourceMassCompletion.firstRead_source, SourceCopyGraph.native_hilbert,
    SourceOwnedObservationHistory.SourceShift.wordRead_coordinate,
    SourceCyclicModule.program_one, SourceCyclicModule.original_root] at coordinate
  change (0 : ℂ) = ((Finsupp.single 0 (1 : ℤ)) 0 : ℂ) at coordinate
  norm_num at coordinate

theorem original_root_not_recovered (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) :
    ¬ Tendsto (fun steps => SourceRecordedEvolution.residual runtime index steps
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCyclicModule.program 1)))) atTop (𝓝 0) := by
  intro lost
  exact original_root_nonzero _ index nonunit (tendsto_nhds_unique (residual_tendsto runtime index _) lost)

end
end SourceCopyCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

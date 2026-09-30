import H0mework.Versions.X.Fock.CopyGraph.TimeModelModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section

theorem continuous_restore (depth : Nat) (index : Index depth) : Continuous (restore depth index) := by
  unfold restore SourceCopyGraph.axes mass
  fun_prop

def finitePhases (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : Packet (inventoryBound runtime) index := fun phase =>
  fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
    (SourceRecordedEvolution.recovery runtime index steps (time phase.val target))

def finiteRestore (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  restore (inventoryBound runtime) index (finitePhases runtime index steps target)

theorem finite_phases_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => finitePhases runtime index steps target) atTop (𝓝 (phases (inventoryBound runtime) index target)) := by
  apply tendsto_pi_nhds.mpr
  intro phase
  have source := SourceCopyCofinal.recovery_tendsto runtime index (time phase.val target)
  simpa only [phase_source, finitePhases] using source

theorem finite_restore_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => finiteRestore runtime index steps target) atTop (𝓝 target) := by
  have source := (continuous_restore (inventoryBound runtime) index).continuousAt.tendsto.comp (finite_phases_tendsto runtime index target)
  simpa only [Function.comp_def, restore_source, finiteRestore] using source

theorem finite_error_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => target - finiteRestore runtime index steps target) atTop (𝓝 0) := by
  simpa only [sub_self] using (tendsto_const_nhds (x := target)).sub (finite_restore_tendsto runtime index target)

theorem continuous_extend (depth : Nat) (index : Index depth) : Continuous (extend depth index) := by
  apply continuous_pi
  intro phase
  refine Fin.lastCases ?_ (fun earlier => ?_) phase
  · simp only [extend, LinearMap.pi_apply, Fin.lastCases_last, LinearMap.comp_apply, LinearMap.proj_apply]
    change Continuous (fun packet : Packet depth index => SourceJointClockGraph.action (packet 0))
    fun_prop
  · simp only [extend, LinearMap.pi_apply, Fin.lastCases_castSucc, LinearMap.proj_apply]
    exact continuous_apply earlier

theorem continuous_next (depth : Nat) (index : Index depth) : Continuous (next depth index) := by
  have drop : Continuous (SourceGeneratedActionObservationHistory.dropFirst (R := ℂ)
      (B := SourceJointClockGraph.Carrier) index.val) := by
    change Continuous (fun packet : SourceGeneratedActionObservationHistory.PrefixCarrier SourceJointClockGraph.Carrier (index.val + 1) =>
      fun phase : Fin (index.val + 1) => packet phase.succ)
    fun_prop
  exact drop.comp (continuous_extend depth index)

theorem finite_future_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => restore (inventoryBound runtime) index (next (inventoryBound runtime) index (finitePhases runtime index steps target)))
      atTop (𝓝 (SourceJointClockGraph.action target)) := by
  have source := (continuous_restore (inventoryBound runtime) index).comp (continuous_next (inventoryBound runtime) index)
  have limit := source.continuousAt.tendsto.comp (finite_phases_tendsto runtime index target)
  simpa only [Function.comp_def, next_source, restore_source] using limit

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

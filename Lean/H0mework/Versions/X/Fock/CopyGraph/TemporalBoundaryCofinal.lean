import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryEffect
import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryFeedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalBoundary

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (time)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section

theorem observer_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => observer runtime index steps target) atTop
      (𝓝 (SourceCopyGraph.recover (inventoryBound runtime) index target)) :=
  SourceCopyCofinal.recovery_tendsto runtime index target

theorem boundary_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) : Tendsto (fun steps => boundary runtime index steps target) atTop (𝓝 0) := by
  have future := observer_tendsto runtime index (time (scale (inventoryBound runtime) index) target)
  have prior := SourceJointClockGraph.action.continuous.continuousAt.tendsto.comp (observer_tendsto runtime index target)
  have difference := future.sub prior
  simpa only [Function.comp_def, SourceCopyTimeModel.recover_cycle, sub_self, boundary] using difference

theorem newest_input_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    type_of% (SourceGeneratedBornDecoder.unit_newest_norm runtime (inventoryBound (next runtime))) ∧
      type_of% (SourceCopyGraph.original_copy_energy (inventoryBound (next runtime)) (inventoryBound (next runtime)) index
        (SourceGeneratedBornDecoder.unitNewest runtime (inventoryBound (next runtime)))) ∧
      type_of% (boundary_cost runtime index) := by
  with_reducible exact ⟨SourceGeneratedBornDecoder.unit_newest_norm runtime (inventoryBound (next runtime)),
    SourceCopyGraph.original_copy_energy (inventoryBound (next runtime)) (inventoryBound (next runtime)) index
      (SourceGeneratedBornDecoder.unitNewest runtime (inventoryBound (next runtime))), boundary_cost runtime index⟩

end
end SourceCopyTemporalBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

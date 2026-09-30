import H0mework.Fock.HistoryConditional.FiniteObservationMinimumSamples

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservationMinimum

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem prefix_kernel_of_update (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (advance : PrefixCarrier SourceJointClockGraph.Carrier length → PrefixCarrier SourceJointClockGraph.Carrier length)
    (law : ∀ value : SourceJointClockGraph.Carrier,
      advance (recordedPrefix runtime index steps length value) =
        recordedPrefix runtime index steps length (SourceJointClockGraph.action value)) :
    LinearMap.ker (recordedPrefix runtime index steps length) ≤
      LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) := by
  apply invariant_submodule_le_kernel SourceJointClockGraph.action.toLinearMap (observer runtime index steps)
  · intro value invisible
    exact congrFun invisible 0
  · intro value invisible
    have origin := law 0
    simp only [map_zero] at origin
    have paid := law value
    rw [show recordedPrefix runtime index steps length value = 0 from invisible, origin] at paid
    exact paid.symm

theorem samples_injective_of_update (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (advance : PrefixCarrier SourceJointClockGraph.Carrier length → PrefixCarrier SourceJointClockGraph.Carrier length)
    (law : ∀ value : SourceJointClockGraph.Carrier,
      advance (recordedPrefix runtime index steps length value) =
        recordedPrefix runtime index steps length (SourceJointClockGraph.action value)) :
    Function.Injective (samples runtime index steps length) := by
  intro left right same
  have observedSame := same_samples runtime index steps length left right same
  have invisible : SourceCopyCurrentCoordinates.realize runtime index steps left -
      SourceCopyCurrentCoordinates.realize runtime index steps right ∈
        LinearMap.ker (recordedPrefix runtime index steps length) := by
    rw [LinearMap.mem_ker, map_sub, observedSame, sub_self]
  have full := prefix_kernel_of_update runtime index steps length advance law invisible
  rw [SourceCopyCurrentCoordinates.kernel_exact] at full
  change SourceCopyCurrentCoordinates.sourceRead runtime index steps
    (SourceCopyCurrentCoordinates.realize runtime index steps left - SourceCopyCurrentCoordinates.realize runtime index steps right) = 0 at full
  rw [map_sub, SourceCopyCurrentCoordinates.realize_source, SourceCopyCurrentCoordinates.realize_source] at full
  exact sub_eq_zero.mp full

end
end SourceFiniteObservationMinimum
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

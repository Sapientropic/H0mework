import H0mework.Fock.CopyGraph.CurrentCoordinatesInvisible

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff windowBound)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceOwnedObservationHistory.SourceShift (H)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem kernel_exact (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) =
      LinearMap.ker (sourceRead runtime index steps) := by
  apply le_antisymm
  · intro target invisible
    have same := (SourceCopyRecordedRecurrence.model_fibre runtime index steps target 0).mpr (by
      intro ticks
      rw [map_zero, map_zero]
      simpa only [← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe, time] using
        (mem_kernel_iff _ _ target).mp invisible ticks)
    have decoded := congrArg (decode runtime index steps) same
    rw [decode_source, decode_source, map_zero] at decoded
    exact decoded
  · exact invariant_submodule_le_kernel SourceJointClockGraph.action.toLinearMap
      (observer runtime index steps) (LinearMap.ker (sourceRead runtime index steps))
      (fun target invisible => observer_zero runtime index steps target invisible)
      (fun target invisible => source_zero_next runtime index steps target invisible)

theorem model_coordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) left =
        projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) right ↔
      sourceRead runtime index steps left = sourceRead runtime index steps right := by
  constructor
  · intro same
    have window := (SourceCopyRecordedRecurrence.full_future_fibre runtime index steps left right).mpr same
    have decoded := congrArg (decode runtime index steps) window
    simpa only [decode_source] using decoded
  · intro same
    have remaining : left - right ∈ LinearMap.ker (sourceRead runtime index steps) := by
      change sourceRead runtime index steps (left - right) = 0
      rw [map_sub, same, sub_self]
    have invisible : left - right ∈
        LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) := by
      rw [kernel_exact]
      exact remaining
    apply (model_fibre_iff _ _ left right).mpr
    intro ticks
    simpa only [map_sub, sub_eq_zero] using (mem_kernel_iff _ _ (left - right)).mp invisible ticks

theorem complete_fibre (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    left = right ↔ sourceRead runtime index steps left = sourceRead runtime index steps right ∧
      ∀ coordinate : Nat, cutoff runtime index steps < coordinate → hilbert left coordinate = hilbert right coordinate := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨same, tail⟩
    have allHilbert : hilbert left = hilbert right := by
      apply lp.ext
      funext coordinate
      by_cases inside : coordinate < cutoff runtime index steps + 1
      · exact congrArg (fun value : Coordinates runtime index steps => value.1 ⟨coordinate, inside⟩) same
      · exact tail coordinate (by omega)
    apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
    apply Prod.ext
    · apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
      exact Prod.ext allHilbert (congrArg (fun value : Coordinates runtime index steps => value.2.1) same)
    · exact congrArg (fun value : Coordinates runtime index steps => value.2.2) same

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

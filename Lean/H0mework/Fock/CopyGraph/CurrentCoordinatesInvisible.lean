import H0mework.Fock.CopyGraph.CurrentCoordinatesRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem column_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0)
    (actor : Fin (inventoryBound runtime + steps + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, target⟫_ℂ = 0 := by
  have within := SourceCopyRecordedRecurrence.address_mono (inventoryBound runtime) index
    (show actor.val ≤ inventoryBound runtime + steps by omega)
  let coordinate : Fin (cutoff runtime index steps + 1) :=
    ⟨indexAfter (inventoryBound runtime) index actor.val, Nat.lt_succ_of_le within⟩
  have hzero := congrArg (fun value : Coordinates runtime index steps => value.1 coordinate) invisible
  have mzero := congrArg (fun value : Coordinates runtime index steps => value.2.1) invisible
  have czero := congrArg (fun value : Coordinates runtime index steps => value.2.2) invisible
  change hilbert target (indexAfter (inventoryBound runtime) index actor.val) = 0 at hzero
  change mass target = 0 at mzero
  change SourceJointClockGraph.clock target = 0 at czero
  rw [column_pairing, hzero, mzero, czero, mul_zero, add_zero, add_zero]

theorem image_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0)
    (source : SourceJointFiniteDecoder.Space (inventoryBound runtime + steps)) :
    ⟪SourceCopyGraph.action (inventoryBound runtime) index
      (SourceJointFiniteDecoder.read (inventoryBound runtime + steps) source), target⟫_ℂ = 0 := by
  rw [SourceJointFiniteDecoder.read, sum_apply, map_sum, sum_inner]
  apply Finset.sum_eq_zero
  intro actor _
  change ⟪SourceCopyGraph.action (inventoryBound runtime) index
    (((Real.sqrt (SourceGeneratedRuntimeHistoryProbability.historyPMF (inventoryBound runtime + steps) actor).toReal : ℂ) * source actor) •
      SourceJointClockGraph.read (Finsupp.single actor.val (1 : ℂ))), target⟫_ℂ = 0
  rw [map_smul, inner_smul_left]
  change starRingEnd ℂ _ * ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, target⟫_ℂ = 0
  rw [column_zero runtime index steps target invisible, mul_zero]

theorem observer_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0) :
    observer runtime index steps target = 0 := by
  have projected : (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection target = 0 := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
      ((SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).zero_mem)
    rw [sub_zero]
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro value ⟨source, rfl⟩
    exact image_zero runtime index steps target invisible source
  apply SourceCopyGraph.action_injective (inventoryBound runtime) index
  rw [map_zero]
  have actual := SourceCopyCofinal.actual_projection runtime index steps target
  rw [SourceCopyCofinal.advanced_action] at actual
  exact actual.symm.trans projected

theorem source_zero_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0) :
    sourceRead runtime index steps (SourceJointClockGraph.action target) = 0 := by
  have mzero := congrArg (fun value : Coordinates runtime index steps => value.2.1) invisible
  have czero := congrArg (fun value : Coordinates runtime index steps => value.2.2) invisible
  change mass target = 0 at mzero
  change SourceJointClockGraph.clock target = 0 at czero
  apply Prod.ext
  · funext coordinate
    change hilbert (time 1 target) coordinate.val = 0
    by_cases origin : coordinate.val = 0
    · exact SourceCopyTimeModel.time_hilbert_before 1 target coordinate.val (by omega)
    · have inside : coordinate.val - 1 < cutoff runtime index steps + 1 := by omega
      have previous := congrArg (fun value : Coordinates runtime index steps => value.1 ⟨coordinate.val - 1, inside⟩) invisible
      change hilbert target (coordinate.val - 1) = 0 at previous
      have shifted := SourceCopyTimeModel.time_hilbert_add 1 target (coordinate.val - 1)
      rw [show coordinate.val - 1 + 1 = coordinate.val by omega] at shifted
      exact shifted.trans previous
  · apply Prod.ext
    · change mass (SourceJointClockGraph.action target) = 0
      rw [SourceCopyTimeModel.mass_next, mzero]
    · change SourceJointClockGraph.clock (SourceJointClockGraph.action target) = 0
      rw [SourceCopyTimeModel.clock_next, mzero, czero, add_zero]

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

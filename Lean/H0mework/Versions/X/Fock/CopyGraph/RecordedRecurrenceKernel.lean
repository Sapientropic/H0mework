import H0mework.Versions.X.Fock.CopyGraph.RecordedRecurrenceSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecordedRecurrence

open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (hilbert mass)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem column_difference (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) (actor : Fin (inventoryBound runtime + steps + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
      difference (cutoff runtime index steps + 1) target⟫_ℂ = 0 := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change (⟪hilbert (SourceColumnForcing.column (inventoryBound runtime) index actor.val),
      hilbert (difference (cutoff runtime index steps + 1) target)⟫_ℂ +
    ⟪mass (SourceColumnForcing.column (inventoryBound runtime) index actor.val),
      mass (difference (cutoff runtime index steps + 1) target)⟫_ℂ) +
    ⟪SourceJointClockGraph.clock (SourceColumnForcing.column (inventoryBound runtime) index actor.val),
      SourceJointClockGraph.clock (difference (cutoff runtime index steps + 1) target)⟫_ℂ = 0
  rw [difference_mass, difference_clock, inner_zero_right, inner_zero_right, add_zero, add_zero]
  change ⟪SourceCopyGraph.hilbertAction (inventoryBound runtime) index (readWord (Finsupp.single actor.val (1 : ℂ))),
    hilbert (difference (cutoff runtime index steps + 1) target)⟫_ℂ = 0
  rw [readWord_single, one_smul, SourceCopyGraph.hilbert_basis]
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, difference_captured]

theorem image_difference (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier)
    (source : SourceJointFiniteDecoder.Space (inventoryBound runtime + steps)) :
    ⟪SourceCopyGraph.action (inventoryBound runtime) index (SourceJointFiniteDecoder.read (inventoryBound runtime + steps) source),
      difference (cutoff runtime index steps + 1) target⟫_ℂ = 0 := by
  rw [SourceJointFiniteDecoder.read, sum_apply, map_sum, sum_inner]
  apply Finset.sum_eq_zero
  intro actor _
  change ⟪SourceCopyGraph.action (inventoryBound runtime) index
    (((Real.sqrt (SourceGeneratedRuntimeHistoryProbability.historyPMF (inventoryBound runtime + steps) actor).toReal : ℂ) * source actor) •
      SourceJointClockGraph.read (Finsupp.single actor.val (1 : ℂ))), difference (cutoff runtime index steps + 1) target⟫_ℂ = 0
  rw [map_smul, inner_smul_left]
  change starRingEnd ℂ _ * ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
    difference (cutoff runtime index steps + 1) target⟫_ℂ = 0
  rw [column_difference, mul_zero]

theorem projected_difference_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection
      (difference (cutoff runtime index steps + 1) target) = 0 := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
    ((SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).zero_mem)
  rw [sub_zero]
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro value ⟨source, rfl⟩
  exact image_difference runtime index steps target source

theorem observer_difference_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceCopyTemporalBoundary.observer runtime index steps (difference (cutoff runtime index steps + 1) target) = 0 := by
  apply SourceCopyGraph.action_injective (inventoryBound runtime) index
  rw [map_zero]
  have actual := SourceCopyCofinal.actual_projection runtime index steps (difference (cutoff runtime index steps + 1) target)
  rw [SourceCopyCofinal.advanced_action] at actual
  exact actual.symm.trans (projected_difference_zero runtime index steps target)

end
end SourceCopyRecordedRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Fock.FiniteObserver.Finite

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem finite_unique (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : Fin (inventoryBound runtime + steps + 1) → ℂ)
    (same : ∀ actor : Fin (inventoryBound runtime + steps + 1),
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
        SourceCopyGraph.action (inventoryBound runtime) index (finiteRead (inventoryBound runtime + steps) left)⟫_ℂ =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
        SourceCopyGraph.action (inventoryBound runtime) index (finiteRead (inventoryBound runtime + steps) right)⟫_ℂ) :
    finiteRead (inventoryBound runtime + steps) left = finiteRead (inventoryBound runtime + steps) right := by
  apply SourceCopyGraph.action_injective (inventoryBound runtime) index
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  let difference := SourceCopyGraph.action (inventoryBound runtime) index (finiteRead (inventoryBound runtime + steps) left) -
    SourceCopyGraph.action (inventoryBound runtime) index (finiteRead (inventoryBound runtime + steps) right)
  have orthogonal (actor : Fin (inventoryBound runtime + steps + 1)) :
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, difference⟫_ℂ = 0 := by
    rw [show difference = _ - _ from rfl, inner_sub_right, same, sub_self]
  change ⟪_ - _, difference⟫_ℂ = 0
  rw [inner_sub_left, finite_action, finite_action]
  simp only [sum_inner, inner_smul_left, orthogonal, mul_zero, Finset.sum_const_zero, sub_self]

theorem observer_calculated (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (word : Nat →₀ ℚ) :
    finiteRead (inventoryBound runtime + steps)
      (fun actor => (calculate (inventoryBound runtime + steps) (index.val + 1) word actor : ℂ)) =
        observer runtime index steps (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord word)) := by
  rw [SourceFiniteObservationMinimum.observer_frame]
  apply finite_unique runtime index steps
  intro actor
  rw [calculated_pairing]
  have original := SourceCopySharedNext.observed_columns runtime index steps actor
    (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord word))
  rw [SourceFiniteObservationMinimum.observer_frame] at original
  exact original.symm

theorem finite_coefficient (bound : Nat) (coefficients : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    SourceCopyTimeModel.hilbert (finiteRead bound coefficients) actor.val = coefficients actor := by
  classical
  change SourceSuccessorBoundary.readWord (∑ source, Finsupp.single source.val (coefficients source)) actor.val = _
  rw [SourceSuccessorBoundary.readWord_coordinate]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single actor]
  · simp
  · intro other _ different
    rw [if_neg (fun same => different (Fin.ext same))]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem frame_calculated (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (word : Nat →₀ ℚ) (actor : Fin (inventoryBound runtime + steps + 1)) :
    (calculate (inventoryBound runtime + steps) (index.val + 1) word actor : ℂ) =
      SourceFiniteObservationMinimum.frame runtime index steps
        (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord word)) actor := by
  have source := congrArg (fun value => SourceCopyTimeModel.hilbert value actor.val)
    (observer_calculated runtime index steps word)
  rw [SourceFiniteObservationMinimum.observer_frame] at source
  exact (finite_coefficient _ _ actor).symm.trans (source.trans (finite_coefficient _ _ actor))

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

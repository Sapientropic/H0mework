import H0mework.Fock.CopyGraph.CurrentCoordinatesKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory.SourceShift (H basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def hilbertLift (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    (Fin (cutoff runtime index steps + 1) → ℂ) →ₗ[ℂ] H :=
  ∑ coordinate, (LinearMap.proj coordinate).smulRight (basis coordinate.val)

theorem hilbert_lift_at (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Fin (cutoff runtime index steps + 1) → ℂ) (coordinate : Fin (cutoff runtime index steps + 1)) :
    hilbertLift runtime index steps value coordinate.val = value coordinate := by
  simp only [hilbertLift, LinearMap.sum_apply]
  change (∑ address : Fin (cutoff runtime index steps + 1), value address • basis address.val) coordinate.val = _
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single coordinate]
  · change value coordinate * basis coordinate.val coordinate.val = value coordinate
    rw [basis, lp.single_apply_self, mul_one]
  · intro address _ different
    change value address * basis address.val coordinate.val = 0
    rw [basis, lp.single_apply_ne _ _ _ (fun same => different (Fin.ext same.symm)), mul_zero]
  · intro absent
    exact (absent (Finset.mem_univ coordinate)).elim

theorem hilbert_lift_outside (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Fin (cutoff runtime index steps + 1) → ℂ) (coordinate : Nat)
    (beyond : cutoff runtime index steps < coordinate) :
    hilbertLift runtime index steps value coordinate = 0 := by
  simp only [hilbertLift, LinearMap.sum_apply]
  change (∑ address : Fin (cutoff runtime index steps + 1), value address • basis address.val) coordinate = 0
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro address _
  change value address * basis address.val coordinate = 0
  rw [basis, lp.single_apply_ne _ _ _ (by omega), mul_zero]

def realize (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Coordinates runtime index steps →ₗ[ℂ] SourceJointClockGraph.Carrier where
  toFun value := WithLp.toLp 2 (WithLp.toLp 2 (hilbertLift runtime index steps value.1, value.2.1), value.2.2)
  map_add' left right := by
    apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
    apply Prod.ext
    · apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
      exact Prod.ext (map_add (hilbertLift runtime index steps) left.1 right.1) rfl
    · rfl
  map_smul' scalar value := by
    apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
    apply Prod.ext
    · apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
      exact Prod.ext (map_smul (hilbertLift runtime index steps) scalar value.1) rfl
    · rfl

theorem realize_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Coordinates runtime index steps) : sourceRead runtime index steps (realize runtime index steps value) = value := by
  apply Prod.ext
  · funext coordinate
    exact hilbert_lift_at runtime index steps value.1 coordinate
  · rfl

theorem source_surjective (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Function.Surjective (sourceRead runtime index steps) :=
  fun value => ⟨realize runtime index steps value, realize_source runtime index steps value⟩

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

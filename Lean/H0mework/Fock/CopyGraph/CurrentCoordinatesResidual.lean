import H0mework.Fock.CopyGraph.CurrentCoordinatesRealization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (hilbert mass)
open SourceCopyRecordedRecurrence (cutoff windowBound)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def retained (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (realize runtime index steps).comp (sourceRead runtime index steps)

def residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  LinearMap.id - retained runtime index steps

theorem reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    retained runtime index steps target + residual runtime index steps target = target := by
  change retained runtime index steps target + (target - retained runtime index steps target) = target
  abel

theorem window_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    realize runtime index steps (decode runtime index steps
      (recordedPrefix runtime index steps (windowBound runtime index steps) target)) = retained runtime index steps target := by
  rw [decode_source]
  rfl

theorem residual_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) : sourceRead runtime index steps (residual runtime index steps target) = 0 := by
  rw [residual, LinearMap.sub_apply, LinearMap.id_apply, map_sub, retained, LinearMap.comp_apply, realize_source, sub_self]

theorem residual_inside (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (coordinate : Fin (cutoff runtime index steps + 1)) :
    hilbert (residual runtime index steps target) coordinate.val = 0 :=
  congrArg (fun value : Coordinates runtime index steps => value.1 coordinate) (residual_source runtime index steps target)

theorem residual_outside (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (coordinate : Nat) (beyond : cutoff runtime index steps < coordinate) :
    hilbert (residual runtime index steps target) coordinate = hilbert target coordinate := by
  simp only [residual, LinearMap.sub_apply, LinearMap.id_apply, hilbert, map_sub]
  change (hilbert target - hilbertLift runtime index steps (sourceRead runtime index steps target).1) coordinate = _
  rw [lp.coeFn_sub]
  change hilbert target coordinate - hilbertLift runtime index steps (sourceRead runtime index steps target).1 coordinate = _
  rw [hilbert_lift_outside _ _ _ _ _ beyond, sub_zero]

theorem retained_orthogonal (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    ⟪retained runtime index steps left, residual runtime index steps right⟫_ℂ = 0 := by
  have mzero := congrArg (fun value : Coordinates runtime index steps => value.2.1) (residual_source runtime index steps right)
  have czero := congrArg (fun value : Coordinates runtime index steps => value.2.2) (residual_source runtime index steps right)
  change mass (residual runtime index steps right) = 0 at mzero
  change SourceJointClockGraph.clock (residual runtime index steps right) = 0 at czero
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change (⟪hilbertLift runtime index steps (sourceRead runtime index steps left).1, hilbert (residual runtime index steps right)⟫_ℂ +
    ⟪mass left, mass (residual runtime index steps right)⟫_ℂ) +
      ⟪SourceJointClockGraph.clock left, SourceJointClockGraph.clock (residual runtime index steps right)⟫_ℂ = 0
  rw [mzero, czero, inner_zero_right, inner_zero_right, add_zero, add_zero,
    hilbertLift, LinearMap.sum_apply, sum_inner]
  apply Finset.sum_eq_zero
  intro coordinate _
  change ⟪(sourceRead runtime index steps left).1 coordinate • basis coordinate.val, hilbert (residual runtime index steps right)⟫_ℂ = 0
  rw [inner_smul_left]
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, residual_inside, mul_zero]

theorem energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps target‖ ^ 2 + ‖residual runtime index steps target‖ ^ 2 = ‖target‖ ^ 2 := by
  have source := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (retained runtime index steps target) (residual runtime index steps target) (retained_orthogonal runtime index steps target target)
  rw [reconstruction] at source
  simpa only [pow_two] using source.symm

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

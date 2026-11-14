import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.ContractiveRecovery
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.LandweberRecovery

open Filter Function
open scoped InnerProductSpace Topology

variable {𝕜 H F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

private def action (read : H →L[𝕜] F) : H →L[𝕜] H :=
  1 - read.adjoint.comp read

private theorem action_apply (read : H →L[𝕜] F) (x : H) :
    action read x = x - read.adjoint (read x) := by
  simp only [action, sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self]

private theorem action_bound (read : H →L[𝕜] F) (bound : ‖read‖ ≤ 1) : ‖action read‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, action_apply, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq (𝕜 := 𝕜),
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq (𝕜 := 𝕜) (read x)]
  have adjointBound : ‖read.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map read).le.trans bound
  have applied : ‖read.adjoint (read x)‖ ≤ ‖read x‖ := by
    simpa only [one_mul] using read.adjoint.le_of_opNorm_le adjointBound (read x)
  have square := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr applied
  linarith only [square, sq_nonneg ‖read x‖]

private theorem action_fixed (read : H →L[𝕜] F) (x : H) :
    action read x = x ↔ read x = 0 := by
  rw [action_apply]
  constructor
  · intro fixed
    have adjointZero : read.adjoint (read x) = 0 := by
      have difference := congrArg (fun y : H => x-y) fixed
      simpa only [sub_sub_cancel, sub_self] using difference
    rw [← inner_self_eq_zero (𝕜 := 𝕜), ← read.adjoint_inner_right, adjointZero, inner_zero_right]
  · intro erased
    rw [erased, map_zero, sub_zero]

local instance kernelComplete (read : H →L[𝕜] F) : CompleteSpace (LinearMap.ker read.toLinearMap) :=
  read.isClosed_ker.isComplete.completeSpace_coe

/-- Use the actual read and its adjoint to correct the observed residual. -/
def step (read : H →L[𝕜] F) (data : F) (x : H) : H :=
  ContractiveRecovery.step (action read) (read.adjoint data) x

theorem step_residual (read : H →L[𝕜] F) (data : F) (x : H) :
    step read data x = x + read.adjoint (data-read x) := by
  rw [step, ContractiveRecovery.step, action_apply, map_sub]
  abel

/-- Average the finite normal iteration on the original complete source space. -/
def approximate (read : H →L[𝕜] F) (data : F) (n : Nat) : H :=
  ContractiveRecovery.approximate (action read) (read.adjoint data) n

/-- The same iteration recovers exactly the observed component when the read has a kernel. -/
theorem recover_visible (read : H →L[𝕜] F) (bound : ‖read‖ ≤ 1) (x : H) :
    Tendsto (approximate read (read x)) atTop
      (𝓝 ((LinearMap.ker read.toLinearMap)ᗮ.starProjection x)) := by
  have fixedKernel : (action read).eqLocus (1 : H →L[𝕜] H) = LinearMap.ker read.toLinearMap := by
    ext y
    change action read y = (1 : H →L[𝕜] H) y ↔ read y = 0
    rw [one_apply_eq_self, action_fixed]
  have convergence := ((action read).tendsto_birkhoffAverage_orthogonalProjection
    (action_bound read bound) x).comp (tendsto_add_atTop_nat 1)
  let K := (action read).eqLocus (1 : H →L[𝕜] H)
  let p := K.starProjection x
  change Tendsto (fun n => birkhoffAverage 𝕜 (action read) id (n+1) x) atTop (𝓝 p) at convergence
  have member : p ∈ LinearMap.ker read.toLinearMap :=
    fixedKernel ▸ K.starProjection_apply_mem x
  have orthogonal : x-p ∈ (LinearMap.ker read.toLinearMap)ᗮ :=
    (congrArg (fun U : Submodule 𝕜 H => Uᗮ) fixedKernel) ▸
      Submodule.sub_starProjection_mem_orthogonal (K := K) x
  have same := Submodule.eq_starProjection_of_mem_orthogonal member orthogonal
  rw [← same] at convergence
  have limit := (tendsto_const_nhds (x := x)).sub convergence
  rw [← Submodule.starProjection_orthogonal_val] at limit
  apply limit.congr' (Eventually.of_forall fun n => ?_)
  have drive : x-action read x = read.adjoint (read x) := by
    rw [action_apply, sub_sub_cancel]
  rw [approximate, ← drive, ContractiveRecovery.actual_approximation]

theorem recover (read : H →L[𝕜] F) (bound : ‖read‖ ≤ 1) (separates : Injective read) (x : H) :
    Tendsto (approximate read (read x)) atTop (𝓝 x) := by
  have member : x ∈ (LinearMap.ker read.toLinearMap)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y invisible
    have zero : y = 0 := separates ((LinearMap.mem_ker.mp invisible).trans read.map_zero.symm)
    rw [zero, inner_zero_left]
  have limit := recover_visible read bound x
  rwa [Submodule.starProjection_eq_self_iff.mpr member] at limit

theorem error (read : H →L[𝕜] F) (bound : ‖read‖ ≤ 1) (x y : F) (n : Nat) :
    ‖approximate read x n-approximate read y n‖ ≤ (n : ℝ)*‖x-y‖ := by
  have adjointBound : ‖read.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map read).le.trans bound
  have paid := ContractiveRecovery.error (action read) (action_bound read bound) (read.adjoint x) (read.adjoint y) n
  change ‖approximate read x n-approximate read y n‖ ≤ (n : ℝ)*‖read.adjoint x-read.adjoint y‖ at paid
  rw [← map_sub] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (by
    simpa only [one_mul] using read.adjoint.le_of_opNorm_le adjointBound (x-y)) (Nat.cast_nonneg _))

end SourceGeneratedActionObservationHistory.LandweberRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

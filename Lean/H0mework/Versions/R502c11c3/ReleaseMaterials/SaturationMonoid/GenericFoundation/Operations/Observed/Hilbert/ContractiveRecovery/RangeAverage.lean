import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.ContractiveRecovery

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.ContractiveRecovery

open Finset Function
open scoped Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The average of the driven orbit can accumulate with a single linear action at each stage. -/
theorem driven_sum_succ (action : H →L[𝕜] H) (drive : H) (n : Nat) :
    birkhoffSum (step action drive) id (n+2) 0 =
      action (birkhoffSum (step action drive) id (n+1) 0) + ((n+1 : Nat) : 𝕜) • drive := by
  unfold birkhoffSum
  rw [Finset.sum_range_succ']
  simp only [iterate_zero, id_eq, add_zero, iterate_succ_apply', step, Finset.sum_add_distrib,
    map_sum, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]

/-- A preceding point in the same action range gives a finite telescoping error. -/
theorem average_range (action : H →L[𝕜] H) (z : H) (n : Nat) :
    birkhoffAverage 𝕜 action id (n+1) (z-action z) =
      (((n+1 : Nat) : 𝕜)⁻¹) • (z-(action)^[n+1] z) := by
  have transport (j : Nat) : (action)^[j] (z-action z) =
      (action)^[j] z-(action)^[j+1] z := by
    induction j with
    | zero => rfl
    | succ j previous =>
        calc
          _ = action ((action)^[j] z-(action)^[j+1] z) :=
            (iterate_succ_apply' (↑action) j _).trans (congrArg action previous)
          _ = _ := by
            rw [map_sub]
            exact congrArg₂ (· - ·) (iterate_succ_apply' (↑action) j z).symm
              (iterate_succ_apply' (↑action) (j+1) z).symm
  unfold birkhoffAverage birkhoffSum
  simp only [id_eq, transport]
  rw [Finset.sum_range_sub', iterate_zero, id_eq]

theorem range_error (action : H →L[𝕜] H) (contractive : ‖action‖ ≤ 1) (z : H) (n : Nat) :
    ‖approximate action ((z-action z)-action (z-action z)) n-(z-action z)‖ ≤
      2*‖z‖/((n : ℝ)+1) := by
  have orbit_norm (j : Nat) : ‖(action)^[j] z‖ ≤ ‖z‖ := by
    induction j with
    | zero => rfl
    | succ j previous =>
        rw [iterate_succ_apply']
        exact (by simpa only [one_mul] using action.le_of_opNorm_le contractive ((action)^[j] z) :
          ‖action ((action)^[j] z)‖ ≤ ‖(action)^[j] z‖).trans previous
  rw [actual_approximation, sub_sub_cancel_left, norm_neg, average_range, norm_smul, norm_inv,
    RCLike.norm_natCast, Nat.cast_add, Nat.cast_one]
  have bound : ‖z-(action)^[n+1] z‖ ≤ 2*‖z‖ := by
    calc
      _ ≤ ‖z‖+‖(action)^[n+1] z‖ := norm_sub_le _ _
      _ ≤ ‖z‖+‖z‖ := add_le_add_right (orbit_norm (n+1)) _
      _ = _ := (two_mul _).symm
  rw [div_eq_mul_inv, mul_comm (2*‖z‖)]
  exact mul_le_mul_of_nonneg_left bound (by positivity)

end SourceGeneratedActionObservationHistory.ContractiveRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.PrefixRecovery.Gram

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.PrefixRecovery

open Filter Finset Function
open scoped InnerProductSpace Topology

variable {𝕜 H F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

def prefixDrive (read : Nat → H →L[𝕜] F) {n : Nat} (data : Fin n → F) : H :=
  ∑ j : Fin n, (weight j : 𝕜) • (row read j).adjoint ((scale read j : 𝕜) • data j)

theorem prefix_drive_source (read : Nat → H →L[𝕜] F) (x : H) (n : Nat) :
    prefixDrive read (fun j : Fin n => read j x) = x-finiteAction read n x := by
  rw [finite_residual]
  exact Fin.sum_univ_eq_sum_range
    (fun j : Nat => (weight j : 𝕜) • (row read j).adjoint (row read j x)) n

/-- Both the driving data and the normal operator use exactly the supplied prefix. -/
def approximate (read : Nat → H →L[𝕜] F) {n : Nat} (data : Fin n → F) : H :=
  ContractiveRecovery.approximate (finiteAction read n) (prefixDrive read data) n

theorem prefix_data_error (read : Nat → H →L[𝕜] F) {n : Nat} (x y : Fin n → F) :
    ‖approximate read x-approximate read y‖ ≤ (n : ℝ)*‖prefixDrive read x-prefixDrive read y‖ :=
  ContractiveRecovery.error (finiteAction read n) (finite_bound read n) _ _ n

omit [CompleteSpace H] in
private theorem orbit_norm (A : H →L[𝕜] H) (bound : ‖A‖ ≤ 1) (x : H) (j : Nat) :
    ‖(A)^[j] x‖ ≤ ‖x‖ := by
  induction j with
  | zero => rfl
  | succ j prev =>
    rw [iterate_succ_apply']
    exact (by simpa only [one_mul] using A.le_of_opNorm_le bound ((A)^[j] x) :
      ‖A ((A)^[j] x)‖ ≤ ‖(A)^[j] x‖).trans prev

omit [CompleteSpace H] in
private theorem orbit_gap (A B : H →L[𝕜] H) (a : ‖A‖ ≤ 1) (b : ‖B‖ ≤ 1) (x : H) (j : Nat) :
    ‖(A)^[j] x-(B)^[j] x‖ ≤ (j : ℝ)*‖A-B‖*‖x‖ := by
  induction j with
  | zero => simp only [iterate_zero, id_eq, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ j prev =>
    rw [iterate_succ_apply', iterate_succ_apply']
    let u := (A)^[j] x
    let v := (B)^[j] x
    change ‖A u-B v‖ ≤ _
    rw [show A u-B v = A (u-v)+(A-B) v by rw [map_sub, sub_apply]; abel]
    have first : ‖A (u-v)‖ ≤ ‖u-v‖ := by simpa only [one_mul] using A.le_of_opNorm_le a (u-v)
    have second : ‖(A-B) v‖ ≤ ‖A-B‖*‖x‖ :=
      ((A-B).le_opNorm v).trans (mul_le_mul_of_nonneg_left (orbit_norm B b x j) (norm_nonneg _))
    calc
      _ ≤ ‖A (u-v)‖+‖(A-B) v‖ := norm_add_le _ _
      _ ≤ ‖u-v‖+‖A-B‖*‖x‖ := add_le_add first second
      _ ≤ (j : ℝ)*‖A-B‖*‖x‖+‖A-B‖*‖x‖ := add_le_add_left prev _
      _ = _ := by rw [Nat.cast_succ]; ring

omit [CompleteSpace H] in
private theorem average_gap (A B : H →L[𝕜] H) (a : ‖A‖ ≤ 1) (b : ‖B‖ ≤ 1) (x : H) (n : Nat) :
    ‖birkhoffAverage 𝕜 A id (n+1) x-birkhoffAverage 𝕜 B id (n+1) x‖ ≤
      (n : ℝ)*‖A-B‖*‖x‖ := by
  let delta := fun j : Nat => (A)^[j] x-(B)^[j] x
  let budget := (n : ℝ)*‖A-B‖*‖x‖
  have scaleNorm : ‖(((n+1 : ℕ) : 𝕜))⁻¹‖ = (((n+1 : ℕ) : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have nonnegative : 0 ≤ (((n+1 : ℕ) : ℝ))⁻¹ := by positivity
  have live : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have bound (j : Nat) (inside : j ∈ range (n+1)) : ‖delta j‖ ≤ budget :=
    (orbit_gap A B a b x j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp inside)) (norm_nonneg _)) (norm_nonneg _))
  simp only [birkhoffAverage, birkhoffSum, id_eq, ← smul_sub, ← sum_sub_distrib, norm_smul, scaleNorm]
  change (((n+1 : ℕ) : ℝ))⁻¹ * ‖∑ j ∈ range (n+1), delta j‖ ≤ budget
  calc
    _ ≤ (((n+1 : ℕ) : ℝ))⁻¹ * (∑ j ∈ range (n+1), ‖delta j‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) nonnegative
    _ ≤ (((n+1 : ℕ) : ℝ))⁻¹ * (∑ _j ∈ range (n+1), budget) :=
      mul_le_mul_of_nonneg_left (sum_le_sum bound) nonnegative
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ live, one_mul]

/-- The omitted rows and the finite iteration have a joint bound that tends to zero. -/
theorem prefix_limit_error (read : Nat → H →L[𝕜] F) (x : H) (n : Nat) :
    ‖approximate read (fun j : Fin n => read j x) -
      ContractiveRecovery.approximate (limitAction read) (x-limitAction read x) n‖ ≤
        (n : ℝ)*mass n*‖x‖ := by
  rw [approximate, prefix_drive_source, ContractiveRecovery.actual_approximation,
    ContractiveRecovery.actual_approximation, sub_sub_sub_cancel_left, norm_sub_rev]
  exact (average_gap (finiteAction read n) (limitAction read)
    (finite_bound read n) (limit_bound read) x n).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (finite_gap read n) (Nat.cast_nonneg _)) (norm_nonneg _))

/-- The finite reads recover the canonical visible component for the entire generated history. -/
theorem recover (read : Nat → H →L[𝕜] F) (x : H) :
    Tendsto (fun n => approximate read (fun j : Fin n => read j x)) atTop
      (𝓝 (((limitAction read).eqLocus (1 : H →L[𝕜] H))ᗮ.starProjection x)) := by
  let A := limitAction read
  let full := ContractiveRecovery.approximate A (x-A x)
  let fitted := fun n => approximate read (fun j : Fin n => read j x)
  let K := A.eqLocus (1 : H →L[𝕜] H)
  have mean := (A.tendsto_birkhoffAverage_orthogonalProjection (limit_bound read) x).comp
    (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => birkhoffAverage 𝕜 A id (n+1) x) atTop (𝓝 (K.starProjection x)) at mean
  have fullLimit := (tendsto_const_nhds (x := x)).sub mean
  rw [← Submodule.starProjection_orthogonal_val] at fullLimit
  have fullLimit : Tendsto full atTop (𝓝 (Kᗮ.starProjection x)) :=
    fullLimit.congr' (Eventually.of_forall fun n => (ContractiveRecovery.actual_approximation A x n).symm)
  have decay := (tendsto_self_mul_const_pow_of_lt_one (r := (1/2 : ℝ))
    (by norm_num) (by norm_num)).mul_const ‖x‖
  have omitted : Tendsto (fun n => fitted n-full n) atTop (𝓝 (0 : H)) :=
    squeeze_zero_norm (prefix_limit_error read x) (by simpa only [zero_mul, mass] using decay)
  have joined := omitted.add fullLimit
  rw [zero_add] at joined
  exact joined.congr' (Eventually.of_forall fun n => sub_add_cancel (fitted n) (full n))

end SourceGeneratedActionObservationHistory.PrefixRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

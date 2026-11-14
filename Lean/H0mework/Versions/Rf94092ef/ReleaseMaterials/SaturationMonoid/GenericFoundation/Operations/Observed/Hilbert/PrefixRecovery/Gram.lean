import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.LandweberRecovery
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.PrefixRecovery

open Finset Filter
open scoped InnerProductSpace Topology

open private action action_bound from
  H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.LandweberRecovery

variable {𝕜 H F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

def scale (read : Nat → H →L[𝕜] F) (j : Nat) : ℝ := (1+‖read j‖)⁻¹

theorem scale_pos (read : Nat → H →L[𝕜] F) (j : Nat) : 0 < scale read j :=
  inv_pos.mpr (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg (read j)))

def row (read : Nat → H →L[𝕜] F) (j : Nat) : H →L[𝕜] F :=
  (scale read j : 𝕜) • read j

private theorem row_bound (read : Nat → H →L[𝕜] F) (j : Nat) : ‖row read j‖ ≤ 1 := by
  have live : 1+‖read j‖ ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg (read j))).ne'
  calc
    _ ≤ ‖(scale read j : 𝕜)‖ * ‖read j‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = scale read j * ‖read j‖ := by
      rw [RCLike.norm_ofReal, abs_of_pos (scale_pos read j)]
    _ ≤ scale read j * (1+‖read j‖) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (scale_pos read j).le
    _ = 1 := inv_mul_cancel₀ live

theorem row_zero_iff (read : Nat → H →L[𝕜] F) (j : Nat) (x : H) :
    row read j x = 0 ↔ read j x = 0 :=
  (smul_eq_zero : (scale read j : 𝕜) • read j x = 0 ↔ _).trans
    (or_iff_right (RCLike.ofReal_ne_zero.mpr (scale_pos read j).ne'))

def mass (n : Nat) : ℝ := (1/2)^n
def weight (j : Nat) : ℝ := mass (j+1)

private theorem weight_pos (j : Nat) : 0 < weight j := by
  unfold weight mass
  positivity

private theorem weight_sum (n : Nat) : ∑ j ∈ range n, weight j = 1-mass n := by
  induction n with
  | zero => simp only [mass, sum_range_zero, pow_zero, sub_self]
  | succ n prior =>
    rw [sum_range_succ, prior, weight, mass, mass, pow_succ]
    ring

private theorem weight_tail (n : Nat) : HasSum (fun j : Nat => weight (j+n)) (mass n) := by
  have terms : (fun j : Nat => weight (j+n)) =
      (fun j => ((1/2 : ℝ)^n * (1/2)) * (1/2)^j) := by
    funext j
    unfold weight mass
    rw [pow_succ, pow_add]
    ring
  rw [terms, show mass n = ((1/2 : ℝ)^n * (1/2)) * 2 by unfold mass; ring]
  exact hasSum_geometric_two.mul_left _

variable [CompleteSpace H] [CompleteSpace F]


private def correction (read : Nat → H →L[𝕜] F) (j : Nat) : H →L[𝕜] H :=
  (row read j).adjoint.comp (row read j)

private def weighted (read : Nat → H →L[𝕜] F) (j : Nat) : H →L[𝕜] H :=
  (weight j : 𝕜) • correction read j

private theorem weighted_bound (read : Nat → H →L[𝕜] F) (j : Nat) : ‖weighted read j‖ ≤ weight j := by
  have h := ContinuousLinearMap.opNorm_smul_le (weight j : 𝕜) (correction read j)
  rw [RCLike.norm_ofReal, abs_of_pos (weight_pos j), correction,
    ContinuousLinearMap.norm_adjoint_comp_self] at h
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (mul_le_one₀ (row_bound read j) (norm_nonneg _) (row_bound read j)) (weight_pos j).le)

private theorem weighted_summable (read : Nat → H →L[𝕜] F) : Summable (weighted read) :=
  ((weight_tail 0).summable.congr fun j => by rw [Nat.add_zero]).of_norm_bounded (weighted_bound read)

/-- Use only the Gram terms for the reads actually in the finite prefix. -/
def finiteAction (read : Nat → H →L[𝕜] F) (n : Nat) : H →L[𝕜] H :=
  1 - ∑ j ∈ range n, weighted read j

private theorem action_convex (read : Nat → H →L[𝕜] F) (n : Nat) :
    finiteAction read n =
      (mass n : 𝕜) • 1 + ∑ j ∈ range n, (weight j : 𝕜) • (1-correction read j) := by
  have coefficient : ∑ j ∈ range n, (weight j : 𝕜) = ((1-mass n : ℝ) : 𝕜) := by
    rw [← RCLike.ofReal_sum, weight_sum]
  simp only [finiteAction, weighted, smul_sub, sum_sub_distrib]
  rw [← sum_smul, coefficient, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
  abel

theorem finite_bound (read : Nat → H →L[𝕜] F) (n : Nat) : ‖finiteAction read n‖ ≤ 1 := by
  have weightBound (j : Nat) : ‖(weight j : 𝕜) • (1-correction read j)‖ ≤ weight j := by
    have h := ContinuousLinearMap.opNorm_smul_le (weight j : 𝕜) (1-correction read j)
    rw [RCLike.norm_ofReal, abs_of_pos (weight_pos j)] at h
    have contracts : ‖(1-correction read j : H →L[𝕜] H)‖ ≤ 1 := by
      change ‖action (row read j)‖ ≤ 1
      exact action_bound (row read j) (row_bound read j)
    exact h.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left contracts (weight_pos j).le)
  have idle : ‖(mass n : 𝕜) • (1 : H →L[𝕜] H)‖ ≤ mass n := by
    have h := ContinuousLinearMap.opNorm_smul_le (mass n : 𝕜) (1 : H →L[𝕜] H)
    have massNonneg : 0 ≤ mass n := by unfold mass; positivity
    rw [RCLike.norm_ofReal, abs_of_nonneg massNonneg] at h
    have identity : ‖(1 : H →L[𝕜] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left identity massNonneg)
  rw [action_convex]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ mass n + ∑ j ∈ range n, weight j :=
      add_le_add idle ((norm_sum_le _ _).trans (sum_le_sum fun j _ => weightBound j))
    _ = 1 := by rw [weight_sum]; ring

/-- The limit operator is used to prove convergence of the finite programme. -/
def limitAction (read : Nat → H →L[𝕜] F) : H →L[𝕜] H :=
  1 - ∑' j, weighted read j

theorem finite_gap (read : Nat → H →L[𝕜] F) (n : Nat) :
    ‖finiteAction read n-limitAction read‖ ≤ mass n := by
  unfold finiteAction limitAction
  rw [← (weighted_summable read).sum_add_tsum_nat_add n,
    show (1 - ∑ j ∈ range n, weighted read j) -
      (1 - ((∑ j ∈ range n, weighted read j) + ∑' j, weighted read (j+n))) =
      ∑' j, weighted read (j+n) by abel]
  exact tsum_of_norm_bounded (weight_tail n) fun j => weighted_bound read (j+n)

theorem finite_tendsto (read : Nat → H →L[𝕜] F) :
    Tendsto (finiteAction read) atTop (𝓝 (limitAction read)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
    (finite_gap read) (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))

theorem limit_bound (read : Nat → H →L[𝕜] F) : ‖limitAction read‖ ≤ 1 :=
  le_of_tendsto (finite_tendsto read).norm (Eventually.of_forall (finite_bound read))

theorem finite_residual (read : Nat → H →L[𝕜] F) (n : Nat) (x : H) :
    x-finiteAction read n x =
      ∑ j ∈ range n, (weight j : 𝕜) • (row read j).adjoint (row read j x) := by
  simp only [finiteAction, sub_apply, one_apply_eq_self, sub_sub_cancel,
    _root_.sum_apply, weighted, correction, smul_apply,
    ContinuousLinearMap.comp_apply]

theorem limit_fixed (read : Nat → H →L[𝕜] F) (x : H) :
    limitAction read x = x ↔ ∀ j, read j x = 0 := by
  have acts := (ContinuousLinearMap.apply 𝕜 H x).continuous.tendsto _ |>.comp (finite_tendsto read)
  change Tendsto (fun n => finiteAction read n x) atTop (𝓝 (limitAction read x)) at acts
  constructor
  · intro fixed j
    have scalar : Tendsto (fun n => RCLike.re (inner 𝕜 x (x-finiteAction read n x))) atTop (𝓝 0) := by
      have h := (RCLike.reCLM.continuous.tendsto (inner 𝕜 x (x-limitAction read x))).comp
        ((tendsto_const_nhds (x := x)).inner ((tendsto_const_nhds (x := x)).sub acts))
      change Tendsto (fun n => RCLike.re (inner 𝕜 x (x-finiteAction read n x))) atTop
        (𝓝 (RCLike.re (inner 𝕜 x (x-limitAction read x)))) at h
      rwa [fixed, sub_self, inner_zero_right, RCLike.zero_re] at h
    have term : weight j * ‖row read j x‖^2 ≤ 0 := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds scalar
      filter_upwards [eventually_gt_atTop j] with n beyond
      rw [finite_residual, inner_sum]
      change weight j * ‖row read j x‖^2 ≤
        (RCLike.reLm : 𝕜 →ₗ[ℝ] ℝ) (∑ i ∈ range n, _)
      rw [map_sum]
      have realTerm (i : Nat) :
          RCLike.re (inner 𝕜 x ((weight i : 𝕜) • (row read i).adjoint (row read i x))) =
            weight i * ‖row read i x‖^2 := by
        rw [inner_smul_right, RCLike.re_ofReal_mul, ContinuousLinearMap.adjoint_inner_right,
          inner_self_eq_norm_sq]
      change weight j * ‖row read j x‖^2 ≤
        ∑ i ∈ range n, RCLike.re (inner 𝕜 x ((weight i : 𝕜) • (row read i).adjoint (row read i x)))
      simp only [realTerm]
      exact single_le_sum (f := fun i => weight i * ‖row read i x‖^2)
        (fun i _ => mul_nonneg (weight_pos i).le (sq_nonneg _)) (mem_range.mpr beyond)
    by_contra alive
    have rowLive := mt (row_zero_iff read j x).mp alive
    exact (not_lt_of_ge term) (mul_pos (weight_pos j) (pow_pos (norm_pos_iff.mpr rowLive) _))
  · intro silent
    have fixed (n : Nat) : finiteAction read n x = x := by
      apply (sub_eq_zero.mp ?_).symm
      rw [finite_residual]
      apply sum_eq_zero
      intro j _
      rw [(row_zero_iff read j x).mpr (silent j), map_zero, smul_zero]
    exact tendsto_nhds_unique acts ((tendsto_const_nhds (x := x)).congr'
      (Eventually.of_forall fun n => (fixed n).symm))

end SourceGeneratedActionObservationHistory.PrefixRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

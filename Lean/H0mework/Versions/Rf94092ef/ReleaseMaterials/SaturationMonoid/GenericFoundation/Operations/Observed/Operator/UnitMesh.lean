import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedUnitMesh

open MeasureTheory Set
open scoped BigOperators

def node (mesh j : Nat) : ℝ := (j : ℝ) / mesh

private theorem width (mesh j : Nat) : node mesh (j+1) - node mesh j = (mesh : ℝ)⁻¹ := by
  simp only [node, Nat.cast_add, Nat.cast_one, add_div, one_div, add_sub_cancel_left]

private theorem ordered (mesh j : Nat) : node mesh j ≤ node mesh (j+1) := by
  apply sub_nonneg.mp
  rw [width]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite right-endpoint word on an equal unit mesh. -/
def average (mesh : Nat) (f : ℝ → E) : E :=
  (mesh : ℝ)⁻¹ • ∑ j ∈ Finset.range mesh, f (node mesh (j+1))

theorem average_bound (mesh : Nat) (positive : 0 < mesh) (f : ℝ → E) (bound : ℝ)
    (samples : ∀ j < mesh, ‖f (node mesh (j+1))‖ ≤ bound) :
    ‖average mesh f‖ ≤ bound := by
  have mPos : (0 : ℝ) < mesh := by exact_mod_cast positive
  rw [average, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr mPos.le)]
  calc
    _ ≤ (mesh : ℝ)⁻¹ * ∑ j ∈ Finset.range mesh, ‖f (node mesh (j+1))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr mPos.le)
    _ ≤ (mesh : ℝ)⁻¹ * ∑ _j ∈ Finset.range mesh, bound :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j hj => samples j (Finset.mem_range.mp hj))) (inv_nonneg.mpr mPos.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

variable [CompleteSpace E]

theorem average_error (mesh : Nat) (positive : 0 < mesh) (f : ℝ → E)
    (regular : ContinuousOn f (Icc 0 1)) (L : ℝ) (price : 0 ≤ L)
    (travel : ∀ u v, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → u ≤ v →
      ‖f u - f v‖ ≤ L * (v-u)) :
    ‖(∫ t : ℝ in (0 : ℝ)..1, f t) - average mesh f‖ ≤ L/(mesh : ℝ) := by
  have mPos : (0 : ℝ) < mesh := by exact_mod_cast positive
  have included (j : Nat) (before : j < mesh) :
      Icc (node mesh j) (node mesh (j+1)) ⊆ Icc (0 : ℝ) 1 := by
    intro t inside
    have cap : node mesh (j+1) ≤ 1 :=
      (div_le_one mPos).mpr (by exact_mod_cast Nat.succ_le_of_lt before)
    exact ⟨(div_nonneg (Nat.cast_nonneg _) mPos.le).trans inside.1, inside.2.trans cap⟩
  have integrable (j : Nat) (before : j < mesh) :
      IntervalIntegrable f volume (node mesh j) (node mesh (j+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ordered mesh j)]
    exact regular.mono (included j before)
  have split := intervalIntegral.sum_integral_adjacent_intervals integrable
  rw [show node mesh 0 = 0 by simp [node], show node mesh mesh = 1 by
    exact div_self mPos.ne'] at split
  rw [← split, average, Finset.smul_sum, ← Finset.sum_sub_distrib]
  let err : Nat → E := fun j => (∫ t in node mesh j..node mesh (j+1), f t) -
    (mesh : ℝ)⁻¹ • f (node mesh (j+1))
  change ‖∑ j ∈ Finset.range mesh, err j‖ ≤ _
  have cell (j : Nat) (before : j < mesh) : ‖err j‖ ≤ (L/(mesh : ℝ)) * (mesh : ℝ)⁻¹ := by
    have range := ordered mesh j
    have endpoint : node mesh (j+1) ∈ Icc (0 : ℝ) 1 :=
      included j before ⟨range,le_rfl⟩
    have point (t : ℝ) (inside : t ∈ uIoc (node mesh j) (node mesh (j+1))) :
        ‖f t - f (node mesh (j+1))‖ ≤ L/(mesh : ℝ) := by
      rw [uIoc_of_le range] at inside
      have gap : node mesh (j+1)-t ≤ (mesh : ℝ)⁻¹ := by
        rw [← width mesh j]
        exact sub_le_sub_left inside.1.le _
      rw [div_eq_mul_inv]
      exact (travel _ _ (included j before ⟨inside.1.le,inside.2⟩) endpoint inside.2).trans
        (mul_le_mul_of_nonneg_left gap price)
    have bound := intervalIntegral.norm_integral_le_of_norm_le_const point
    rw [abs_of_nonneg (sub_nonneg.mpr range), width mesh j] at bound
    dsimp only [err]
    rw [← width mesh j, ← intervalIntegral.integral_const, ← intervalIntegral.integral_sub
      (integrable j before) intervalIntegrable_const]
    rw [width]
    exact bound
  calc
    _ ≤ ∑ j ∈ Finset.range mesh, ‖err j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range mesh, (L/(mesh : ℝ)) * (mesh : ℝ)⁻¹ :=
      Finset.sum_le_sum (fun j hj => cell j (Finset.mem_range.mp hj))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedUnitMesh

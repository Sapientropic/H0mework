import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false

namespace LAlanineTrueTube.Dynamics

open Set Metric
open scoped NNReal

abbrev Space := Fin 3 → ℝ

noncomputable section

def clip (lower upper x : Space) (i : Fin 3) : ℝ :=
  max (lower i) (min (upper i) (x i))

theorem clip_mem (lower upper : Space) (ordered : lower ≤ upper) (x : Space) :
    clip lower upper x ∈ Icc lower upper := by
  constructor
  · intro i
    exact le_max_left _ _
  · intro i
    exact max_le (ordered i) (min_le_left _ _)

theorem clip_eq (lower upper x : Space) (inside : x ∈ Icc lower upper) :
    clip lower upper x = x := by
  funext i
  simp only [clip, min_eq_right (inside.2 i), max_eq_right (inside.1 i)]

theorem clip_lipschitz (lower upper : Space) : LipschitzWith 1 (clip lower upper) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  have scalar : LipschitzWith 1 (fun t : ℝ => max (lower i) (min (upper i) t)) :=
    (LipschitzWith.id.const_min _).const_max _
  exact (scalar.dist_le_mul (x i) (y i)).trans (by simpa using dist_le_pi_dist x y i)

def extension (lower upper : Space) (f : Space → Space) (x : Space) : Space :=
  f (clip lower upper x)

theorem extension_lipschitz (lower upper : Space) (ordered : lower ≤ upper)
    (f : Space → Space) (K : ℝ≥0) (lip : LipschitzOnWith K f (Icc lower upper)) :
    LipschitzWith K (extension lower upper f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (lip.dist_le_mul _ (clip_mem lower upper ordered x) _ (clip_mem lower upper ordered y)).trans
    (mul_le_mul_of_nonneg_left (by simpa using (clip_lipschitz lower upper).dist_le_mul x y) K.coe_nonneg)

def fieldBound (lower upper : Space) : ℝ≥0 :=
  ∑ i : Fin 3, (‖lower i‖₊ + ‖upper i‖₊)

theorem norm_le_fieldBound (lower upper x : Space) (inside : x ∈ Icc lower upper) :
    ‖x‖ ≤ (fieldBound lower upper : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (fieldBound lower upper).coe_nonneg).mpr
  intro i
  have h : |x i| ≤ |lower i| + |upper i| := by
    apply abs_le.mpr
    constructor <;> linarith [inside.1 i, inside.2 i, neg_abs_le (lower i), le_abs_self (upper i),
      abs_nonneg (lower i), abs_nonneg (upper i)]
  have bound : ‖lower i‖₊ + ‖upper i‖₊ ≤ fieldBound lower upper :=
    Finset.single_le_sum (f := fun j => ‖lower j‖₊ + ‖upper j‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact h.trans (by exact_mod_cast bound)

theorem extension_bounds (lower upper : Space) (ordered : lower ≤ upper) (f : Space → Space)
    (gLower gUpper : Space) (bounds : ∀ x ∈ Icc lower upper, f x ∈ Icc gLower gUpper)
    (x : Space) : extension lower upper f x ∈ Icc gLower gUpper :=
  bounds _ (clip_mem lower upper ordered x)

end
end LAlanineTrueTube.Dynamics

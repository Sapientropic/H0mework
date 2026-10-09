import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandGlobalSource.Gradient
import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel ContinuousGradient Set Metric ODE
open scoped NNReal
noncomputable section

def windowZero (radius : ℝ≥0) : Icc (-(radius : ℝ)) radius :=
  ⟨0,neg_nonpos.mpr radius.coe_nonneg,radius.coe_nonneg⟩

theorem global_picard (initial : Point) (radius : ℝ≥0) :
    IsPicardLindelof (fun _ => sourceGradient) (windowZero radius) initial
      (sourceSpeedBound * radius + 1) 0 sourceSpeedBound sourceLipschitzBound where
  lipschitzOnWith _ _ := sourceGradient_globally_lipschitz.lipschitzOnWith
  continuousOn _ _ := continuous_const.continuousOn
  norm_le _ _ x _ := sourceGradient_uniform_bound x
  mul_max_le := by
    change (sourceSpeedBound : ℝ) * max ((radius : ℝ) - 0) (0 - -(radius : ℝ)) ≤
      ((sourceSpeedBound : ℝ) * radius + 1) - 0
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    linarith

def window (initial : Point) (radius : ℝ≥0) : ℝ → Point :=
  Classical.choose (global_picard initial radius).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem window_starts (initial : Point) (radius : ℝ≥0) : window initial radius 0 = initial :=
  (Classical.choose_spec (global_picard initial radius).exists_eq_forall_mem_Icc_hasDerivWithinAt₀).1

theorem window_derivative (initial : Point) (radius : ℝ≥0) (t : ℝ)
    (inside : t ∈ Ioo (-(radius : ℝ)) radius) :
    HasDerivAt (window initial radius) (sourceGradient (window initial radius t)) t :=
  ((Classical.choose_spec (global_picard initial radius).exists_eq_forall_mem_Icc_hasDerivWithinAt₀).2
    t (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)

theorem windows_agree (initial : Point) (R S : ℝ≥0) (t : ℝ)
    (left : |t| < (R : ℝ)) (right : |t| < (S : ℝ)) :
    window initial R t = window initial S t := by
  let r : ℝ := min (R : ℝ) (S : ℝ)
  have positive : 0 < r := lt_min ((abs_nonneg t).trans_lt left) ((abs_nonneg t).trans_lt right)
  have leftInside : Ioo (-r) r ⊆ Ioo (-(R : ℝ)) R := by
    intro u hu
    exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hu.1,hu.2.trans_le (min_le_left _ _)⟩
  have rightInside : Ioo (-r) r ⊆ Ioo (-(S : ℝ)) S := by
    intro u hu
    exact ⟨(neg_le_neg (min_le_right _ _)).trans_lt hu.1,hu.2.trans_le (min_le_right _ _)⟩
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun _ => sourceGradient) (s := fun _ => univ)
    (fun _ _ => sourceGradient_globally_lipschitz.lipschitzOnWith)
    (show (0 : ℝ) ∈ Ioo (-r) r from ⟨by linarith,positive⟩)
    (fun u hu => ⟨window_derivative initial R u (leftInside hu),mem_univ _⟩)
    (fun u hu => ⟨window_derivative initial S u (rightInside hu),mem_univ _⟩)
    ((window_starts initial R).trans (window_starts initial S).symm)
  exact abs_lt.mp (lt_min left right)

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Chemistry.LAlanineRefinementDensity.LaplaceIntegers
import H0mework.Chemistry.LAlanineRefinementDensity.DensitySlices
import H0mework.Chemistry.LAlanineRefinementDensity.Quadrature
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceProducer

open SourceFiniteData SourceGaussianModel SourceLaplaceIntegers
open Set Filter
open scoped BigOperators Interval Topology

noncomputable section

def axisBound (axis : Fin 3) : ℚ := ∑ innerAxis : Fin 3, densityBound (fourthIndex innerAxis axis)

theorem actual_axis_bounds : axisBound = ![15202, 4209, 1977] := by
  funext axis
  fin_cases axis <;> decide +kernel

theorem axisBound_positive (axis : Fin 3) : 0 < axisBound axis := by
  rw [actual_axis_bounds]
  fin_cases axis <;> norm_num

theorem radius_positive : 0 < boxRadius := by decide +kernel

def lower (axis : Fin 3) : ℝ := ((boxCentre axis - boxRadius : ℚ) : ℝ)
def upper (axis : Fin 3) : ℝ := ((boxCentre axis + boxRadius : ℚ) : ℝ)

theorem interval_ordered (axis : Fin 3) : lower axis < upper axis := by
  have positive : (0 : ℝ) < (boxRadius : ℝ) := by exact_mod_cast radius_positive
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  linarith

def TransverseInside (point : Point) (axis : Fin 3) : Prop :=
  ∀ other : Fin 3, other ≠ axis → |point other - (boxCentre other : ℝ)| ≤ (boxRadius : ℝ)

theorem slice_inside (point : Point) (axis : Fin 3) (transverse : TransverseInside point axis)
    (time : ℝ) (inside : time ∈ Icc (lower axis) (upper axis)) :
    InsideCube boxCentre boxRadius (Function.update point axis time) := by
  intro other
  by_cases same : other = axis
  · subst other
    simp only [Function.update_self]
    apply abs_le.mpr
    simp only [lower, upper, Rat.cast_sub, Rat.cast_add] at inside
    constructor <;> linarith [inside.1, inside.2]
  · rw [Function.update_of_ne same]
    exact transverse other same

def sourceSlice (point : Point) (axis : Fin 3) (time : ℝ) : ℝ :=
  laplacian sourceTerms densityMatrix (Function.update point axis time)

theorem sourceSlice_contDiff (point : Point) (axis : Fin 3) : ContDiff ℝ 2 (sourceSlice point axis) :=
  laplacian_slice_contDiff sourceTerms densityMatrix point axis 2

def errorBudget (axis : Fin 3) (panels : Nat) : ℝ :=
  (upper axis - lower axis) ^ 3 * (axisBound axis : ℝ) / (12 * (panels : ℝ) ^ 2)

theorem errorBudget_positive (axis : Fin 3) (panels : Nat) (positive : 0 < panels) :
    0 < errorBudget axis panels := by
  have width := sub_pos.mpr (interval_ordered axis)
  have bound : (0 : ℝ) < (axisBound axis : ℝ) := by exact_mod_cast axisBound_positive axis
  unfold errorBudget
  positivity

theorem actual_doubling_budget (axis : Fin 3) (panels : Nat) :
    errorBudget axis (2 * panels) = errorBudget axis panels / 4 := by
  unfold errorBudget
  push_cast
  ring

theorem actual_doubling_strict (axis : Fin 3) (panels : Nat) (positive : 0 < panels) :
    errorBudget axis (2 * panels) < errorBudget axis panels := by
  rw [actual_doubling_budget]
  have source := errorBudget_positive axis panels positive
  linarith

theorem actual_bisection_readout (point : Point) (axis : Fin 3) :
    trapezoidal_integral (sourceSlice point axis) 2 (lower axis) (upper axis) =
      trapezoidal_integral (sourceSlice point axis) 1 (lower axis) ((lower axis + upper axis) / 2) +
        trapezoidal_integral (sourceSlice point axis) 1 ((lower axis + upper axis) / 2) (upper axis) :=
  actualBisection_readout _ _ _

theorem errorBudget_tendsto_zero (axis : Fin 3) : Tendsto (errorBudget axis) atTop (𝓝 0) := by
  have inverse : Tendsto (fun n : Nat => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have limit := (inverse.pow 2).const_mul ((upper axis - lower axis) ^ 3 * (axisBound axis : ℝ) / 12)
  convert! limit using 1
  · funext n
    simp only [errorBudget, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  · norm_num

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceProducer

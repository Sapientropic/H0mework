import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousGradient

open scoped BigOperators

theorem fderiv_coordinate (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) (axis : Fin 3)
    (hf : DifferentiableAt ℝ f x) (value : ℝ)
    (hd : HasDerivAt (fun t => f (Function.update x axis t)) value (x axis)) :
    (fderiv ℝ f x) (Pi.single axis 1) = value := by
  have hu : HasDerivAt (Function.update x axis) (Pi.single axis 1) (x axis) := by
    have he : (ContinuousLinearMap.pi (Pi.single axis (ContinuousLinearMap.id ℝ ℝ))) 1 =
        (Pi.single axis 1 : Fin 3 → ℝ) := by
      ext direction
      by_cases h : direction = axis
      · subst direction; simp
      · simp [h]
    have hu := (hasFDerivAt_update (𝕜 := ℝ) x (i := axis) (x axis)).hasDerivAt
    rw [he] at hu
    exact hu
  have hc := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x axis) hu (Function.update_eq_self axis x).symm
  simpa only [Function.update_eq_self] using hc.unique hd

theorem linear_apply_coordinates (f : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    f v = ∑ axis : Fin 3, f (Pi.single axis 1) * v axis := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro axis _
  have hsingle : Pi.single axis (v axis) = v axis • (Pi.single axis 1 : Fin 3 → ℝ) := by
    ext direction
    by_cases h : direction = axis
    · subst direction; simp
    · simp [h]
  rw [hsingle, map_smul]
  simp only [smul_eq_mul, mul_comm]

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousGradient

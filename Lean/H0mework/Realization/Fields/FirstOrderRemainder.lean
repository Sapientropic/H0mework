import Mathlib.Analysis.Calculus.MeanValue

/-! The reusable first-order estimate. Its original declaration identity is
preserved for the existing molecular flow consumers. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.FiniteRemainder

open Set

theorem firstOrder_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f velocity acceleration : ℝ → E) (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (first : ∀ s, HasDerivAt f (velocity s) s)
    (second : ∀ s, HasDerivAt velocity (acceleration s) s)
    (bound : ∀ s ∈ Icc 0 t, ‖acceleration s‖ ≤ C) :
    ‖f t - f 0 - t • velocity 0‖ ≤ C * t ^ 2 := by
  have velocityBound (s : ℝ) (hs : s ∈ Icc 0 t) : ‖velocity s - velocity 0‖ ≤ C * t := by
    have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x (_ : x ∈ Icc 0 t) => (second x).hasDerivWithinAt)
      (fun x (hx : x ∈ Ico 0 t) => bound x (Ico_subset_Icc_self hx)) s hs
    simp only [sub_zero] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left hs.2 hC)
  let remainder (s : ℝ) := f s - f 0 - s • velocity 0
  have derivative (s : ℝ) : HasDerivAt remainder (velocity s - velocity 0) s := by
    simpa only [remainder, Pi.sub_def, one_smul, id_eq] using
      ((first s).sub_const (f 0)).sub ((hasDerivAt_id s).smul_const (velocity 0))
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (_ : x ∈ Icc 0 t) => (derivative x).hasDerivWithinAt)
    (fun x (hx : x ∈ Ico 0 t) => velocityBound x (Ico_subset_Icc_self hx)) t ⟨ht, le_rfl⟩
  simpa [remainder, pow_two, mul_assoc] using estimate

end LAlanine40K2025.Thermal.Load.Producer.FiniteRemainder
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

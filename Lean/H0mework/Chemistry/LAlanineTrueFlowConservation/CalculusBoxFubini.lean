import Mathlib.MeasureTheory.Integral.Pi

/-! The existing product-measure Fubini consumer, in the original Fin 3 time coordinate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LAlanineTrueFlowConservation

open Set MeasureTheory
noncomputable section

private theorem box_time_measurePreserving (lower upper : Fin 3 → ℝ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
      (((volume : Measure ℝ).restrict (Icc (lower 2) (upper 2))).prod
        (volume.restrict (Icc (lower ∘ (2 : Fin 3).succAbove)
          (upper ∘ (2 : Fin 3).succAbove))))
      (volume.restrict (Icc lower upper)) := by
  have split := (measurePreserving_piFinSuccAbove
    (fun i : Fin 3 => (volume : Measure ℝ).restrict (Icc (lower i) (upper i))) 2).symm
  simpa only [← Measure.restrict_pi_pi, pi_univ_Icc] using! split

theorem integral_box_time (lower upper : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (integrable : IntegrableOn f (Icc lower upper)) :
    (∫ x in Icc lower upper, f x) =
      ∫ p in Icc (lower ∘ (2 : Fin 3).succAbove) (upper ∘ (2 : Fin 3).succAbove),
        ∫ t in Icc (lower 2) (upper 2), f ((2 : Fin 3).insertNth t p) := by
  have transformed := (box_time_measurePreserving lower upper).integrable_comp_of_integrable integrable
  rw [← (box_time_measurePreserving lower upper).integral_comp' f]
  exact integral_prod_symm _ transformed

theorem integrable_box_time (lower upper : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (integrable : IntegrableOn f (Icc lower upper)) :
    IntegrableOn (fun p => ∫ t in Icc (lower 2) (upper 2), f ((2 : Fin 3).insertNth t p))
      (Icc (lower ∘ (2 : Fin 3).succAbove) (upper ∘ (2 : Fin 3).succAbove)) :=
  ((box_time_measurePreserving lower upper).integrable_comp_of_integrable integrable).integral_prod_right

end
end LAlanineTrueFlowConservation

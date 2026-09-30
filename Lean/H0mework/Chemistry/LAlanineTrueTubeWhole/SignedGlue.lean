import H0mework.Chemistry.LAlanineTrueTubeWhole.SignedReparametrize

set_option autoImplicit false

namespace LAlanineTrueTube.Signed

open Set Filter
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem full_left_derivative {negative positive : ℝ → E} {field : E → E} {h s : ℝ}
    (law : IsIntegralCurveOn negative (fun _ x => -field x) (Icc 0 h))
    (time : s ∈ Icc (-h) 0) :
    HasDerivWithinAt (full negative positive) (field (full negative positive s))
      (Icc (-h) 0) s := by
  rw [full_left _ _ _ time.2]
  exact (reversed_integralCurve law s time).congr_of_mem
    (fun t ht => full_left _ _ _ ht.2) time

theorem full_right_derivative {negative positive : ℝ → E} {field : E → E} {h s : ℝ}
    (same : negative 0 = positive 0)
    (law : IsIntegralCurveOn positive (fun _ => field) (Icc 0 h))
    (time : s ∈ Icc 0 h) :
    HasDerivWithinAt (full negative positive) (field (full negative positive s))
      (Icc 0 h) s := by
  rw [full_right same _ time.1]
  exact (law s time).congr_of_mem (fun t ht => full_right same _ ht.1) time

theorem full_integralCurve {negative positive : ℝ → E} {field : E → E} {h : ℝ}
    (nonnegative : 0 ≤ h) (same : negative 0 = positive 0)
    (left : IsIntegralCurveOn negative (fun _ x => -field x) (Icc 0 h))
    (right : IsIntegralCurveOn positive (fun _ => field) (Icc 0 h)) :
    IsIntegralCurveOn (full negative positive) (fun _ => field) (Icc (-h) h) := by
  intro s time
  rcases lt_trichotomy s 0 with negativeTime | zeroTime | positiveTime
  · have derivative := full_left_derivative (positive := positive) left
      (show s ∈ Icc (-h) 0 from ⟨time.1, negativeTime.le⟩)
    apply derivative.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds negativeTime)]
      with t ht hneg
    exact ⟨ht.1, hneg⟩
  · subst s
    have derivative := (full_left_derivative (positive := positive) left
      (show (0 : ℝ) ∈ Icc (-h) 0 from ⟨neg_nonpos.mpr nonnegative, le_rfl⟩)).union
      (full_right_derivative same right ⟨le_rfl, nonnegative⟩)
    simpa only [Icc_union_Icc_eq_Icc (neg_nonpos.mpr nonnegative) nonnegative] using derivative
  · have derivative := full_right_derivative same right
      (show s ∈ Icc 0 h from ⟨positiveTime.le, time.2⟩)
    apply derivative.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ici_mem_nhds positiveTime)]
      with t ht hpos
    exact ⟨hpos, ht.2⟩

theorem full_hasDerivAt_zero {negative positive : ℝ → E} {field : E → E} {h : ℝ}
    (positiveLength : 0 < h) (same : negative 0 = positive 0)
    (left : IsIntegralCurveOn negative (fun _ x => -field x) (Icc 0 h))
    (right : IsIntegralCurveOn positive (fun _ => field) (Icc 0 h)) :
    HasDerivAt (full negative positive) (field (negative 0)) 0 := by
  have derivative := full_integralCurve positiveLength.le same left right 0
    ⟨neg_nonpos.mpr positiveLength.le, positiveLength.le⟩
  simpa only [full_zero] using
    derivative.hasDerivAt (Icc_mem_nhds (neg_lt_zero.mpr positiveLength) positiveLength)

end
end LAlanineTrueTube.Signed

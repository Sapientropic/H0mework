import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.KernelBilinear

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadSum

open Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeCompleteStressCarrier NativeHigherTimeJets NativeUnheatedPairInverseFlux

noncomputable section
abbrev E := ComplexVorticityHilbertState

def weights : lp (fun _ : IntegerWavevector => ℝ) 2 :=
  ⟨weight, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using weight_summable⟩

def rowNorms (value : E) : lp (fun _ : IntegerWavevector => ℝ) 2 :=
  ⟨fun c => ‖value c‖, value.2.norm⟩

theorem rowNorms_norm (value : E) : ‖rowNorms value‖ = ‖value‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro c
    exact (Real.norm_of_nonneg (norm_nonneg (value c))).le
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro c
    exact (Real.norm_of_nonneg (norm_nonneg (value c))).ge

theorem weighted_summable (value : E) : Summable (fun c => weight c * ‖value c‖) := by
  have paid := lp.summable_mul (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
    rw [Real.holderConjugate_iff]; norm_num) weights (rowNorms value)
  simpa only [weights, rowNorms, Real.norm_of_nonneg (weight_pos _).le, Real.norm_of_nonneg (norm_nonneg _)] using paid

theorem weighted_bound (value : E) : (∑' c, weight c * ‖value c‖) ≤ ‖weights‖ * ‖value‖ := by
  have paid := lp.tsum_mul_le_mul_norm' (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
    rw [Real.holderConjugate_iff]; norm_num) weights (rowNorms value)
  rw [rowNorms_norm] at paid
  simpa only [weights, rowNorms, Real.norm_of_nonneg (weight_pos _).le, Real.norm_of_nonneg (norm_nonneg _)] using paid

variable (kernel : IntegerWavevector → IntegerWavevector → IntegerWavevector → ℂ)
  (cap : ℝ) (bounded : ∀ a b c, ‖kernel a b c‖ ≤ cap * weight c)
  (wave : IntegerWavevector) (i j l : Coordinate)

def innerTerm (left middle : E) (c a : IntegerWavevector) : ℂ :=
  kernel a (wave-c-a) c * (left a i * middle (wave-c-a) j)

def innerValue (left middle : E) (c : IntegerWavevector) : ℂ := ∑' a, innerTerm kernel wave i j left middle c a

def value (left middle right : E) : ℂ := ∑' c, innerValue kernel wave i j left middle c * right c l

include bounded

theorem cap_nonnegative : 0 ≤ cap := by
  have paid := (norm_nonneg (kernel 0 0 0)).trans (bounded 0 0 0)
  simpa only [weight, if_true, mul_one] using paid

theorem inner_summable (left middle : E) (c : IntegerWavevector) :
    Summable (innerTerm kernel wave i j left middle c) := by
  apply Summable.of_norm
  apply ((mixed_pair_summable left middle (wave-c) j i).norm.mul_left (cap * weight c)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro a
  rw [innerTerm, norm_mul]
  exact mul_le_mul_of_nonneg_right (bounded a (wave-c-a) c) (norm_nonneg _)

theorem inner_bound (left middle : E) (c : IntegerWavevector) :
    ‖innerValue kernel wave i j left middle c‖ ≤ (3 * cap * ‖left‖ * ‖middle‖) * weight c := by
  have sums := (inner_summable kernel cap bounded wave i j left middle c).norm
  apply (norm_tsum_le_tsum_norm sums).trans
  have upper := ((mixed_pair_summable left middle (wave-c) j i).norm.mul_left (cap * weight c))
  have compare := sums.tsum_le_tsum (fun a => by
    change ‖kernel a (wave-c-a) c * (left a i * middle (wave-c-a) j)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bounded _ _ _) (norm_nonneg _)) upper
  rw [tsum_mul_left] at compare
  exact compare.trans ((mul_le_mul_of_nonneg_left (absolute_pair_bound left middle (wave-c) j i)
    (mul_nonneg (cap_nonnegative kernel cap bounded) (weight_pos c).le)).trans_eq (by ring))

theorem outer_summable (left middle right : E) :
    Summable (fun c => innerValue kernel wave i j left middle c * right c l) := by
  apply Summable.of_norm
  apply ((weighted_summable right).mul_left (3 * cap * ‖left‖ * ‖middle‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro c
  rw [norm_mul]
  have first := inner_bound kernel cap bounded wave i j left middle c
  have coordinate := norm_le_pi_norm (right c) l
  exact (mul_le_mul first coordinate (norm_nonneg _) (by positivity [cap_nonnegative kernel cap bounded, weight_pos c])).trans_eq (by ring)

theorem norm_bound (left middle right : E) :
    ‖value kernel wave i j l left middle right‖ ≤
      (3 * cap * ‖weights‖) * ‖left‖ * ‖middle‖ * ‖right‖ := by
  have sums := (outer_summable kernel cap bounded wave i j l left middle right).norm
  apply (norm_tsum_le_tsum_norm sums).trans
  have compare := sums.tsum_le_tsum (fun c => by
    rw [norm_mul]
    have first := inner_bound kernel cap bounded wave i j left middle c
    exact (mul_le_mul first (norm_le_pi_norm (right c) l) (norm_nonneg _)
      (by positivity [cap_nonnegative kernel cap bounded, weight_pos c])).trans_eq (by ring))
    ((weighted_summable right).mul_left (3 * cap * ‖left‖ * ‖middle‖))
  rw [tsum_mul_left] at compare
  exact compare.trans ((mul_le_mul_of_nonneg_left (weighted_bound right)
    (by positivity [cap_nonnegative kernel cap bounded])).trans_eq (by ring))

theorem inner_add_left (left other middle : E) (c : IntegerWavevector) :
    innerValue kernel wave i j (left+other) middle c =
      innerValue kernel wave i j left middle c + innerValue kernel wave i j other middle c := by
  simp only [innerValue, innerTerm, lp.coeFn_add, Pi.add_apply, add_mul, mul_add]
  exact (inner_summable kernel cap bounded wave i j left middle c).tsum_add
    (inner_summable kernel cap bounded wave i j other middle c)

theorem inner_add_middle (left middle other : E) (c : IntegerWavevector) :
    innerValue kernel wave i j left (middle+other) c =
      innerValue kernel wave i j left middle c + innerValue kernel wave i j left other c := by
  simp only [innerValue, innerTerm, lp.coeFn_add, Pi.add_apply, mul_add]
  exact (inner_summable kernel cap bounded wave i j left middle c).tsum_add
    (inner_summable kernel cap bounded wave i j left other c)

theorem add_left (left other middle right : E) :
    value kernel wave i j l (left+other) middle right =
      value kernel wave i j l left middle right + value kernel wave i j l other middle right := by
  simp only [value, inner_add_left kernel cap bounded, add_mul]
  exact (outer_summable kernel cap bounded wave i j l left middle right).tsum_add
    (outer_summable kernel cap bounded wave i j l other middle right)

theorem add_middle (left middle other right : E) :
    value kernel wave i j l left (middle+other) right =
      value kernel wave i j l left middle right + value kernel wave i j l left other right := by
  simp only [value, inner_add_middle kernel cap bounded, add_mul]
  exact (outer_summable kernel cap bounded wave i j l left middle right).tsum_add
    (outer_summable kernel cap bounded wave i j l left other right)

theorem add_right (left middle right other : E) :
    value kernel wave i j l left middle (right+other) =
      value kernel wave i j l left middle right + value kernel wave i j l left middle other := by
  simp only [value, lp.coeFn_add, Pi.add_apply, mul_add]
  exact (outer_summable kernel cap bounded wave i j l left middle right).tsum_add
    (outer_summable kernel cap bounded wave i j l left middle other)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadSum

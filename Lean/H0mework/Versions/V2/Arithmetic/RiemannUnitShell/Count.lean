import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.FirstCurrent
import Mathlib.NumberTheory.AbelSummation

/-! The original reciprocal interval source generates exact integer counts, including its actual mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

/-- The actual reciprocal of the half-open unit interval source. -/
def burnolReciprocalStepSourceRaw (lower upper : ℝ) (x : ℝ) : ℂ :=
  if lower ≤ |x|⁻¹ ∧ |x|⁻¹ < upper then ((|x| : ℝ) : ℂ)⁻¹ else 0

def burnolReciprocalStepChannels (lower upper x : ℝ) : Finset ℕ :=
  Finset.Ico ⌈lower * |x|⌉₊ ⌈upper * |x|⌉₊

theorem burnolReciprocalStep_source_term (lower upper x : ℝ) (nonzero : x ≠ 0) (n : ℕ+) :
    (((n : ℕ) : ℂ)⁻¹) * burnolReciprocalStepSourceRaw lower upper (x / (n : ℕ)) =
      if (n : ℕ) ∈ burnolReciprocalStepChannels lower upper x then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have nPositive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have reciprocal : |x / (n : ℕ)|⁻¹ = ((n : ℕ) : ℝ) / |x| := by
    rw [abs_div, abs_of_pos nPositive, inv_div]
  have incidence : lower ≤ |x / (n : ℕ)|⁻¹ ∧ |x / (n : ℕ)|⁻¹ < upper ↔
      (n : ℕ) ∈ burnolReciprocalStepChannels lower upper x := by
    rw [reciprocal]
    simp only [burnolReciprocalStepChannels, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]
    rw [le_div_iff₀ positive, div_lt_iff₀ positive]
  unfold burnolReciprocalStepSourceRaw
  simp only [incidence]
  split_ifs
  · rw [← Complex.ofReal_inv, reciprocal, Complex.ofReal_div]
    push_cast
    field_simp
  · exact mul_zero _

theorem burnolReciprocalStep_forward_count (lower upper x : ℝ) (lowerPositive : 0 < lower)
    (nonzero : x ≠ 0) :
    burnolInnerGapForward (burnolReciprocalStepSourceRaw lower upper) x =
      ((burnolReciprocalStepChannels lower upper x).card : ℂ) * ((|x| : ℝ) : ℂ)⁻¹ := by
  classical
  let term : ℕ → ℂ := fun n =>
    if n ∈ burnolReciprocalStepChannels lower upper x then ((|x| : ℝ) : ℂ)⁻¹ else 0
  have support : Function.support term ⊆ {n : ℕ | 0 < n} := by
    intro n active
    have belongs : n ∈ burnolReciprocalStepChannels lower upper x := by
      by_contra outside
      exact active (if_neg outside)
    have lowerBound := (Finset.mem_Ico.mp belongs).1
    exact lt_of_lt_of_le (Nat.ceil_pos.mpr (mul_pos lowerPositive (abs_pos.mpr nonzero))) lowerBound
  calc
    _ = ∑' n : ℕ+, term (n : ℕ) := by
      apply tsum_congr
      exact burnolReciprocalStep_source_term lower upper x nonzero
    _ = ∑' n : ℕ, term n := tsum_subtype_eq_of_support_subset support
    _ = ∑ n ∈ burnolReciprocalStepChannels lower upper x, term n :=
      tsum_eq_sum (fun n outside => if_neg outside)
    _ = _ := by
      simp only [term, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]

def burnolReciprocalStepWaveReal (lower upper x : ℝ) : ℝ :=
  if x = 0 then lower - upper else
    ((burnolReciprocalStepChannels lower upper x).card : ℝ) / |x| - (upper - lower)

def burnolReciprocalStepWaveRaw (lower upper x : ℝ) : ℂ := burnolReciprocalStepWaveReal lower upper x

theorem burnolReciprocalStepWave_coSum (lower upper x : ℝ) (lowerPositive : 0 < lower) :
    burnolReciprocalStepWaveRaw lower upper x =
      burnolInnerGapForward (burnolReciprocalStepSourceRaw lower upper) x - (upper - lower : ℂ) := by
  by_cases atZero : x = 0
  · subst x
    have sourceZero : burnolReciprocalStepSourceRaw lower upper 0 = 0 := by
      simp [burnolReciprocalStepSourceRaw, lowerPositive.not_ge]
    simp [burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal, burnolInnerGapForward, sourceZero]
  · rw [burnolReciprocalStep_forward_count lower upper x lowerPositive atZero]
    unfold burnolReciprocalStepWaveRaw burnolReciprocalStepWaveReal
    rw [if_neg atZero]
    push_cast
    rw [div_eq_mul_inv]

theorem burnolReciprocalStepWave_bound (lower upper x : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) (nonzero : x ≠ 0) :
    ‖burnolReciprocalStepWaveRaw lower upper x‖ ≤ |x|⁻¹ := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have upperPositive : 0 < upper := lowerPositive.trans_le ordered
  have indexOrder : ⌈lower * |x|⌉₊ ≤ ⌈upper * |x|⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right ordered positive.le)
  have l₀ := Nat.le_ceil (lower * |x|)
  have u₀ := Nat.le_ceil (upper * |x|)
  have l₁ := Nat.ceil_lt_add_one (mul_pos lowerPositive positive).le
  have u₁ := Nat.ceil_lt_add_one (mul_pos upperPositive positive).le
  unfold burnolReciprocalStepWaveRaw burnolReciprocalStepWaveReal burnolReciprocalStepChannels
  rw [if_neg nonzero, Nat.card_Ico, Nat.cast_sub indexOrder,
    Complex.norm_real, Real.norm_eq_abs]
  have expression : ((⌈upper * |x|⌉₊ : ℝ) - (⌈lower * |x|⌉₊ : ℝ)) / |x| - (upper - lower) =
      ((⌈upper * |x|⌉₊ : ℝ) - (⌈lower * |x|⌉₊ : ℝ) - (upper - lower) * |x|) / |x| := by
    field_simp
  rw [expression, abs_div, abs_of_pos positive, inv_eq_one_div,
    div_le_div_iff_of_pos_right positive, abs_le]
  constructor <;> nlinarith

theorem burnolReciprocalStepWave_small (lower upper x : ℝ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) (small : |x| ≤ upper⁻¹) :
    burnolReciprocalStepWaveRaw lower upper x = (lower - upper : ℂ) := by
  by_cases zero : x = 0
  · subst x
    simp [burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal]
  have positive : 0 < |x| := abs_pos.mpr zero
  have upperPositive : 0 < upper := lowerPositive.trans_le ordered
  have upperSmall : upper * |x| ≤ 1 := by
    rw [inv_eq_one_div, le_div_iff₀ upperPositive] at small
    nlinarith
  have lowerSmall : lower * |x| ≤ 1 :=
    (mul_le_mul_of_nonneg_right ordered positive.le).trans upperSmall
  have lowerIndex : ⌈lower * |x|⌉₊ = 1 :=
    (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr
      ⟨by simpa using mul_pos lowerPositive positive, by simpa using lowerSmall⟩
  have upperIndex : ⌈upper * |x|⌉₊ = 1 :=
    (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr
      ⟨by simpa using mul_pos upperPositive positive, by simpa using upperSmall⟩
  simp [burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal, zero, burnolReciprocalStepChannels, lowerIndex, upperIndex]

theorem burnolReciprocalStepWave_measurable (lower upper : ℝ) :
    Measurable (burnolReciprocalStepWaveRaw lower upper) := by
  unfold burnolReciprocalStepWaveRaw burnolReciprocalStepWaveReal burnolReciprocalStepChannels
  simp only [Nat.card_Ico]
  apply Complex.measurable_ofReal.comp
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  fun_prop

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.X.NavierStokes.SourceAction.FinitePrefixChart

set_option autoImplicit false
open scoped Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryClock

open Set
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

def duration (length : ℕ) : ℝ := WholePrefixState.duration stackedShortCurrent length

theorem duration_pos (length : ℕ) : 0 < duration length := WholePrefixState.duration_pos _ _

theorem duration_strictMono : StrictMono duration := by
  intro first last ordered
  exact elapsedTime_strictMono stackedShortCurrent (Nat.add_lt_add_right ordered 1)

def fraction (time : ℝ) : ℝ := time / (1 + time)

theorem fraction_pos {time : ℝ} (positive : 0 < time) : 0 < fraction time :=
  div_pos positive (by linarith)

theorem fraction_lt_one {time : ℝ} (nonnegative : 0 ≤ time) : fraction time < 1 := by
  exact (div_lt_one (by linarith : 0 < 1 + time)).mpr (by linarith)

theorem fraction_strict {first last : ℝ} (nonnegative : 0 ≤ first) (ordered : first < last) :
    fraction first < fraction last := by
  unfold fraction
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + first) (by linarith : 0 < 1 + last)).mpr
  nlinarith

def clockRange : Set ℝ := range (fun length => fraction (duration length))

theorem clockRange_nonempty : clockRange.Nonempty := range_nonempty _

theorem clockRange_bounded : BddAbove clockRange := by
  refine ⟨1, ?_⟩
  rintro _ ⟨length, rfl⟩
  exact (fraction_lt_one (duration_pos length).le).le

def ceiling : ℝ := sSup clockRange

theorem duration_fraction_le (length : ℕ) : fraction (duration length) ≤ ceiling :=
  le_csSup clockRange_bounded (mem_range_self length)

theorem ceiling_pos : 0 < ceiling := (fraction_pos (duration_pos 0)).trans_le (duration_fraction_le 0)

theorem ceiling_le_one : ceiling ≤ 1 := by
  apply csSup_le clockRange_nonempty
  rintro _ ⟨length, rfl⟩
  exact (fraction_lt_one (duration_pos length).le).le

theorem duration_fraction_lt (length : ℕ) : fraction (duration length) < ceiling :=
  (fraction_strict (duration_pos length).le (duration_strictMono (Nat.lt_succ_self length))).trans_le
    (duration_fraction_le (length + 1))

def clockFraction (parameter : ℝ) : ℝ := ceiling * Real.sigmoid parameter

theorem clockFraction_pos (parameter : ℝ) : 0 < clockFraction parameter :=
  mul_pos ceiling_pos (Real.sigmoid_pos parameter)

theorem clockFraction_lt_ceiling (parameter : ℝ) : clockFraction parameter < ceiling := by
  exact (mul_lt_mul_of_pos_left (Real.sigmoid_lt_one parameter) ceiling_pos).trans_eq (mul_one _)

theorem clockFraction_lt_one (parameter : ℝ) : clockFraction parameter < 1 :=
  (clockFraction_lt_ceiling parameter).trans_le ceiling_le_one

def physicalTime (parameter : ℝ) : ℝ := clockFraction parameter / (1 - clockFraction parameter)

theorem physicalTime_pos (parameter : ℝ) : 0 < physicalTime parameter :=
  div_pos (clockFraction_pos parameter) (sub_pos.mpr (clockFraction_lt_one parameter))

theorem exists_cover (parameter : ℝ) : ∃ length : ℕ, physicalTime parameter < duration length := by
  obtain ⟨value, ⟨length, rfl⟩, less⟩ :=
    exists_lt_of_lt_csSup clockRange_nonempty (clockFraction_lt_ceiling parameter)
  refine ⟨length, ?_⟩
  have scaled := (lt_div_iff₀ (by linarith [duration_pos length] : 0 < 1 + duration length)).mp less
  apply (div_lt_iff₀ (sub_pos.mpr (clockFraction_lt_one parameter))).mpr
  nlinarith

def cover (parameter : ℝ) : ℕ := Nat.find (exists_cover parameter)

theorem cover_spec (parameter : ℝ) : physicalTime parameter < duration (cover parameter) :=
  Nat.find_spec (exists_cover parameter)

def clockRate (parameter : ℝ) : ℝ :=
  (ceiling * (Real.sigmoid parameter * (1 - Real.sigmoid parameter))) / (1 - clockFraction parameter) ^ 2

theorem clockRate_pos (parameter : ℝ) : 0 < clockRate parameter :=
  div_pos (mul_pos ceiling_pos (mul_pos (Real.sigmoid_pos parameter) (sub_pos.mpr (Real.sigmoid_lt_one parameter))))
    (sq_pos_of_pos (sub_pos.mpr (clockFraction_lt_one parameter)))

theorem physicalTime_contDiff : ContDiff ℝ ∞ physicalTime := by
  have fractionSmooth : ContDiff ℝ ∞ clockFraction := contDiff_const.mul (contDiff_sigmoid.of_le le_top)
  exact fractionSmooth.div (contDiff_const.sub fractionSmooth) (fun parameter => (sub_pos.mpr (clockFraction_lt_one parameter)).ne')

theorem physicalTime_hasDerivAt (parameter : ℝ) : HasDerivAt physicalTime (clockRate parameter) parameter := by
  have fractional := (Real.hasDerivAt_sigmoid parameter).const_mul ceiling
  have denominator := (hasDerivAt_const parameter (1 : ℝ)).sub fractional
  have actual := fractional.div denominator (sub_pos.mpr (clockFraction_lt_one parameter)).ne'
  convert! actual using 1
  dsimp [clockRate, clockFraction]
  ring

def physicalDomain : Set ℝ := {actual | 0 < actual ∧ fraction actual < ceiling}

def inverseTime (actual : ℝ) : ℝ := -Real.log ((fraction actual / ceiling)⁻¹ - 1)

theorem clockFraction_inverse (actual : ℝ) (inside : actual ∈ physicalDomain) :
    clockFraction (inverseTime actual) = fraction actual := by
  have ratioPositive : 0 < fraction actual / ceiling := div_pos (fraction_pos inside.1) ceiling_pos
  have ratioLt : fraction actual / ceiling < 1 := (div_lt_one ceiling_pos).mpr inside.2
  have logPositive : 0 < (fraction actual / ceiling)⁻¹ - 1 := by
    rw [sub_pos, one_lt_inv_iff₀]
    exact ⟨ratioPositive, ratioLt⟩
  simp only [clockFraction, inverseTime, Real.sigmoid, neg_neg, Real.exp_log logPositive]
  rw [show 1 + ((fraction actual / ceiling)⁻¹ - 1) = (fraction actual / ceiling)⁻¹ by ring, inv_inv]
  exact mul_div_cancel₀ _ ceiling_pos.ne'

theorem physicalTime_inverse (actual : ℝ) (inside : actual ∈ physicalDomain) :
    physicalTime (inverseTime actual) = actual := by
  rw [physicalTime, clockFraction_inverse actual inside]
  unfold fraction
  have nonzero : 1 + actual ≠ 0 := (by linarith [inside.1] : 0 < 1 + actual).ne'
  field_simp
  ring

theorem physicalTime_injective : Function.Injective physicalTime := by
  intro first last same
  have dFirst := (sub_pos.mpr (clockFraction_lt_one first)).ne'
  have dLast := (sub_pos.mpr (clockFraction_lt_one last)).ne'
  have fractions : clockFraction first = clockFraction last := by
    have equality := (div_eq_div_iff dFirst dLast).mp same
    nlinarith
  exact Real.sigmoid_injective (mul_left_cancel₀ ceiling_pos.ne' fractions)

theorem physicalTime_mem (parameter : ℝ) : physicalTime parameter ∈ physicalDomain := by
  refine ⟨physicalTime_pos parameter, ?_⟩
  have nonzero : 1 - clockFraction parameter ≠ 0 := (sub_pos.mpr (clockFraction_lt_one parameter)).ne'
  have denominator : 1 + physicalTime parameter = (1 - clockFraction parameter)⁻¹ := by
    unfold physicalTime
    field_simp [nonzero]
    ring
  have same : fraction (physicalTime parameter) = clockFraction parameter := by
    rw [fraction, denominator]
    unfold physicalTime
    field_simp [nonzero]
  exact same ▸ clockFraction_lt_ceiling parameter

theorem inverseTime_physicalTime (parameter : ℝ) : inverseTime (physicalTime parameter) = parameter :=
  physicalTime_injective (physicalTime_inverse _ (physicalTime_mem parameter))

theorem duration_mem (length : ℕ) : duration length ∈ physicalDomain :=
  ⟨duration_pos length, duration_fraction_lt length⟩

theorem physicalDomain_of_le_duration (length : ℕ) (actual : ℝ) (positive : 0 < actual)
    (before : actual ≤ duration length) : actual ∈ physicalDomain := by
  refine ⟨positive, ?_⟩
  rcases lt_or_eq_of_le before with earlier | endpoint
  · exact (fraction_strict positive.le earlier).trans (duration_fraction_lt length)
  · rw [endpoint]
    exact duration_fraction_lt length

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryClock

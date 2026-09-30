import H0mework.NavierStokes.SourceAction.PressureWholeConvolution
import H0mework.NavierStokes.SourceReadout.Action

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeFullOrderAction

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeStressSource

noncomputable section

abbrev ScalarL2 := lp (fun _ : IntegerWavevector => ℝ) 2

def translated (field : ScalarL2) (offset : IntegerWavevector) : ScalarL2 :=
  ⟨fun wave => field (wave - offset), memℓp_gen <| by
    simpa [Equiv.subRight, Function.comp_def] using
      (Equiv.subRight offset).summable_iff.mpr (lp.memℓp field |>.summable (by norm_num))⟩

theorem translated_norm (field : ScalarL2) (offset : IntegerWavevector) :
    ‖translated field offset‖ = ‖field‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.subRight offset).tsum_eq (fun wave => ‖field wave‖ ^ (2 : ℝ))

def convolution (left : IntegerWavevector → ℝ) (right : ScalarL2) : ScalarL2 :=
  ∑' wave, left wave • translated right wave

theorem convolution_summable (left : IntegerWavevector → ℝ) (right : ScalarL2)
    (paid : Summable left) : Summable fun wave => left wave • translated right wave := by
  apply Summable.of_norm
  simp only [norm_smul, translated_norm]
  exact paid.norm.mul_right _

theorem convolution_apply (left : IntegerWavevector → ℝ) (right : ScalarL2)
    (paid : Summable left) (wave : IntegerWavevector) :
    convolution left right wave = ∑' first, left first * right (wave - first) := by
  exact (lp.evalCLM ℝ (fun _ : IntegerWavevector => ℝ) 2 wave).map_tsum
    (convolution_summable left right paid)

theorem convolution_row_summable (left : IntegerWavevector → ℝ) (right : ScalarL2)
    (paid : Summable left) (wave : IntegerWavevector) :
    Summable fun first => left first * right (wave - first) := by
  apply (paid.norm.mul_right ‖right‖).of_norm_bounded
  intro first
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) right _) (norm_nonneg _)

theorem convolution_norm_le (left : IntegerWavevector → ℝ) (right : ScalarL2)
    (paid : Summable left) :
    ‖convolution left right‖ ≤ (∑' wave, ‖left wave‖) * ‖right‖ := by
  calc
    _ ≤ ∑' wave, ‖left wave • translated right wave‖ :=
      norm_tsum_le_tsum_norm (by
        simp only [norm_smul, translated_norm]
        exact paid.norm.mul_right _)
    _ = _ := by simp only [norm_smul, translated_norm, tsum_mul_right]

def frequencySize (wave : IntegerWavevector) : ℝ := 1 + ∑ coordinate, |(wave coordinate : ℝ)|

theorem frequencySize_nonneg (wave : IntegerWavevector) : 0 ≤ frequencySize wave := by
  unfold frequencySize
  positivity

theorem frequencySize_add_le (left right : IntegerWavevector) :
    frequencySize (left + right) ≤ frequencySize left + frequencySize right := by
  have bound : (∑ coordinate : Fin 3, |((left + right) coordinate : ℝ)|) ≤
      ∑ coordinate : Fin 3, (|(left coordinate : ℝ)| + |(right coordinate : ℝ)|) := by
    apply Finset.sum_le_sum
    intro coordinate _
    simpa only [Pi.add_apply, Int.cast_add] using
      abs_add_le (left coordinate : ℝ) (right coordinate : ℝ)
  rw [Finset.sum_add_distrib] at bound
  unfold frequencySize
  linarith

def wordWeight (order : ℕ) (ceiling : ℝ) (wave : IntegerWavevector) : ℝ :=
  min (frequencySize wave) ceiling ^ order

theorem wordWeight_nonneg (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (wave : IntegerWavevector) : 0 ≤ wordWeight order ceiling wave :=
  pow_nonneg (le_min (frequencySize_nonneg wave) nonnegative) _

theorem wordWeight_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (wave : IntegerWavevector) : wordWeight order ceiling wave ≤ ceiling ^ order :=
  pow_le_pow_left₀ (le_min (frequencySize_nonneg wave) nonnegative) (min_le_right _ _) _

private theorem min_add_le (a b ceiling : ℝ) (aNonneg : 0 ≤ a) (bNonneg : 0 ≤ b)
    (ceilingNonneg : 0 ≤ ceiling) :
    min (a + b) ceiling ≤ min a ceiling + min b ceiling := by
  by_cases first : a ≤ ceiling
  · by_cases second : b ≤ ceiling
    · rw [min_eq_left first, min_eq_left second]
      exact min_le_left _ _
    · rw [min_eq_left first, min_eq_right (le_of_not_ge second)]
      exact (min_le_right _ _).trans (le_add_of_nonneg_left aNonneg)
  · rw [min_eq_right (le_of_not_ge first)]
    by_cases second : b ≤ ceiling
    · rw [min_eq_left second]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right bNonneg)
    · rw [min_eq_right (le_of_not_ge second)]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right ceilingNonneg)

theorem wordWeight_add_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (left right : IntegerWavevector) :
    wordWeight order ceiling (left + right) ≤
      2 ^ order * (wordWeight order ceiling left + wordWeight order ceiling right) := by
  let a := min (frequencySize left) ceiling
  let b := min (frequencySize right) ceiling
  have aNonneg : 0 ≤ a := le_min (frequencySize_nonneg left) nonnegative
  have bNonneg : 0 ≤ b := le_min (frequencySize_nonneg right) nonnegative
  have base : min (frequencySize (left + right)) ceiling ≤ a + b :=
    (min_le_min_right ceiling (frequencySize_add_le left right)).trans
      (min_add_le _ _ _ (frequencySize_nonneg left) (frequencySize_nonneg right) nonnegative)
  calc
    _ ≤ (a + b) ^ order := pow_le_pow_left₀
      (le_min (frequencySize_nonneg _) nonnegative) base _
    _ ≤ (2 * max a b) ^ order := pow_le_pow_left₀ (add_nonneg aNonneg bNonneg)
      (by linarith [le_max_left a b, le_max_right a b]) _
    _ = 2 ^ order * (max a b) ^ order := mul_pow _ _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total a b with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (pow_nonneg aNonneg _)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (pow_nonneg bNonneg _)

def weighted (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling) : ScalarL2 →L[ℝ] ScalarL2 :=
  lp.mapCLM 2 (fun wave => wordWeight order ceiling wave • ContinuousLinearMap.id ℝ ℝ)
    (pow_nonneg nonnegative order) (fun wave => by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wordWeight_nonneg order ceiling nonnegative wave)]
        using wordWeight_le order ceiling nonnegative wave)

@[simp] theorem weighted_apply (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (field : ScalarL2) (wave : IntegerWavevector) :
    weighted order ceiling nonnegative field wave = wordWeight order ceiling wave * field wave := rfl

theorem weighted_convolution_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (field : ScalarL2) (positive : ∀ wave, 0 ≤ field wave) (paid : Summable field)
    (wave : IntegerWavevector) :
    weighted order ceiling nonnegative (convolution field field) wave ≤
      (2 * 2 ^ order) * convolution field (weighted order ceiling nonnegative field) wave := by
  let w := wordWeight order ceiling
  have weightedNonneg (first) : 0 ≤ (weighted order ceiling nonnegative field) first :=
    mul_nonneg (wordWeight_nonneg _ _ nonnegative _) (positive _)
  have secondSum := convolution_row_summable field (weighted order ceiling nonnegative field) paid wave
  have firstSum : Summable fun first =>
      w first * field first * field (wave - first) := by
    have transformed := (Equiv.subLeft wave).summable_iff.mpr secondSum
    simpa [Function.comp_def, weighted_apply, mul_comm, mul_left_comm, mul_assoc] using transformed
  have swapped : (∑' first, w first * field first * field (wave - first)) =
      convolution field (weighted order ceiling nonnegative field) wave := by
    rw [convolution_apply _ _ paid]
    convert (Equiv.subLeft wave).tsum_eq
      (fun first => field first * (weighted order ceiling nonnegative field) (wave - first)) using 1
    simp [weighted_apply, w, mul_comm, mul_assoc]
  rw [weighted_apply, convolution_apply _ _ paid, ← tsum_mul_left]
  calc
    _ ≤ ∑' first, 2 ^ order *
        ((w first * field first * field (wave - first)) +
          field first * (weighted order ceiling nonnegative field) (wave - first)) := by
      apply ((convolution_row_summable field field paid wave).mul_left (w wave)).tsum_le_tsum _
        ((firstSum.add secondSum).mul_left (2 ^ order))
      intro first
      have source := wordWeight_add_le order ceiling nonnegative first (wave - first)
      rw [add_sub_cancel] at source
      have multiply := mul_le_mul_of_nonneg_right source
        (mul_nonneg (positive first) (positive (wave - first)))
      convert multiply using 1
      simp only [weighted_apply, w]
      ring
    _ = _ := by
      rw [tsum_mul_left, firstSum.tsum_add secondSum]
      rw [swapped, ← convolution_apply _ _ paid]
      ring

theorem weighted_convolution_norm_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (field : ScalarL2) (positive : ∀ wave, 0 ≤ field wave) (paid : Summable field) :
    ‖weighted order ceiling nonnegative (convolution field field)‖ ≤
      (2 * 2 ^ order) * (∑' wave, field wave) * ‖weighted order ceiling nonnegative field‖ := by
  have weightedNonneg (wave) : 0 ≤ (weighted order ceiling nonnegative field) wave :=
    mul_nonneg (wordWeight_nonneg _ _ nonnegative _) (positive _)
  have convolutionNonneg (right : ScalarL2) (h : ∀ wave, 0 ≤ right wave) (wave) :
      0 ≤ convolution field right wave := by
    rw [convolution_apply _ _ paid]
    exact tsum_nonneg fun first => mul_nonneg (positive _) (h _)
  have normLe : ‖weighted order ceiling nonnegative (convolution field field)‖ ≤
      ‖(2 * 2 ^ order : ℝ) • convolution field (weighted order ceiling nonnegative field)‖ := by
    apply lp.norm_mono (by norm_num)
    intro wave
    change |wordWeight order ceiling wave * convolution field field wave| ≤
      |(2 * 2 ^ order) * convolution field (weighted order ceiling nonnegative field) wave|
    rw [abs_of_nonneg (mul_nonneg
      (wordWeight_nonneg _ _ nonnegative _) (convolutionNonneg field positive wave))]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (convolutionNonneg _ weightedNonneg wave))]
    exact weighted_convolution_le order ceiling nonnegative field positive paid wave
  calc
    _ ≤ _ := normLe
    _ = (2 * 2 ^ order) * ‖convolution field (weighted order ceiling nonnegative field)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ _ := by
      have young := convolution_norm_le field (weighted order ceiling nonnegative field) paid
      simp only [Real.norm_eq_abs, abs_of_nonneg (positive _)] at young
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left young (by positivity : 0 ≤ (2 * 2 ^ order : ℝ))

def amplitude (velocity : ComplexVorticityHilbertState) : ScalarL2 :=
  ⟨vorticityRowAmplitude velocity, memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      summable_vorticityRowAmplitude_sq velocity⟩

private theorem coordinate_norm_le (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (coordinate : Fin 3) :
    ‖velocity wave coordinate‖ ≤ amplitude velocity wave := by
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)

theorem quadraticFlux_norm_le_convolution (velocity : ComplexVorticityHilbertState)
    (paid : Summable (amplitude velocity)) (wave : IntegerWavevector) (output input : Fin 3) :
    ‖quadraticFlux velocity wave output input‖ ≤ convolution (amplitude velocity) (amplitude velocity) wave := by
  rw [convolution_apply _ _ paid, quadraticFlux, norm_neg]
  apply (norm_tsum_le_tsum_norm (flux_pair_summable velocity wave output input).norm).trans
  apply (flux_pair_summable velocity wave output input).norm.tsum_le_tsum _
    (convolution_row_summable _ _ paid wave)
  intro first
  rw [norm_mul]
  exact mul_le_mul (coordinate_norm_le velocity first input)
    (coordinate_norm_le velocity (wave - first) output) (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)

def weightedFlux (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (velocity : ComplexVorticityHilbertState) (paid : Summable (amplitude velocity))
    (output input : Fin 3) : lp (fun _ : IntegerWavevector => ℂ) 2 :=
  ⟨fun wave => wordWeight order ceiling wave • quadraticFlux velocity wave output input,
    (lp.memℓp (weighted order ceiling nonnegative
      (convolution (amplitude velocity) (amplitude velocity)))).mono <| fun wave => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wordWeight_nonneg _ _ nonnegative _)]
        exact mul_le_mul_of_nonneg_left
          (quadraticFlux_norm_le_convolution velocity paid wave output input)
          (wordWeight_nonneg _ _ nonnegative _)⟩

theorem weightedFlux_norm_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (velocity : ComplexVorticityHilbertState) (paid : Summable (amplitude velocity))
    (output input : Fin 3) :
    ‖weightedFlux order ceiling nonnegative velocity paid output input‖ ≤
      (2 * 2 ^ order) * (∑' wave, amplitude velocity wave) *
        ‖weighted order ceiling nonnegative (amplitude velocity)‖ := by
  apply le_trans _ (weighted_convolution_norm_le order ceiling nonnegative (amplitude velocity)
    (vorticityRowAmplitude_nonneg velocity) paid)
  apply lp.norm_mono (by norm_num)
  intro wave
  change ‖wordWeight order ceiling wave • quadraticFlux velocity wave output input‖ ≤
    ‖wordWeight order ceiling wave * convolution (amplitude velocity) (amplitude velocity) wave‖
  rw [norm_smul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (wordWeight_nonneg _ _ nonnegative _)]
  apply mul_le_mul_of_nonneg_left _ (wordWeight_nonneg _ _ nonnegative _)
  exact (quadraticFlux_norm_le_convolution velocity paid wave output input).trans (Real.le_norm_self _)

theorem source_weightedFlux_norm_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (state : ComplexVorticityHilbertState)
    (gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (state wave))
    (output input : Fin 3) :
    ‖weightedFlux order ceiling nonnegative (wholeBiotSavartVelocityState state)
      (summable_wholeStateVelocityAmplitude state gradient) output input‖ ≤
      (2 * 2 ^ order) * wholeStateVelocityMajorant state *
        ‖weighted order ceiling nonnegative (amplitude (wholeBiotSavartVelocityState state))‖ :=
  weightedFlux_norm_le order ceiling nonnegative (wholeBiotSavartVelocityState state)
    (summable_wholeStateVelocityAmplitude state gradient) output input

end
end SaturationMonoid.NavierStokes.NativeFullOrderAction

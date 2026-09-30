import H0mework.NavierStokes.SourceAction.Flux
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeHigherTimeJets

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeStressSource NativeFullOrderAction NativeFullOrderFlux NativeFullOrderEvolution

noncomputable section

def mixedFlux (left right : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  fun wave output input => -∑' first, left first input * right (wave - first) output

theorem mixedFlux_diagonal (state : ComplexVorticityHilbertState) : mixedFlux state state = quadraticFlux state := rfl

private theorem coordinate_bound (state : ComplexVorticityHilbertState) (wave : IntegerWavevector)
    (coordinate : Coordinate) : ‖state wave coordinate‖ ≤ vorticityRowAmplitude state wave := by
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)

theorem mixed_pair_summable (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Summable fun first => left first input * right (wave - first) output := by
  apply Summable.of_norm
  apply (summable_fixedOutputVorticityAmplitudeProduct left right wave).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro first
  rw [norm_mul]
  exact mul_le_mul (coordinate_bound left first input) (coordinate_bound right (wave - first) output)
    (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)

theorem mixedFlux_norm_le (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖mixedFlux left right wave output input‖ ≤ 3 * ‖left‖ * ‖right‖ := by
  unfold mixedFlux
  rw [norm_neg]
  apply (norm_tsum_le_tsum_norm (mixed_pair_summable left right wave output input).norm).trans
  apply le_trans _ (tsum_fixedOutputVorticityAmplitudeProduct_le_three_mul_norm left right wave)
  apply (mixed_pair_summable left right wave output input).norm.tsum_le_tsum _
    (summable_fixedOutputVorticityAmplitudeProduct left right wave)
  intro first
  rw [norm_mul]
  exact mul_le_mul (coordinate_bound left first input) (coordinate_bound right (wave - first) output)
    (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)

theorem mixedFlux_add_left (left other right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    mixedFlux (left + other) right wave output input =
      mixedFlux left right wave output input + mixedFlux other right wave output input := by
  simp only [mixedFlux, lp.coeFn_add, Pi.add_apply, add_mul]
  rw [(mixed_pair_summable left right wave output input).tsum_add
    (mixed_pair_summable other right wave output input), neg_add]

theorem mixedFlux_add_right (left right other : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    mixedFlux left (right + other) wave output input =
      mixedFlux left right wave output input + mixedFlux left other wave output input := by
  simp only [mixedFlux, lp.coeFn_add, Pi.add_apply, mul_add]
  rw [(mixed_pair_summable left right wave output input).tsum_add
    (mixed_pair_summable left other wave output input), neg_add]

theorem mixedFlux_smul_left (scalar : ℝ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    mixedFlux (scalar • left) right wave output input = scalar • mixedFlux left right wave output input := by
  simp only [mixedFlux, lp.coeFn_smul, Pi.smul_apply, smul_mul_assoc, smul_neg]
  rw [Summable.tsum_const_smul scalar (mixed_pair_summable left right wave output input)]

theorem mixedFlux_smul_right (scalar : ℝ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    mixedFlux left (scalar • right) wave output input = scalar • mixedFlux left right wave output input := by
  simp only [mixedFlux, lp.coeFn_smul, Pi.smul_apply, mul_smul_comm, smul_neg]
  rw [Summable.tsum_const_smul scalar (mixed_pair_summable left right wave output input)]

def mixedFluxLinear (wave : IntegerWavevector) (output input : Coordinate) :
    ComplexVorticityHilbertState →ₗ[ℝ] ComplexVorticityHilbertState →ₗ[ℝ] ℂ where
  toFun left :=
    { toFun right := mixedFlux left right wave output input
      map_add' right other := mixedFlux_add_right left right other wave output input
      map_smul' scalar right := mixedFlux_smul_right scalar left right wave output input }
  map_add' left other := by
    ext right
    exact mixedFlux_add_left left other right wave output input
  map_smul' scalar left := by
    ext right
    exact mixedFlux_smul_left scalar left right wave output input

def mixedFluxCLM (wave : IntegerWavevector) (output input : Coordinate) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState →L[ℝ] ℂ :=
  (mixedFluxLinear wave output input).mkContinuous₂ 3
    (fun left right => mixedFlux_norm_le left right wave output input)

@[simp] theorem mixedFluxCLM_apply (wave : IntegerWavevector) (output input : Coordinate)
    (left right : ComplexVorticityHilbertState) :
    mixedFluxCLM wave output input left right = mixedFlux left right wave output input := rfl

theorem mixedFlux_hasDerivWithinAt
    {left right : ℝ → ComplexVorticityHilbertState} {leftRate rightRate : ComplexVorticityHilbertState}
    {domain : Set ℝ} {time : ℝ}
    (leftDerivative : HasDerivWithinAt left leftRate domain time)
    (rightDerivative : HasDerivWithinAt right rightRate domain time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivWithinAt (fun actual => mixedFlux (left actual) (right actual) wave output input)
      (mixedFlux leftRate (right time) wave output input + mixedFlux (left time) rightRate wave output input)
      domain time := by
  have actual := ((mixedFluxCLM wave output input).hasFDerivAt.comp_hasDerivWithinAt time leftDerivative).clm_apply rightDerivative
  simpa only [mixedFluxCLM_apply, Function.comp_def] using actual

theorem mixedFlux_contDiff {left right : ℝ → ComplexVorticityHilbertState} {order : WithTop ℕ∞}
    (leftSmooth : ContDiff ℝ order left) (rightSmooth : ContDiff ℝ order right)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ContDiff ℝ order (fun actual => mixedFlux (left actual) (right actual) wave output input) :=
  ((mixedFluxCLM wave output input).contDiff.comp leftSmooth).clm_apply rightSmooth

def mixedTimeSum (left right : ℕ → ℝ → ComplexVorticityHilbertState)
    (order : ℕ) (time : ℝ) : NativeFluidStressFourierState :=
  fun wave output input => ∑ rank ∈ Finset.range (order + 1),
    (order.choose rank : ℂ) * mixedFlux (left rank time) (right (order - rank) time) wave output input

theorem mixedTimeSum_hasDerivWithinAt
    (left right : ℕ → ℝ → ComplexVorticityHilbertState) (order : ℕ)
    (domain : Set ℝ) (time : ℝ)
    (leftNext : ∀ rank ≤ order, HasDerivWithinAt (left rank) (left (rank + 1) time) domain time)
    (rightNext : ∀ rank ≤ order, HasDerivWithinAt (right rank) (right (rank + 1) time) domain time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivWithinAt (fun actual => mixedTimeSum left right order actual wave output input)
      (mixedTimeSum left right (order + 1) time wave output input) domain time := by
  have term (rank : ℕ) (inside : rank ∈ Finset.range (order + 1)) :=
    (mixedFlux_hasDerivWithinAt (leftNext rank (by simpa using inside))
      (rightNext (order - rank) (Nat.sub_le _ _)) wave output input).const_mul (order.choose rank : ℂ)
  have actual := HasDerivWithinAt.fun_sum term
  have coefficient :
      (∑ rank ∈ Finset.range (order + 1), (order.choose rank : ℂ) *
        (mixedFlux (left (rank + 1) time) (right (order - rank) time) wave output input +
          mixedFlux (left rank time) (right (order - rank + 1) time) wave output input)) =
        mixedTimeSum left right (order + 1) time wave output input := by
    unfold mixedTimeSum
    rw [show order + 1 + 1 = order + 2 by omega,
      Finset.sum_choose_succ_mul (fun i j => mixedFlux (left i time) (right j time) wave output input) order]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro rank inside
    have index : order - rank + 1 = order + 1 - rank := by
      have rankLe : rank ≤ order := by simpa using inside
      omega
    rw [index]
  rw [coefficient] at actual
  exact actual

theorem weighted_convolution_mixed_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (left right : ScalarL2) (leftNonnegative : ∀ wave, 0 ≤ left wave) (rightNonnegative : ∀ wave, 0 ≤ right wave)
    (leftPaid : Summable left) (rightPaid : Summable right) (wave : IntegerWavevector) :
    weighted order ceiling nonnegative (convolution left right) wave ≤ 2 ^ order *
      (convolution right (weighted order ceiling nonnegative left) wave +
        convolution left (weighted order ceiling nonnegative right) wave) := by
  let w := wordWeight order ceiling
  have secondSum := convolution_row_summable left (weighted order ceiling nonnegative right) leftPaid wave
  have firstSum : Summable fun first => w first * left first * right (wave - first) := by
    have transformed := (Equiv.subLeft wave).summable_iff.mpr
      (convolution_row_summable right (weighted order ceiling nonnegative left) rightPaid wave)
    simpa [Function.comp_def, weighted_apply, w, mul_comm, mul_left_comm, mul_assoc] using transformed
  have swapped : (∑' first, w first * left first * right (wave - first)) =
      convolution right (weighted order ceiling nonnegative left) wave := by
    rw [convolution_apply _ _ rightPaid]
    convert! (Equiv.subLeft wave).tsum_eq
      (fun first => right first * (weighted order ceiling nonnegative left) (wave - first)) using 1
    simp [weighted_apply, w, mul_comm, mul_assoc]
  rw [weighted_apply, convolution_apply _ _ leftPaid, ← tsum_mul_left]
  calc
    _ ≤ ∑' first, 2 ^ order *
        ((w first * left first * right (wave - first)) +
          left first * (weighted order ceiling nonnegative right) (wave - first)) := by
      apply ((convolution_row_summable left right leftPaid wave).mul_left (w wave)).tsum_le_tsum _
        ((firstSum.add secondSum).mul_left (2 ^ order))
      intro first
      have split := wordWeight_add_le order ceiling nonnegative first (wave - first)
      rw [add_sub_cancel] at split
      have scaled := mul_le_mul_of_nonneg_right split (mul_nonneg (leftNonnegative first) (rightNonnegative (wave - first)))
      convert! scaled using 1
      simp only [weighted_apply, w]
      ring
    _ = _ := by
      rw [tsum_mul_left, firstSum.tsum_add secondSum, swapped, ← convolution_apply _ _ leftPaid]

theorem weighted_convolution_mixed_norm_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (left right : ScalarL2) (leftNonnegative : ∀ wave, 0 ≤ left wave) (rightNonnegative : ∀ wave, 0 ≤ right wave)
    (leftPaid : Summable left) (rightPaid : Summable right) :
    ‖weighted order ceiling nonnegative (convolution left right)‖ ≤ 2 ^ order *
      ((∑' wave, right wave) * ‖weighted order ceiling nonnegative left‖ +
        (∑' wave, left wave) * ‖weighted order ceiling nonnegative right‖) := by
  have convolutionNonnegative (f g : ScalarL2) (fp : ∀ wave, 0 ≤ f wave) (gp : ∀ wave, 0 ≤ g wave)
      (paid : Summable f) (wave) : 0 ≤ convolution f g wave := by
    rw [convolution_apply _ _ paid]
    exact tsum_nonneg fun first => mul_nonneg (fp _) (gp _)
  have weightedNonnegative (f : ScalarL2) (positive : ∀ wave, 0 ≤ f wave) (wave) :
      0 ≤ weighted order ceiling nonnegative f wave :=
    mul_nonneg (wordWeight_nonneg _ _ nonnegative _) (positive _)
  let first := convolution right (weighted order ceiling nonnegative left)
  let second := convolution left (weighted order ceiling nonnegative right)
  have pointwise : ‖weighted order ceiling nonnegative (convolution left right)‖ ≤ ‖(2 ^ order : ℝ) • (first + second)‖ := by
    apply lp.norm_mono (by norm_num)
    intro wave
    change |wordWeight order ceiling wave * convolution left right wave| ≤ |2 ^ order * (first wave + second wave)|
    rw [abs_of_nonneg (mul_nonneg (wordWeight_nonneg _ _ nonnegative _)
      (convolutionNonnegative left right leftNonnegative rightNonnegative leftPaid wave))]
    rw [abs_of_nonneg (mul_nonneg (by positivity)
      (add_nonneg (convolutionNonnegative _ _ rightNonnegative (weightedNonnegative left leftNonnegative) rightPaid wave)
        (convolutionNonnegative _ _ leftNonnegative (weightedNonnegative right rightNonnegative) leftPaid wave)))]
    exact weighted_convolution_mixed_le order ceiling nonnegative left right leftNonnegative rightNonnegative leftPaid rightPaid wave
  apply pointwise.trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_add_le first second).trans
  have l := convolution_norm_le right (weighted order ceiling nonnegative left) rightPaid
  have r := convolution_norm_le left (weighted order ceiling nonnegative right) leftPaid
  simp only [Real.norm_eq_abs, abs_of_nonneg (rightNonnegative _)] at l
  simp only [Real.norm_eq_abs, abs_of_nonneg (leftNonnegative _)] at r
  exact add_le_add l r

theorem mixedFlux_norm_le_convolution (left right : ComplexVorticityHilbertState)
    (leftPaid : Summable (amplitude left)) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖mixedFlux left right wave output input‖ ≤ convolution (amplitude left) (amplitude right) wave := by
  rw [mixedFlux, norm_neg, convolution_apply _ _ leftPaid]
  apply (norm_tsum_le_tsum_norm (mixed_pair_summable left right wave output input).norm).trans
  apply (mixed_pair_summable left right wave output input).norm.tsum_le_tsum _
    (convolution_row_summable _ _ leftPaid wave)
  intro first
  rw [norm_mul]
  exact mul_le_mul (coordinate_bound left first input) (coordinate_bound right (wave - first) output)
    (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)

def weightedMixedFlux (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (left right : ComplexVorticityHilbertState) (leftPaid : Summable (amplitude left))
    (output input : Coordinate) : lp (fun _ : IntegerWavevector => ℂ) 2 :=
  ⟨fun wave => wordWeight order ceiling wave • mixedFlux left right wave output input,
    (lp.memℓp (weighted order ceiling nonnegative (convolution (amplitude left) (amplitude right)))).mono fun wave => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wordWeight_nonneg _ _ nonnegative _)]
      exact mul_le_mul_of_nonneg_left (mixedFlux_norm_le_convolution left right leftPaid wave output input)
        (wordWeight_nonneg _ _ nonnegative _)⟩

theorem weightedMixedFlux_norm_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (left right : ComplexVorticityHilbertState) (leftPaid : Summable (amplitude left)) (rightPaid : Summable (amplitude right))
    (output input : Coordinate) :
    ‖weightedMixedFlux order ceiling nonnegative left right leftPaid output input‖ ≤ 2 ^ order *
      ((∑' wave, amplitude right wave) * ‖weighted order ceiling nonnegative (amplitude left)‖ +
        (∑' wave, amplitude left wave) * ‖weighted order ceiling nonnegative (amplitude right)‖) := by
  apply le_trans _ (weighted_convolution_mixed_norm_le order ceiling nonnegative (amplitude left) (amplitude right)
    (vorticityRowAmplitude_nonneg left) (vorticityRowAmplitude_nonneg right) leftPaid rightPaid)
  apply lp.norm_mono (by norm_num)
  intro wave
  change ‖wordWeight order ceiling wave • mixedFlux left right wave output input‖ ≤
    ‖wordWeight order ceiling wave * convolution (amplitude left) (amplitude right) wave‖
  rw [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (wordWeight_nonneg _ _ nonnegative _)]
  exact mul_le_mul_of_nonneg_left
    ((mixedFlux_norm_le_convolution left right leftPaid wave output input).trans (Real.le_norm_self _))
    (wordWeight_nonneg _ _ nonnegative _)

def mixedMomentDensity (order : ℕ) (left right : ComplexVorticityHilbertState)
    (output input : Coordinate) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * Complex.normSq (mixedFlux left right wave output input)

def mixedMomentBudget (order : ℕ) (left right : ComplexVorticityHilbertState) : ℝ :=
  2 * (2 ^ order) ^ 2 *
    ((∑' wave, amplitude right wave) ^ 2 * (∑' wave, velocityMomentDensity order left wave) +
      (∑' wave, amplitude left wave) ^ 2 * (∑' wave, velocityMomentDensity order right wave))

theorem weightedMixedFlux_square_bound (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (left right : ComplexVorticityHilbertState) (leftPaid : Summable (amplitude left)) (rightPaid : Summable (amplitude right))
    (leftMoment : Summable (velocityMomentDensity order left)) (rightMoment : Summable (velocityMomentDensity order right))
    (output input : Coordinate) :
    ‖weightedMixedFlux order ceiling nonnegative left right leftPaid output input‖ ^ 2 ≤ mixedMomentBudget order left right := by
  let a := (∑' wave, amplitude right wave) * ‖weighted order ceiling nonnegative (amplitude left)‖
  let b := (∑' wave, amplitude left wave) * ‖weighted order ceiling nonnegative (amplitude right)‖
  have first : a ^ 2 ≤ (∑' wave, amplitude right wave) ^ 2 * (∑' wave, velocityMomentDensity order left wave) := by
    dsimp [a]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (capped_amplitude_norm_sq_le order ceiling nonnegative left leftMoment) (sq_nonneg _)
  have second : b ^ 2 ≤ (∑' wave, amplitude left wave) ^ 2 * (∑' wave, velocityMomentDensity order right wave) := by
    dsimp [b]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (capped_amplitude_norm_sq_le order ceiling nonnegative right rightMoment) (sq_nonneg _)
  have quadratic : (a + b) ^ 2 ≤ 2 *
      ((∑' wave, amplitude right wave) ^ 2 * (∑' wave, velocityMomentDensity order left wave) +
        (∑' wave, amplitude left wave) ^ 2 * (∑' wave, velocityMomentDensity order right wave)) := by
    nlinarith [sq_nonneg (a - b)]
  have paid := pow_le_pow_left₀ (norm_nonneg _)
    (weightedMixedFlux_norm_le order ceiling nonnegative left right leftPaid rightPaid output input) 2
  rw [mul_pow] at paid
  apply paid.trans
  have scaled := mul_le_mul_of_nonneg_left quadratic (sq_nonneg ((2 : ℝ) ^ order))
  convert! scaled using 1
  unfold mixedMomentBudget
  ring

theorem mixed_moment_control (order : ℕ) (left right : ComplexVorticityHilbertState)
    (leftPaid : Summable (amplitude left)) (rightPaid : Summable (amplitude right))
    (leftMoment : Summable (velocityMomentDensity order left)) (rightMoment : Summable (velocityMomentDensity order right))
    (output input : Coordinate) :
    Summable (mixedMomentDensity order left right output input) ∧
      (∑' wave, mixedMomentDensity order left right output input wave) ≤ mixedMomentBudget order left right := by
  have nonnegative wave : 0 ≤ mixedMomentDensity order left right output input wave :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have finite (observed : Finset IntegerWavevector) :
      (∑ wave ∈ observed, mixedMomentDensity order left right output input wave) ≤ mixedMomentBudget order left right := by
    let ceiling := frequencyCeiling observed
    have positive := frequencyCeiling_nonneg observed
    have bound := weightedMixedFlux_square_bound order ceiling positive left right leftPaid rightPaid leftMoment rightMoment output input
    have observedBound := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
      (weightedMixedFlux order ceiling positive left right leftPaid output input) observed
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at observedBound
    apply le_trans _ bound
    convert! observedBound using 1
    apply Finset.sum_congr rfl
    intro wave inside
    simp only [mixedMomentDensity, weightedMixedFlux, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, Complex.normSq_eq_norm_sq]
    rw [wordWeight_full_on_modes observed order wave inside]
  exact ⟨summable_of_sum_le nonnegative finite, Real.tsum_le_of_sum_le nonnegative finite⟩

end
end SaturationMonoid.NavierStokes.NativeHigherTimeJets

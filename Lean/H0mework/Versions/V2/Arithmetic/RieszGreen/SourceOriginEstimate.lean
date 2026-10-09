import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Consumer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter FourierTransform MeasureTheory Set
open scoped FourierTransform Topology
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def originExponent (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  (coordinate.value.re + 1 / 2) / 2

theorem originExponent_bounds (coordinate : BurnolCompletedMellinCoordinate) :
    1 / 2 < originExponent coordinate ∧ originExponent coordinate < coordinate.value.re ∧
      originExponent coordinate < 1 := by
  dsimp [originExponent]
  constructor
  · linarith [coordinate.rightHalf]
  constructor <;> linarith [coordinate.rightHalf, coordinate.belowOne]

theorem phase_holder (power : ℝ) (nonnegative : 0 ≤ power) (below : power ≤ 1) (t : ℝ) :
    ‖(𝐞 t : ℂ) - 1‖ ≤ (2 + 2 * Real.pi) * |t| ^ power := by
  have linear : ‖(𝐞 t : ℂ) - 1‖ ≤ (2 * Real.pi) * |t| := by
    simpa only [Real.fourierChar_apply, mul_comm Complex.I,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t))
  have bounded : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 := by
    simpa only [Circle.norm_coe, norm_one, one_add_one_eq_two] using norm_sub_le (𝐞 t : ℂ) (1 : ℂ)
  have nonnegativePower := Real.rpow_nonneg (abs_nonneg t) power
  by_cases small : |t| ≤ 1
  · exact linear.trans ((mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one (abs_nonneg t) small below) (by positivity)).trans
        (by nlinarith [Real.pi_pos]))
  · have oneLe : 1 ≤ |t| ^ power := Real.one_le_rpow (le_of_not_ge small) nonnegative
    exact bounded.trans (by nlinarith [Real.pi_pos])

theorem tail_origin_moment_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (fun x : ℝ => |x| ^ originExponent coordinate *
      ‖burnolRadiusMellinTailKernelRaw q (coordinate.value + 1) x‖) := by
  let power := originExponent coordinate - coordinate.value.re - 1
  have exponent : power < -1 := by
    dsimp [power]
    linarith [(originExponent_bounds coordinate).2.1]
  have majorant := ((integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < q)).mpr exponent).integrable_indicator measurableSet_Ioi
  apply majorant.congr
  filter_upwards with x
  by_cases inside : x ∈ Ioi q
  · have positive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) inside
    rw [indicator_of_mem inside]
    simp only [burnolRadiusMellinTailKernelRaw, if_pos inside,
      Complex.norm_cpow_eq_rpow_re_of_pos positive, neg_re, Complex.star_def,
      Complex.conj_re, Complex.add_re, Complex.one_re, abs_of_pos positive]
    rw [← Real.rpow_add positive]
    congr 1
    dsimp [power]
    ring
  · rw [indicator_of_notMem inside]
    simp only [burnolRadiusMellinTailKernelRaw, if_neg inside, norm_zero, mul_zero]

theorem fourier_tail_origin_zero (coordinate : BurnolCompletedMellinCoordinate) :
    burnolMellinTailDerivativeFourierRaw q coordinate 0 =
      (q : ℂ) ^ (-star coordinate.value) / star coordinate.value := by
  have exponent : (-star (coordinate.value + 1)).re < -1 := by
    simp only [neg_re, Complex.star_def, Complex.conj_re, Complex.add_re, Complex.one_re]
    linarith [coordinate.rightHalf]
  have total : (∫ x : ℝ, burnolRadiusMellinTailKernelRaw q (coordinate.value + 1) x) =
      ∫ x : ℝ in Ioi q, (x : ℂ) ^ (-star (coordinate.value + 1)) := by
    change (∫ x : ℝ, (Ioi q).indicator (fun x : ℝ => (x : ℂ) ^ (-star (coordinate.value + 1))) x) = _
    exact integral_indicator measurableSet_Ioi
  simp only [burnolMellinTailDerivativeFourierRaw, VectorFourier.fourierIntegral,
    innerₗ_apply_apply, Real.inner_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    one_smul]
  rw [total, integral_Ioi_cpow_of_lt exponent (by norm_num)]
  have power : -star (coordinate.value + 1) + 1 = -star coordinate.value := by
    simp only [star_add, star_one]
    ring
  rw [power]
  ring

theorem numerator_origin_zero (coordinate : BurnolCompletedMellinCoordinate) :
    burnolGapTailFourierNumerator q coordinate 0 = 0 := by
  have nonzero : star coordinate.value ≠ 0 := by
    apply star_ne_zero.mpr
    intro zero
    have positive := coordinate.rightHalf
    rw [zero] at positive
    norm_num at positive
  simp only [burnolGapTailFourierNumerator, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one, fourier_tail_origin_zero]
  field_simp
  ring

def tailOriginMoment (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ∫ x : ℝ, |x| ^ originExponent coordinate *
    ‖burnolRadiusMellinTailKernelRaw q (coordinate.value + 1) x‖

theorem tailOriginMoment_nonneg (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ tailOriginMoment coordinate :=
  integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (norm_nonneg _)

theorem tail_fourier_read (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    burnolMellinTailDerivativeFourierRaw q coordinate frequency =
      ∫ x : ℝ, (𝐞 (-(frequency * x)) : ℂ) *
        burnolRadiusMellinTailKernelRaw q (coordinate.value + 1) x := by
  unfold burnolMellinTailDerivativeFourierRaw VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  simp only [innerₗ_apply_apply, Real.inner_apply, Circle.smul_def, smul_eq_mul]
  rw [mul_comm x frequency]

theorem tail_fourier_holder (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    ‖burnolMellinTailDerivativeFourierRaw q coordinate frequency -
      burnolMellinTailDerivativeFourierRaw q coordinate 0‖ ≤
      ((2 + 2 * Real.pi) * tailOriginMoment coordinate) * |frequency| ^ originExponent coordinate := by
  let raw := burnolRadiusMellinTailKernelRaw q (coordinate.value + 1)
  have rawInt : Integrable raw := burnolMellinTailDerivativeRaw_integrable q (by norm_num) coordinate
  have phasedInt : Integrable (fun x : ℝ => (𝐞 (-(frequency * x)) : ℂ) * raw x) := by
    apply rawInt.norm.mono' (by fun_prop)
    filter_upwards with x
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact le_rfl
  have difference : burnolMellinTailDerivativeFourierRaw q coordinate frequency -
      burnolMellinTailDerivativeFourierRaw q coordinate 0 =
      ∫ x : ℝ, ((𝐞 (-(frequency * x)) : ℂ) - 1) * raw x := by
    rw [tail_fourier_read, tail_fourier_read]
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
    rw [← integral_sub phasedInt rawInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have bound (x : ℝ) : ‖((𝐞 (-(frequency * x)) : ℂ) - 1) * raw x‖ ≤
      ((2 + 2 * Real.pi) * |frequency| ^ originExponent coordinate) *
        (|x| ^ originExponent coordinate * ‖raw x‖) := by
    rw [norm_mul]
    have source := phase_holder (originExponent coordinate)
      (by linarith [(originExponent_bounds coordinate).1])
      (originExponent_bounds coordinate).2.2.le (-(frequency * x))
    rw [abs_neg, abs_mul, Real.mul_rpow (abs_nonneg frequency) (abs_nonneg x)] at source
    calc
      _ ≤ ((2 + 2 * Real.pi) * (|frequency| ^ originExponent coordinate *
          |x| ^ originExponent coordinate)) * ‖raw x‖ :=
        mul_le_mul_of_nonneg_right source (norm_nonneg _)
      _ = _ := by ring
  rw [difference]
  have estimate := norm_integral_le_of_norm_le
    ((tail_origin_moment_integrable coordinate).const_mul
      ((2 + 2 * Real.pi) * |frequency| ^ originExponent coordinate))
    (Filter.Eventually.of_forall bound)
  rw [integral_const_mul] at estimate
  exact estimate.trans_eq (by dsimp [tailOriginMoment, raw]; ring)

def numeratorOriginBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  let mean := star (burnolRadiusMellinGapMoment q coordinate.value) * (((2 * q : ℝ) : ℂ)⁻¹)
  (2 + 2 * Real.pi) *
    ((‖mean‖ + ‖(q : ℂ) ^ (-star coordinate.value) - mean‖) * q ^ originExponent coordinate +
      ‖star coordinate.value‖ * tailOriginMoment coordinate)

theorem numerator_origin_holder (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    ‖burnolGapTailFourierNumerator q coordinate frequency‖ ≤
      numeratorOriginBound coordinate * |frequency| ^ originExponent coordinate := by
  let mean := star (burnolRadiusMellinGapMoment q coordinate.value) * (((2 * q : ℝ) : ℂ)⁻¹)
  let outer := (q : ℂ) ^ (-star coordinate.value) - mean
  have split : burnolGapTailFourierNumerator q coordinate frequency =
      mean * ((𝐞 (q * frequency) : ℂ) - 1) +
      outer * ((𝐞 (-(q * frequency)) : ℂ) - 1) -
      star coordinate.value * (burnolMellinTailDerivativeFourierRaw q coordinate frequency -
        burnolMellinTailDerivativeFourierRaw q coordinate 0) := by
    have origin := numerator_origin_zero coordinate
    simp only [burnolGapTailFourierNumerator, mul_zero, neg_zero, AddChar.map_zero_eq_one,
      Circle.coe_one, mul_one] at origin
    change mean * (𝐞 (q * frequency) : ℂ) + outer * (𝐞 (-(q * frequency)) : ℂ) -
      star coordinate.value * burnolMellinTailDerivativeFourierRaw q coordinate frequency = _
    change mean + outer - star coordinate.value * burnolMellinTailDerivativeFourierRaw q coordinate 0 = 0 at origin
    linear_combination origin
  have positivePhase := phase_holder (originExponent coordinate)
    (by linarith [(originExponent_bounds coordinate).1])
    (originExponent_bounds coordinate).2.2.le (q * frequency)
  have negativePhase := phase_holder (originExponent coordinate)
    (by linarith [(originExponent_bounds coordinate).1])
    (originExponent_bounds coordinate).2.2.le (-(q * frequency))
  rw [abs_mul, abs_of_pos (by norm_num : 0 < q), Real.mul_rpow (by norm_num : 0 ≤ q)
    (abs_nonneg frequency)] at positivePhase
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : 0 < q), Real.mul_rpow (by norm_num : 0 ≤ q)
    (abs_nonneg frequency)] at negativePhase
  rw [split]
  calc
    _ ≤ ‖mean * ((𝐞 (q * frequency) : ℂ) - 1)‖ +
        ‖outer * ((𝐞 (-(q * frequency)) : ℂ) - 1)‖ +
        ‖star coordinate.value * (burnolMellinTailDerivativeFourierRaw q coordinate frequency -
          burnolMellinTailDerivativeFourierRaw q coordinate 0)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖mean‖ * ((2 + 2 * Real.pi) * (q ^ originExponent coordinate * |frequency| ^ originExponent coordinate)) +
        ‖outer‖ * ((2 + 2 * Real.pi) * (q ^ originExponent coordinate * |frequency| ^ originExponent coordinate)) +
        ‖star coordinate.value‖ * (((2 + 2 * Real.pi) * tailOriginMoment coordinate) *
          |frequency| ^ originExponent coordinate) := by
      simp only [norm_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left positivePhase (norm_nonneg _))
        (mul_le_mul_of_nonneg_left negativePhase (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (tail_fourier_holder coordinate frequency) (norm_nonneg _))
    _ = _ := by dsimp [numeratorOriginBound, mean, outer]; ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

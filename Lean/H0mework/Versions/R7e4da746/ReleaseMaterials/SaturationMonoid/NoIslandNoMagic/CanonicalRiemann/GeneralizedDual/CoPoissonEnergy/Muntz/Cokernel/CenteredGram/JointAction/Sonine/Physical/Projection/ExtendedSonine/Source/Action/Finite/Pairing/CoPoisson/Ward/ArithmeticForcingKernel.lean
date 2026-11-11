import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingForcing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticMomentGram
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticForcingKernel

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSource.Translator
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

def forcingCoefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  ForcingWhole.coefficient coordinate

def edgeCoefficient (j : ℕ) : ℂ :=
  (2 * q : ℂ) * (-1 : ℂ) ^ j * (2 * j : ℕ) * (2 * (Real.pi : ℂ) * q) ^ (2 * j) /
    ((2 * j + 1).factorial : ℂ)

def coefficient (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  forcingCoefficient coordinate * edgeCoefficient j / ((2 * j + 1 : ℕ) - star coordinate.value)

def arithmeticCoefficient (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  if j = 0 then 0 else coefficient coordinate j * riemannZeta (2 * j + 1 : ℕ)

private theorem phase_exp (x y : ℝ) :
    Constructor.phase x y = Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * (y : ℂ)) := by
  unfold Constructor.phase
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem phase_pair (x : ℝ) :
    Constructor.phase x q + Constructor.phase x (-q) =
      2 * Complex.cos (2 * (Real.pi : ℂ) * q * (x : ℂ)) := by
  rw [phase_exp, phase_exp, Complex.cos]
  have first : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * q =
      -(2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by ring
  have second : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * ((-q : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by push_cast; ring
  rw [first, second]
  ring

private theorem fourier_one (x : ℝ) :
    burnolRadiusTruncatedFourierRaw q (intervalConstant q) x =
      ∫ y : ℝ in (-q)..q, Constructor.phase x y := by
  have actual := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  rw [← Constructor.fourierRaw_state, congrFun actual x, Constructor.fourierRaw_integral]
  simp only [mul_one]

private theorem edge_trigonometric (x : ℝ) (nonzero : x ≠ 0) :
    Edge.raw q x = (2 * q : ℂ) *
      (Complex.cos (2 * (Real.pi : ℂ) * q * (x : ℂ)) -
        Complex.sin (2 * (Real.pi : ℂ) * q * (x : ℂ)) /
          (2 * (Real.pi : ℂ) * q * (x : ℂ))) := by
  have piNe : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have xNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  have slopeNe : -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) piNe) Complex.I_ne_zero) xNe
  rw [Edge.raw_apply, phase_pair, fourier_one,
    intervalIntegral.integral_congr (fun y _ => phase_exp x y), integral_exp_mul_complex slopeNe,
    Complex.sin]
  have first : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * q =
      -(2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by ring
  have second : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * ((-q : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * q * (x : ℂ)) * Complex.I := by push_cast; ring
  rw [first, second]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem edge_zero_coefficient : edgeCoefficient 0 = 0 := by norm_num [edgeCoefficient]

/-- The complete original edge, including its T1 subtraction, generates this even series. -/
theorem edge_expansion (x : ℝ) :
    HasSum (fun j : ℕ => edgeCoefficient j * (x : ℂ) ^ (2 * j)) (Edge.raw q x) := by
  by_cases zero : x = 0
  · subst x
    rw [ForcingTail.edge_zero]
    have terms : (fun j : ℕ => edgeCoefficient j * (0 : ℂ) ^ (2 * j)) = fun _ => 0 := by
      funext j
      by_cases initial : j = 0
      · simp [initial, edge_zero_coefficient]
      · rw [zero_pow (by omega : 2 * j ≠ 0), mul_zero]
    simpa only [Complex.ofReal_zero, terms] using (show HasSum (fun _ : ℕ => (0 : ℂ)) 0 from hasSum_zero)
  · let z : ℂ := 2 * (Real.pi : ℂ) * q * (x : ℂ)
    have zNe : z ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)) (Complex.ofReal_ne_zero.mpr zero)
    have source := ((Complex.hasSum_cos z).sub ((Complex.hasSum_sin z).div_const z)).mul_left (2 * q : ℂ)
    rw [edge_trigonometric x zero]
    convert! source using 1
    funext j
    have factorialNe : ((2 * j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * j)
    have nextNe : (2 * (j : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
    unfold edgeCoefficient
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp [zNe, factorialNe, nextNe]
    rw [show z ^ (2 * j) = (2 * (Real.pi : ℂ) * q) ^ (2 * j) * (x : ℂ) ^ (2 * j) from mul_pow _ _ _]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring

theorem coefficient_zero (coordinate : BurnolCompletedMellinCoordinate) : coefficient coordinate 0 = 0 := by
  rw [coefficient, edge_zero_coefficient, mul_zero, zero_div]

theorem coefficient_one (coordinate : BurnolCompletedMellinCoordinate) :
    coefficient coordinate 1 = -(Real.pi : ℂ) ^ 2 * forcingCoefficient coordinate /
      (24 * (3 - star coordinate.value)) := by
  rw [div_mul_eq_div_div]
  norm_num [coefficient, edgeCoefficient]
  ring

theorem coefficient_two (coordinate : BurnolCompletedMellinCoordinate) :
    coefficient coordinate 2 = (Real.pi : ℂ) ^ 4 * forcingCoefficient coordinate /
      (960 * (5 - star coordinate.value)) := by
  rw [div_mul_eq_div_div]
  norm_num [coefficient, edgeCoefficient]
  ring

theorem edge_bound (j : ℕ) (x : ℝ) (inside : |x| ≤ q) :
    ‖edgeCoefficient j * (x : ℂ) ^ (2 * j)‖ ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ j := by
  have factorialPositive : (0 : ℝ) < (2 * j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have ratio : ((2 * j : ℕ) : ℝ) / (2 * j + 1).factorial ≤ 1 := by
    apply (div_le_one factorialPositive).mpr
    exact_mod_cast (Nat.le_succ (2 * j)).trans (Nat.self_le_factorial (2 * j + 1))
  have phasePositive : 0 ≤ 2 * Real.pi * q := by positivity
  have phaseBound : (2 * Real.pi * q) * |x| ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * 4 * q) * q := by gcongr; exact Real.pi_le_four
      _ = _ := by norm_num
  have phaseNorm : ‖(2 : ℂ) * (Real.pi : ℂ) * q‖ = 2 * Real.pi * q := by
    rw [norm_mul, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  have read : ‖edgeCoefficient j * (x : ℂ) ^ (2 * j)‖ =
      (1 / 2 : ℝ) * (((2 * j : ℕ) : ℝ) / (2 * j + 1).factorial) *
        ((2 * Real.pi * q) * |x|) ^ (2 * j) := by
    unfold edgeCoefficient
    simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, phaseNorm]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, norm_div, norm_ofNat, norm_one]
    rw [mul_pow]
    have scalar : (1 / 4 : ℝ) ^ (2 * j) * (2 : ℝ) ^ (2 * j) = (1 / 2 : ℝ) ^ (2 * j) := by
      rw [← mul_pow]
      norm_num
    linear_combination (((2 * j : ℕ) : ℝ) / (2 * j + 1).factorial * Real.pi ^ (2 * j) * |x| ^ (2 * j) / 2) * scalar
  rw [read]
  calc
    _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (2 * j) := by
      calc
        _ ≤ (1 / 2 : ℝ) * 1 * ((2 * Real.pi * q) * |x|) ^ (2 * j) := by gcongr
        _ ≤ _ := by rw [mul_one]; gcongr
    _ = _ := by rw [pow_mul]; norm_num

theorem coefficient_bound (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) (x : ℝ)
    (inside : |x| ≤ q) :
    ‖coefficient coordinate j * (x : ℂ) ^ (2 * j)‖ ≤
      (‖forcingCoefficient coordinate‖ / 2) * (1 / 4 : ℝ) ^ j := by
  by_cases initial : j = 0
  · subst j
    rw [coefficient_zero, zero_mul, norm_zero]
    positivity
  have denominator : 1 ≤ ‖((2 * j + 1 : ℕ) : ℂ) - star coordinate.value‖ := by
    calc
      1 ≤ (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value).re := by
        simp only [sub_re, natCast_re, star_def, conj_re]
        have degree : (2 : ℝ) ≤ 2 * j := by exact_mod_cast (by omega : 2 ≤ 2 * j)
        push_cast
        linarith [coordinate.belowOne]
      _ ≤ _ := Complex.re_le_norm _
  have original := edge_bound j x inside
  rw [coefficient, div_mul_eq_mul_div, mul_assoc, norm_div, norm_mul]
  calc
    _ ≤ ‖forcingCoefficient coordinate‖ * ‖edgeCoefficient j * (x : ℂ) ^ (2 * j)‖ := by
      exact div_le_self (by positivity) denominator
    _ ≤ _ := by nlinarith [norm_nonneg (forcingCoefficient coordinate)]

private theorem weighted_term (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ)
    (x : ℝ) (positive : 0 < x) :
    (x : ℂ) ^ (-star coordinate.value) * (edgeCoefficient j * (x : ℂ) ^ (2 * j)) =
      edgeCoefficient j * (x : ℂ) ^ (((2 * j : ℕ) : ℂ) - star coordinate.value) := by
  rw [← Complex.cpow_natCast, mul_left_comm,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
  congr 2
  ring

private theorem weighted_integral (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ)
    (x : ℝ) (positive : 0 < x) :
    (∫ t : ℝ in Ioc 0 x,
      edgeCoefficient j * (t : ℂ) ^ (((2 * j : ℕ) : ℂ) - star coordinate.value)) =
        edgeCoefficient j * (x : ℂ) ^ (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) /
          (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) := by
  have exponent : -1 < (((2 * j : ℕ) : ℂ) - star coordinate.value).re := by
    simp only [sub_re, natCast_re, star_def, conj_re]
    have nonnegative : (0 : ℝ) ≤ 2 * j := by positivity
    push_cast
    linarith [coordinate.belowOne]
  have exponentNe : (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) ≠ 0 := by
    intro zero
    have real := congrArg Complex.re zero
    simp only [sub_re, natCast_re, star_def, conj_re, zero_re] at real
    have nonnegative : (0 : ℝ) ≤ 2 * j := by positivity
    push_cast at real
    linarith [coordinate.belowOne]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le positive.le,
    integral_cpow (Or.inl exponent), show (((2 * j : ℕ) : ℂ) - star coordinate.value) + 1 =
      (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) by push_cast; ring,
    Complex.ofReal_zero, Complex.zero_cpow exponentNe, sub_zero]
  ring

private theorem primitive_expansion (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (small : x ≤ q) :
    HasSum (fun j : ℕ =>
      edgeCoefficient j * (x : ℂ) ^ (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) /
        (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value)) (ForcingPrimitive.edgePrimitive coordinate x) := by
  let term := fun j : ℕ => fun t : ℝ =>
    edgeCoefficient j * (t : ℂ) ^ (((2 * j : ℕ) : ℂ) - star coordinate.value)
  let majorant := fun j : ℕ => fun t : ℝ =>
    ((1 / 2 : ℝ) * (1 / 4 : ℝ) ^ j) * t ^ (-coordinate.value.re)
  have power : IntegrableOn (fun t : ℝ => t ^ (-coordinate.value.re)) (Ioc 0 x) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := x)
      (by linarith [coordinate.belowOne] : -1 < -coordinate.value.re)).1
  have majorantSum : Summable (fun j : ℕ => (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left _
  have result := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioc 0 x))
    majorant
    (F := term)
    (f := fun t : ℝ => (t : ℂ) ^ (-star coordinate.value) * Edge.raw q t)
    (fun j => by
      have measurable : Measurable (term j) := by unfold term; fun_prop
      exact measurable.aestronglyMeasurable)
    (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
      rw [show term j t = (t : ℂ) ^ (-star coordinate.value) *
        (edgeCoefficient j * (t : ℂ) ^ (2 * j)) from (weighted_term coordinate j t inside.1).symm,
        norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos inside.1]
      simp only [neg_re, star_def, conj_re]
      exact (mul_le_mul_of_nonneg_left (edge_bound j t (by
        rw [abs_of_pos inside.1]; exact inside.2.trans small)) (Real.rpow_nonneg inside.1.le _)).trans_eq
          (by unfold majorant; ring))
    (by filter_upwards with t; exact majorantSum.mul_right _)
    (by
      simp only [majorant, tsum_mul_right]
      exact power.const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
      have actual := (edge_expansion t).mul_left ((t : ℂ) ^ (-star coordinate.value))
      exact actual.congr_fun (fun j => (weighted_term coordinate j t inside.1).symm))
  rw [ForcingPrimitive.edgePrimitive, intervalIntegral.integral_of_le positive.le]
  simpa only [term, weighted_integral coordinate _ x positive] using result

private theorem forcing_positive_expansion (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (small : x ≤ q) :
    HasSum (fun j : ℕ => coefficient coordinate j * (x : ℂ) ^ (2 * j))
      (ForcingTail.forcingRemainder coordinate x) := by
  have original := (primitive_expansion coordinate x positive small).mul_left
    (forcingCoefficient coordinate * (x : ℂ) ^ (star coordinate.value - 1))
  have target : forcingCoefficient coordinate * (x : ℂ) ^ (star coordinate.value - 1) *
      ForcingPrimitive.edgePrimitive coordinate x = ForcingTail.forcingRemainder coordinate x := by
    rw [ForcingTail.forcingRemainder, ForcingTail.edgeRemainder, abs_of_pos positive]
    unfold forcingCoefficient
    ring
  rw [target] at original
  apply original.congr_fun
  intro j
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have powers : (x : ℂ) ^ (star coordinate.value - 1) *
      (x : ℂ) ^ (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) = (x : ℂ) ^ (2 * j) := by
    rw [← Complex.cpow_add _ _ nonzero,
      show (star coordinate.value - 1) + (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) =
        ((2 * j : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
  unfold coefficient
  symm
  calc
    _ = forcingCoefficient coordinate * edgeCoefficient j *
        ((x : ℂ) ^ (star coordinate.value - 1) *
          (x : ℂ) ^ (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value)) /
            (((2 * j + 1 : ℕ) : ℂ) - star coordinate.value) := by ring
    _ = _ := by rw [powers]; ring

/-- The original Mellin primitive is integrated term by term using a source-owned geometric majorant. -/
theorem forcing_expansion (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (inside : |x| ≤ q) :
    HasSum (fun j : ℕ => coefficient coordinate j * (x : ℂ) ^ (2 * j))
      (ForcingTail.forcingRemainder coordinate x) := by
  by_cases zero : x = 0
  · subst x
    have terms : (fun j : ℕ => coefficient coordinate j * (0 : ℂ) ^ (2 * j)) = fun _ => 0 := by
      funext j
      by_cases initial : j = 0
      · simp [initial, coefficient_zero]
      · rw [zero_pow (by omega : 2 * j ≠ 0), mul_zero]
    simp only [Complex.ofReal_zero, terms, ForcingTail.forcingRemainder, ForcingTail.edgeRemainder,
      abs_zero, ForcingPrimitive.edgePrimitive, intervalIntegral.integral_same, mul_zero]
    exact hasSum_zero
  · have positive := forcing_positive_expansion coordinate |x| (abs_pos.mpr zero) inside
    have target : ForcingTail.forcingRemainder coordinate |x| = ForcingTail.forcingRemainder coordinate x := by
      simp only [ForcingTail.forcingRemainder, ForcingTail.edgeRemainder, abs_abs]
    rw [target] at positive
    apply positive.congr_fun
    intro j
    congr 1
    rcases le_total 0 x with xpos | xneg
    · rw [abs_of_nonneg xpos]
    · rw [abs_of_nonpos xneg, Complex.ofReal_neg]
      simp only [pow_mul, neg_sq]

private theorem constant_norm_bound : ‖intervalConstant q‖ ≤ (1 : ℝ) := by
  have square : ‖intervalConstant q‖ ^ 2 = 2 * q := by
    exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
  norm_num at square
  nlinarith [norm_nonneg (intervalConstant q)]

theorem forcing_term_bound (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) :
    ‖coefficient coordinate j • ArithmeticMomentGram.powerL2 j‖ ≤
      (‖forcingCoefficient coordinate‖ / 2) * (1 / 4 : ℝ) ^ j := by
  have compared : ‖coefficient coordinate j • ArithmeticMomentGram.powerL2 j‖ ≤
      ((‖forcingCoefficient coordinate‖ / 2) * (1 / 4 : ℝ) ^ j) * ‖intervalConstant q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_smul (coefficient coordinate j) (ArithmeticMomentGram.powerL2 j),
      ArithmeticMomentGram.power_coeFn j, intervalConstant_coeFn q,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x scaled actual constant inside
    rw [scaled, constant]
    simp only [Pi.smul_apply, smul_eq_mul, actual, ArithmeticMomentGram.powerRaw, norm_one, mul_one]
    exact coefficient_bound coordinate j x (abs_le.mpr inside)
  exact compared.trans (mul_le_of_le_one_right (by positivity) constant_norm_bound)

theorem forcing_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun j : ℕ => ‖coefficient coordinate j • ArithmeticMomentGram.powerL2 j‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (forcing_term_bound coordinate)
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left _

/-- The scalar primitive and the strong L² series represent the same original forcing. -/
theorem forcing_strong_expansion (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => coefficient coordinate j • ArithmeticMomentGram.powerL2 j)
      (ForcingTail.forcingRemainderState coordinate) := by
  have normSum := forcing_norm_summable coordinate
  have pointwise := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr normSum)
  have terms : ∀ᵐ x : ℝ ∂μq, ∀ j : ℕ,
      (coefficient coordinate j • ArithmeticMomentGram.powerL2 j : Hq) x =
        coefficient coordinate j * (x : ℂ) ^ (2 * j) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (coefficient coordinate j) (ArithmeticMomentGram.powerL2 j),
      ArithmeticMomentGram.power_coeFn j] with x scaled actual
    rw [scaled]
    simp only [Pi.smul_apply, smul_eq_mul, actual, ArithmeticMomentGram.powerRaw]
  have same : (∑' j : ℕ, coefficient coordinate j • ArithmeticMomentGram.powerL2 j) =
      ForcingTail.forcingRemainderState coordinate := by
    apply Lp.ext
    filter_upwards [pointwise, terms, ForcingTail.forcingRemainderState_ae_raw coordinate,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x summed actual source inside
    rw [source]
    exact (summed.congr_fun (fun j => (actual j).symm)).unique
      (forcing_expansion coordinate x (abs_le.mpr inside))
  exact same ▸ normSum.of_norm.hasSum

private def countingCLM (scale : ℝ) : Hq →L[ℂ] Hq :=
  (Real.sqrt scale : ℂ)⁻¹ • burnolQuarterRestriction.comp
    ((burnolMultiplicativeDilation (-Real.log scale)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      burnolQuarterZeroExtension)

private theorem countingCLM_apply (scale : ℝ) (state : Hq) :
    countingCLM scale state = InverseAction.countingWindow scale state := rfl

theorem counting_power (n j : ℕ) :
    InverseAction.countingWindow n (ArithmeticMomentGram.powerL2 j) =
      ((n : ℂ)⁻¹) ^ (2 * j + 1) • ArithmeticMomentGram.powerL2 j := by
  by_cases initial : n = 0
  · subst n
    simp [InverseAction.countingWindow]
  have positive : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero initial
  have large : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr initial
  apply Lp.ext
  filter_upwards [InverseAction.countingWindow_raw n positive _ _ (ArithmeticMomentGram.power_coeFn j),
    Lp.coeFn_smul (((n : ℂ)⁻¹) ^ (2 * j + 1)) (ArithmeticMomentGram.powerL2 j),
    ArithmeticMomentGram.power_coeFn j, ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x actual scaled power inside
  have divided : x / n ∈ symmetricInterval q := by
    apply abs_le.mp
    rw [abs_div, abs_of_pos positive]
    exact (div_le_self (abs_nonneg x) large).trans (abs_le.mpr inside)
  rw [actual, scaled]
  change (n : ℂ)⁻¹ * (symmetricInterval q).indicator (ArithmeticMomentGram.powerRaw j) (x / n) = _
  rw [indicator_of_mem divided]
  simp only [Pi.smul_apply, smul_eq_mul, power]
  unfold ArithmeticMomentGram.powerRaw
  rw [Complex.ofReal_div, Complex.ofReal_natCast, div_pow, pow_succ]
  simp only [div_eq_mul_inv, inv_pow]
  ring

private def integerTerm (coordinate : BurnolCompletedMellinCoordinate) (n j : ℕ) : Hq :=
  ((n : ℂ)⁻¹) ^ (2 * j + 1) • (coefficient coordinate j • ArithmeticMomentGram.powerL2 j)

private theorem integer_term_bound (coordinate : BurnolCompletedMellinCoordinate) (n j : ℕ) :
    ‖integerTerm coordinate n j‖ ≤ ((n : ℝ)⁻¹) ^ 3 *
      ((‖forcingCoefficient coordinate‖ / 2) * (1 / 4 : ℝ) ^ j) := by
  by_cases initial : j = 0
  · subst j
    simp only [integerTerm, coefficient_zero, zero_smul, smul_zero, norm_zero]
    positivity
  by_cases zero : n = 0
  · subst n
    simp [integerTerm]
  have large : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero
  have scalar : ((n : ℝ)⁻¹) ^ (2 * j + 1) ≤ ((n : ℝ)⁻¹) ^ 3 :=
    pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ large) (by omega)
  rw [integerTerm, norm_smul, norm_pow, norm_inv, Complex.norm_natCast]
  exact mul_le_mul scalar (forcing_term_bound coordinate j) (norm_nonneg _) (by positivity)

set_option maxHeartbeats 800000 in
private theorem double_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun pair : ℕ × ℕ => ‖integerTerm coordinate pair.1 pair.2‖) := by
  have integers : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by decide : 1 < 3))
  have powers : Summable (fun j : ℕ => (‖forcingCoefficient coordinate‖ / 2) * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left _
  have majorant := integers.mul_of_nonneg powers (fun _ => by positivity) (fun _ => by positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun pair => integer_term_bound coordinate pair.1 pair.2) majorant

private theorem counted_forcing_expansion (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) :
    HasSum (fun j : ℕ => integerTerm coordinate n j)
      (InverseAction.countingWindow n (ForcingTail.forcingRemainderState coordinate)) := by
  have actual := (forcing_strong_expansion coordinate).mapL (countingCLM n)
  rw [countingCLM_apply] at actual
  apply actual.congr_fun
  intro j
  rw [map_smul, countingCLM_apply, counting_power]
  unfold integerTerm
  module

private theorem integer_column_sum (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) :
    HasSum (fun n : ℕ => integerTerm coordinate n j)
      (arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j) := by
  by_cases initial : j = 0
  · subst j
    simp only [integerTerm, coefficient_zero, zero_smul, smul_zero, arithmeticCoefficient, if_true]
    exact hasSum_zero
  have degree : 1 < 2 * j + 1 := by omega
  have norms : Summable (fun n : ℕ => ‖((n : ℂ)⁻¹) ^ (2 * j + 1)‖) := by
    simpa only [norm_pow, norm_inv, Complex.norm_natCast, inv_pow] using
      (Real.summable_nat_pow_inv.mpr degree)
  have zeta : (∑' n : ℕ, ((n : ℂ)⁻¹) ^ (2 * j + 1)) = riemannZeta (2 * j + 1 : ℕ) := by
    rw [zeta_nat_eq_tsum_of_gt_one degree]
    simp only [one_div, inv_pow]
  have actual := norms.of_norm.hasSum.smul_const (coefficient coordinate j • ArithmeticMomentGram.powerL2 j)
  rw [zeta] at actual
  convert! actual using 1
  simp only [arithmeticCoefficient, if_neg initial]
  module

theorem arithmetic_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun j : ℕ => ‖arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j‖) := by
  have double := double_norm_summable coordinate
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ double.prod_symm.prod
  intro j
  rw [← (integer_column_sum coordinate j).tsum_eq]
  exact norm_tsum_le_tsum_norm (double.prod_symm.prod_factor j)

/-- Absolute summation of the original integer channels generates the odd-zeta coefficients. -/
theorem integer_strong_expansion (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j)
      (∑' n : ℕ, InverseAction.countingWindow n (ForcingTail.forcingRemainderState coordinate)) := by
  have whole : (∑' n : ℕ, InverseAction.countingWindow n (ForcingTail.forcingRemainderState coordinate)) =
      ∑' j : ℕ, arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j := by
    calc
      _ = ∑' n : ℕ, ∑' j : ℕ, integerTerm coordinate n j :=
        tsum_congr (fun n => (counted_forcing_expansion coordinate n).tsum_eq.symm)
      _ = ∑' j : ℕ, ∑' n : ℕ, integerTerm coordinate n j :=
        (double_norm_summable coordinate).of_norm.tsum_comm.symm
      _ = _ := tsum_congr (fun j => (integer_column_sum coordinate j).tsum_eq)
  exact whole ▸ (arithmetic_norm_summable coordinate).of_norm.hasSum

/-- This is the same mean-zero integer source consumed by CountingForcing. -/
theorem forcingSeries (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => arithmeticCoefficient coordinate j • ArithmeticMomentGram.centeredPower j)
      (CountingForcing.integerSource coordinate) := by
  simpa only [map_smul, ArithmeticMomentGram.centeredPower, CountingForcing.integerSource] using!
    (integer_strong_expansion coordinate).mapL Constructor.zeroMean

theorem forcingSeries_interval (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => arithmeticCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq))
      (CountingForcing.integerSource coordinate : Hq) := by
  exact (forcingSeries coordinate).mapL burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL

theorem forcingSeries_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun j : ℕ => ‖arithmeticCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq)‖) := by
  have original := (arithmetic_norm_summable coordinate).mul_left ‖Constructor.zeroMean‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ original
  intro j
  have actual := Constructor.zeroMean.le_opNorm
    (arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j)
  change ‖((arithmeticCoefficient coordinate j • ArithmeticMomentGram.centeredPower j : M) : Hq)‖ ≤ _
  rw [Submodule.norm_coe]
  simpa only [map_smul, ArithmeticMomentGram.centeredPower] using! actual

/-- The full right-slot source pairing is generated by its strong series, for the actual q test. -/
theorem original_pair (coordinate : BurnolCompletedMellinCoordinate) (state : Hq) :
    HasSum (fun j : ℕ => arithmeticCoefficient coordinate j *
      inner ℂ state (ArithmeticMomentGram.centeredPower j : Hq))
      (inner ℂ state (CountingForcing.integerSource coordinate : Hq)) := by
  simpa only [innerSL_apply_apply, inner_smul_right] using!
    (forcingSeries_interval coordinate).mapL (innerSL ℂ state)

private theorem actual_gram (left right : BurnolCompletedMellinCoordinate) (j k : ℕ) :
    inner ℂ (arithmeticCoefficient left j • (ArithmeticMomentGram.centeredPower j : Hq))
      (arithmeticCoefficient right k • (ArithmeticMomentGram.centeredPower k : Hq)) =
        star (arithmeticCoefficient left j) * arithmeticCoefficient right k *
          (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
            (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
              1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
  rw [inner_smul_left, inner_smul_right, ArithmeticMomentGram.inner_centered]
  simp only [starRingEnd_apply]
  ring

theorem original_gram_norm_summable (left right : BurnolCompletedMellinCoordinate) :
    Summable (fun pair : ℕ × ℕ => ‖star (arithmeticCoefficient left pair.1) *
      arithmeticCoefficient right pair.2 *
        (2 * (q : ℂ) ^ (2 * pair.1 + 2 * pair.2 + 1) *
          (1 / (2 * (pair.1 : ℂ) + 2 * (pair.2 : ℂ) + 1) -
            1 / ((2 * (pair.1 : ℂ) + 1) * (2 * (pair.2 : ℂ) + 1))))‖) := by
  have majorant := (forcingSeries_norm_summable left).mul_of_nonneg
    (forcingSeries_norm_summable right) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ majorant
  intro pair
  rw [← actual_gram]
  exact norm_inner_le_norm _ _

/-- The full arithmetic kernel is read in the original q Gram, with every cross degree retained. -/
theorem original_gram (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (CountingForcing.integerSource left : Hq) (CountingForcing.integerSource right : Hq) =
      ∑' j : ℕ, ∑' k : ℕ, star (arithmeticCoefficient left j) * arithmeticCoefficient right k *
        (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
          (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
            1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
  have leftRead := (forcingSeries_interval left).mapL
    (innerSLFlip ℂ (CountingForcing.integerSource right : Hq))
  calc
    _ = ∑' j : ℕ, inner ℂ
        (arithmeticCoefficient left j • (ArithmeticMomentGram.centeredPower j : Hq))
        (CountingForcing.integerSource right : Hq) := leftRead.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro j
      have rightRead := (forcingSeries_interval right).mapL
        (innerSL ℂ (arithmeticCoefficient left j • (ArithmeticMomentGram.centeredPower j : Hq)))
      calc
        _ = ∑' k : ℕ, inner ℂ
            (arithmeticCoefficient left j • (ArithmeticMomentGram.centeredPower j : Hq))
            (arithmeticCoefficient right k • (ArithmeticMomentGram.centeredPower k : Hq)) :=
          rightRead.tsum_eq.symm
        _ = _ := tsum_congr (fun k => actual_gram left right j k)

theorem original_norm (coordinate : BurnolCompletedMellinCoordinate) :
    (‖CountingForcing.integerSource coordinate‖ ^ 2 : ℂ) =
      ∑' j : ℕ, ∑' k : ℕ, star (arithmeticCoefficient coordinate j) * arithmeticCoefficient coordinate k *
        (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
          (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
            1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
  simpa only [inner_self_eq_norm_sq_to_K, Submodule.norm_coe] using! original_gram coordinate coordinate

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ArithmeticForcingKernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

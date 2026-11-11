import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticForcingKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticLogGram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ReturnedArithmeticKernel

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

/-- These moments are integrals of the original inverse-generated return. -/
def moment (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  ∫ y : ℝ in symmetricInterval q, (y : ℂ) ^ (2 * j) * burnolRieszReturnRaw coordinate y

def coefficient (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  ((-1 : ℂ) ^ j * (2 * (Real.pi : ℂ)) ^ (2 * j) / ((2 * j).factorial : ℂ)) * moment coordinate j

def arithmeticCoefficient (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  if j = 0 then 0 else coefficient coordinate j * riemannZeta (2 * j + 1 : ℕ)

def integerSource (coordinate : BurnolCompletedMellinCoordinate) : M :=
  Constructor.zeroMean (∑' n : ℕ, InverseAction.countingWindow n (WholeSourceWindow.smoothState coordinate))

theorem moment_zero (coordinate : BurnolCompletedMellinCoordinate) : moment coordinate 0 = 0 := by
  simpa only [moment, Nat.mul_zero, pow_zero, one_mul] using InverseTail.return_mean_zero coordinate

theorem coefficient_zero (coordinate : BurnolCompletedMellinCoordinate) : coefficient coordinate 0 = 0 := by
  rw [coefficient, moment_zero, mul_zero]

private theorem quarter_integral (f : ℝ → ℂ) :
    (∫ y : ℝ in symmetricInterval q, f y) = ∫ y : ℝ in (-q)..q, f y := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  rfl

private theorem phase_exp (x y : ℝ) :
    Constructor.phase x y = Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * (y : ℂ)) := by
  unfold Constructor.phase
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem phase_pair (x y : ℝ) : Constructor.phase x y + Constructor.phase x (-y) =
    2 * Complex.cos (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) := by
  rw [phase_exp, phase_exp, Complex.cos]
  have first : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * (y : ℂ) =
      -(2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) * Complex.I := by ring
  have second : (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * ((-y : ℝ) : ℂ) =
      (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) * Complex.I := by push_cast; ring
  rw [first, second]
  ring

theorem smooth_cosine (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    InverseTail.smoothFourier coordinate x =
      ∫ y : ℝ in symmetricInterval q,
        Complex.cos (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) * burnolRieszReturnRaw coordinate y := by
  have positive : Continuous (fun y : ℝ => Constructor.phase x y * burnolRieszReturnRaw coordinate y) :=
    (Constructor.phaseContinuous x).mul (burnolRieszReturnRaw_continuous coordinate)
  have negative : Continuous (fun y : ℝ => Constructor.phase x (-y) * burnolRieszReturnRaw coordinate y) :=
    ((Constructor.phaseContinuous x).comp continuous_neg).mul (burnolRieszReturnRaw_continuous coordinate)
  have reflected : (∫ y : ℝ in symmetricInterval q, Constructor.phase x (-y) * burnolRieszReturnRaw coordinate y) =
      ∫ y : ℝ in symmetricInterval q, Constructor.phase x y * burnolRieszReturnRaw coordinate y := by
    rw [quarter_integral, quarter_integral]
    have actual := intervalIntegral.integral_comp_neg
      (f := fun y : ℝ => Constructor.phase x y * burnolRieszReturnRaw coordinate y) (a := -q) (b := q)
    simpa only [return_raw_even, neg_neg] using actual
  have combined : (∫ y : ℝ in symmetricInterval q, Constructor.phase x y * burnolRieszReturnRaw coordinate y) +
      (∫ y : ℝ in symmetricInterval q, Constructor.phase x (-y) * burnolRieszReturnRaw coordinate y) =
      2 * ∫ y : ℝ in symmetricInterval q,
        Complex.cos (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) * burnolRieszReturnRaw coordinate y := by
    have positiveIntegral : IntegrableOn (fun y : ℝ => Constructor.phase x y * burnolRieszReturnRaw coordinate y)
        (symmetricInterval q) := positive.integrableOn_Icc
    have negativeIntegral : IntegrableOn (fun y : ℝ => Constructor.phase x (-y) * burnolRieszReturnRaw coordinate y)
        (symmetricInterval q) := negative.integrableOn_Icc
    rw [← integral_add positiveIntegral negativeIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [← add_mul, phase_pair]
    ring
  rw [reflected] at combined
  rw [InverseTail.smoothFourier, Constructor.fourierRaw_integral, ← quarter_integral]
  linear_combination combined / 2

private def cosineTerm (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) (x y : ℝ) : ℂ :=
  ((-1 : ℂ) ^ j * (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) ^ (2 * j) /
    ((2 * j).factorial : ℂ)) * burnolRieszReturnRaw coordinate y

private theorem cosine_term_bound (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) (x y : ℝ)
    (insideX : |x| ≤ q) (insideY : |y| ≤ q) :
    ‖cosineTerm coordinate j x y‖ ≤ (1 / 4 : ℝ) ^ j * ‖burnolRieszReturnRaw coordinate y‖ := by
  have phase : ‖2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc
      _ ≤ 2 * 4 * q * q := by gcongr; exact Real.pi_le_four
      _ = _ := by norm_num
  have factorial : (1 : ℝ) ≤ (2 * j).factorial := by exact_mod_cast Nat.factorial_pos (2 * j)
  have scalar : ‖(-1 : ℂ) ^ j * (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) ^ (2 * j) /
      ((2 * j).factorial : ℂ)‖ ≤ (1 / 4 : ℝ) ^ j := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ ‖2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)‖ ^ (2 * j) := div_le_self (by positivity) factorial
      _ ≤ (1 / 2 : ℝ) ^ (2 * j) := pow_le_pow_left₀ (norm_nonneg _) phase _
      _ = _ := by rw [pow_mul]; norm_num
  rw [cosineTerm, norm_mul]
  exact mul_le_mul_of_nonneg_right scalar (norm_nonneg _)

private theorem coefficient_integral (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) (x : ℝ) :
    (∫ y : ℝ in symmetricInterval q, cosineTerm coordinate j x y) =
      coefficient coordinate j * (x : ℂ) ^ (2 * j) := by
  have identity : cosineTerm coordinate j x = fun y : ℝ =>
      (((-1 : ℂ) ^ j * (2 * (Real.pi : ℂ)) ^ (2 * j) / ((2 * j).factorial : ℂ)) * (x : ℂ) ^ (2 * j)) *
        ((y : ℂ) ^ (2 * j) * burnolRieszReturnRaw coordinate y) := by
    funext y
    simp only [cosineTerm, mul_pow]
    ring
  rw [identity, integral_const_mul]
  unfold coefficient moment
  ring

theorem coefficient_bound (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) (x : ℝ)
    (inside : |x| ≤ q) :
    ‖coefficient coordinate j * (x : ℂ) ^ (2 * j)‖ ≤ InverseTail.returnMass coordinate * (1 / 4 : ℝ) ^ j := by
  have regular : Continuous (cosineTerm coordinate j x) := by
    have returned := burnolRieszReturnRaw_continuous coordinate
    unfold cosineTerm
    fun_prop
  rw [← coefficient_integral]
  calc
    _ ≤ ∫ y : ℝ in symmetricInterval q, ‖cosineTerm coordinate j x y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ in symmetricInterval q, (1 / 4 : ℝ) ^ j * ‖burnolRieszReturnRaw coordinate y‖ := by
      apply integral_mono_ae regular.norm.integrableOn_Icc
        ((burnolRieszReturnRaw_continuous coordinate).norm.integrableOn_Icc.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y located
      exact cosine_term_bound coordinate j x y inside (abs_le.mpr located)
    _ = _ := by rw [integral_const_mul]; exact mul_comm _ _

/-- The original return's even Fourier integral generates every coefficient before any arithmetic summation. -/
theorem scalar_expansion (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (inside : |x| ≤ q) :
    HasSum (fun j : ℕ => coefficient coordinate j * (x : ℂ) ^ (2 * j))
      (InverseTail.smoothFourier coordinate x) := by
  have powers : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have actual := hasSum_integral_of_dominated_convergence (μ := μq)
    (fun j : ℕ => fun y : ℝ => (1 / 4 : ℝ) ^ j * ‖burnolRieszReturnRaw coordinate y‖)
    (F := fun j : ℕ => cosineTerm coordinate j x)
    (f := fun y : ℝ => Complex.cos (2 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ)) * burnolRieszReturnRaw coordinate y)
    (fun j => by
      have returned := (burnolRieszReturnRaw_continuous coordinate).measurable
      have measured : Measurable (cosineTerm coordinate j x) := by unfold cosineTerm; fun_prop
      exact measured.aestronglyMeasurable)
    (fun j => by
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y located
      exact cosine_term_bound coordinate j x y inside (abs_le.mpr located))
    (by filter_upwards with y; exact powers.mul_right _)
    (by simp only [tsum_mul_right]; exact (burnolRieszReturnRaw_continuous coordinate).norm.integrableOn_Icc.const_mul _)
    (by filter_upwards with y; exact (Complex.hasSum_cos _).mul_right (burnolRieszReturnRaw coordinate y))
  simpa only [coefficient_integral, ← smooth_cosine] using actual

private theorem constant_norm_bound : ‖intervalConstant q‖ ≤ (1 : ℝ) := by
  have square : ‖intervalConstant q‖ ^ 2 = 2 * q := by
    exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
  norm_num at square
  nlinarith [norm_nonneg (intervalConstant q)]

theorem term_bound (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) :
    ‖coefficient coordinate j • ArithmeticMomentGram.powerL2 j‖ ≤
      InverseTail.returnMass coordinate * (1 / 4 : ℝ) ^ j := by
  have mass : 0 ≤ InverseTail.returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
  have compared : ‖coefficient coordinate j • ArithmeticMomentGram.powerL2 j‖ ≤
      (InverseTail.returnMass coordinate * (1 / 4 : ℝ) ^ j) * ‖intervalConstant q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_smul (coefficient coordinate j) (ArithmeticMomentGram.powerL2 j),
      ArithmeticMomentGram.power_coeFn j, intervalConstant_coeFn q,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x scaled actual constant inside
    rw [scaled, constant]
    simp only [Pi.smul_apply, smul_eq_mul, actual, ArithmeticMomentGram.powerRaw, norm_one, mul_one]
    exact coefficient_bound coordinate j x (abs_le.mpr inside)
  exact compared.trans (mul_le_of_le_one_right (by positivity) constant_norm_bound)

theorem norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun j : ℕ => ‖coefficient coordinate j • ArithmeticMomentGram.powerL2 j‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_bound coordinate)
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left _

/-- The original Fourier integral and the strong L² series represent the same return. -/
theorem smooth_strong_expansion (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => coefficient coordinate j • ArithmeticMomentGram.powerL2 j)
      (WholeSourceWindow.smoothState coordinate) := by
  have normSum := norm_summable coordinate
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
      WholeSourceWindow.smoothState coordinate := by
    apply Lp.ext
    filter_upwards [pointwise, terms, WholeSourceWindow.smoothState_ae_raw coordinate,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x summed actual source inside
    rw [source]
    exact (summed.congr_fun (fun j => (actual j).symm)).unique
      (scalar_expansion coordinate x (abs_le.mpr inside))
  exact same ▸ normSum.of_norm.hasSum

private def countingCLM (scale : ℝ) : Hq →L[ℂ] Hq :=
  (Real.sqrt scale : ℂ)⁻¹ • burnolQuarterRestriction.comp
    ((burnolMultiplicativeDilation (-Real.log scale)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      burnolQuarterZeroExtension)

private theorem countingCLM_apply (scale : ℝ) (state : Hq) :
    countingCLM scale state = InverseAction.countingWindow scale state := rfl

private def integerTerm (coordinate : BurnolCompletedMellinCoordinate) (n j : ℕ) : Hq :=
  ((n : ℂ)⁻¹) ^ (2 * j + 1) • (coefficient coordinate j • ArithmeticMomentGram.powerL2 j)

private theorem integer_term_bound (coordinate : BurnolCompletedMellinCoordinate) (n j : ℕ) :
    ‖integerTerm coordinate n j‖ ≤ ((n : ℝ)⁻¹) ^ 3 *
      (InverseTail.returnMass coordinate * (1 / 4 : ℝ) ^ j) := by
  have mass : 0 ≤ InverseTail.returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
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
  exact mul_le_mul scalar (term_bound coordinate j) (norm_nonneg _) (by positivity)

set_option maxHeartbeats 800000 in
private theorem double_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun pair : ℕ × ℕ => ‖integerTerm coordinate pair.1 pair.2‖) := by
  have mass : 0 ≤ InverseTail.returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
  have integers : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by decide : 1 < 3))
  have powers : Summable (fun j : ℕ => InverseTail.returnMass coordinate * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left _
  have majorant := integers.mul_of_nonneg powers (fun _ => by positivity) (fun _ => by positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun pair => integer_term_bound coordinate pair.1 pair.2) majorant

private theorem counted_scalar_expansion (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) :
    HasSum (fun j : ℕ => integerTerm coordinate n j)
      (InverseAction.countingWindow n (WholeSourceWindow.smoothState coordinate)) := by
  have actual := (smooth_strong_expansion coordinate).mapL (countingCLM n)
  rw [countingCLM_apply] at actual
  apply actual.congr_fun
  intro j
  rw [map_smul, countingCLM_apply, ArithmeticForcingKernel.counting_power]
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
      (∑' n : ℕ, InverseAction.countingWindow n (WholeSourceWindow.smoothState coordinate)) := by
  have whole : (∑' n : ℕ, InverseAction.countingWindow n (WholeSourceWindow.smoothState coordinate)) =
      ∑' j : ℕ, arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j := by
    calc
      _ = ∑' n : ℕ, ∑' j : ℕ, integerTerm coordinate n j :=
        tsum_congr (fun n => (counted_scalar_expansion coordinate n).tsum_eq.symm)
      _ = ∑' j : ℕ, ∑' n : ℕ, integerTerm coordinate n j :=
        (double_norm_summable coordinate).of_norm.tsum_comm.symm
      _ = _ := tsum_congr (fun j => (integer_column_sum coordinate j).tsum_eq)
  exact whole ▸ (arithmetic_norm_summable coordinate).of_norm.hasSum

/-- This is the original mean-zero integer source of the smooth return. -/
theorem returnedSeries (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => arithmeticCoefficient coordinate j • ArithmeticMomentGram.centeredPower j)
      (integerSource coordinate) := by
  simpa only [map_smul, ArithmeticMomentGram.centeredPower, integerSource] using!
    (integer_strong_expansion coordinate).mapL Constructor.zeroMean

theorem returnedSeries_interval (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => arithmeticCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq))
      (integerSource coordinate : Hq) := by
  exact (returnedSeries coordinate).mapL burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL

theorem returnedSeries_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun j : ℕ => ‖arithmeticCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq)‖) := by
  have original := (arithmetic_norm_summable coordinate).mul_left ‖Constructor.zeroMean‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ original
  intro j
  have actual := Constructor.zeroMean.le_opNorm
    (arithmeticCoefficient coordinate j • ArithmeticMomentGram.powerL2 j)
  change ‖((arithmeticCoefficient coordinate j • ArithmeticMomentGram.centeredPower j : M) : Hq)‖ ≤ _
  rw [Submodule.norm_coe]
  simpa only [map_smul, ArithmeticMomentGram.centeredPower] using! actual

/-- Every full continuous contribution is projected only after its actual constant value is paid. -/
theorem original_forward (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Constructor.zeroMean (burnolQuarterRestriction (AmbientCounting.value coordinate)) =
      CountingForcing.integerSource coordinate + integerSource coordinate -
        fourierMean coordinate • CenteredCountingDual.logarithm := by
  rw [AmbientContact.original_position_slot coordinate zero, AmbientContact.positionSlot, AmbientContact.regularSlot,
    AmbientContinuousMean.forcing_continuous, AmbientContinuousMean.return_continuous]
  simp only [map_sub, map_add, map_smul, Constructor.zeroMean_constant, smul_zero, sub_zero, zero_add]
  rfl

def combinedCoefficient (coordinate : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  ArithmeticForcingKernel.arithmeticCoefficient coordinate j + arithmeticCoefficient coordinate j

theorem combined_series (coordinate : BurnolCompletedMellinCoordinate) :
    HasSum (fun j : ℕ => combinedCoefficient coordinate j • ArithmeticMomentGram.centeredPower j)
      (CountingForcing.integerSource coordinate + integerSource coordinate) := by
  simpa only [combinedCoefficient, add_smul] using!
    (ArithmeticForcingKernel.forcingSeries coordinate).add (returnedSeries coordinate)

/-- The whole counted b is generated in the shared q carrier, with its original Fourier mean intact. -/
theorem original_series (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    HasSum (fun j : ℕ => combinedCoefficient coordinate j • ArithmeticMomentGram.centeredPower j)
      (Constructor.zeroMean (burnolQuarterRestriction (AmbientCounting.value coordinate)) +
        fourierMean coordinate • CenteredCountingDual.logarithm) := by
  rw [original_forward coordinate zero, sub_add_cancel]
  exact combined_series coordinate

theorem original_series_interval (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    HasSum (fun j : ℕ => combinedCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq))
      ((Constructor.zeroMean (burnolQuarterRestriction (AmbientCounting.value coordinate)) : Hq) +
        fourierMean coordinate • (CenteredCountingDual.logarithm : Hq)) :=
  (original_series coordinate zero).mapL burnolQuarterMeanZeroClosedFace.toSubmodule.subtypeL

theorem combined_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun j : ℕ => ‖combinedCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq)‖) := by
  have majorant := (ArithmeticForcingKernel.forcingSeries_norm_summable coordinate).add
    (returnedSeries_norm_summable coordinate)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ majorant
  intro j
  rw [combinedCoefficient, add_smul]
  exact norm_add_le _ _

private theorem gram_entry (coordinate : BurnolCompletedMellinCoordinate) (j k : ℕ) :
    inner ℂ (combinedCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq))
      (ArithmeticForcingKernel.arithmeticCoefficient coordinate k • (ArithmeticMomentGram.centeredPower k : Hq)) =
      star (combinedCoefficient coordinate j) * ArithmeticForcingKernel.arithmeticCoefficient coordinate k *
        (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
          (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
            1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
  rw [inner_smul_left, inner_smul_right, ArithmeticMomentGram.inner_centered]
  simp only [starRingEnd_apply]
  ring

theorem original_gram_norm_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun pair : ℕ × ℕ => ‖star (combinedCoefficient coordinate pair.1) *
      ArithmeticForcingKernel.arithmeticCoefficient coordinate pair.2 *
        (2 * (q : ℂ) ^ (2 * pair.1 + 2 * pair.2 + 1) *
          (1 / (2 * (pair.1 : ℂ) + 2 * (pair.2 : ℂ) + 1) -
            1 / ((2 * (pair.1 : ℂ) + 1) * (2 * (pair.2 : ℂ) + 1))))‖) := by
  have majorant := (combined_norm_summable coordinate).mul_of_nonneg
    (ArithmeticForcingKernel.forcingSeries_norm_summable coordinate) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ majorant
  intro pair
  rw [← gram_entry]
  exact norm_inner_le_norm _ _

/-- Both slots are the actual complete sources. The return moments and original logarithmic mean survive explicitly. -/
theorem original_forcing_pair (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (Constructor.zeroMean (burnolQuarterRestriction (AmbientCounting.value coordinate)) : Hq)
      (CountingForcing.integerSource coordinate : Hq) =
      (∑' j : ℕ, ∑' k : ℕ, star (combinedCoefficient coordinate j) *
        ArithmeticForcingKernel.arithmeticCoefficient coordinate k *
          (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
            (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
              1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1))))) -
        star (fourierMean coordinate) *
          (∑' k : ℕ, ArithmeticForcingKernel.arithmeticCoefficient coordinate k *
            (4 * (k : ℂ) * (q : ℂ) ^ (2 * k + 1) / (2 * (k : ℂ) + 1) ^ 2)) := by
  have leftRead := (original_series_interval coordinate zero).mapL
    (innerSLFlip ℂ (CountingForcing.integerSource coordinate : Hq))
  have whole : inner ℂ
      ((Constructor.zeroMean (burnolQuarterRestriction (AmbientCounting.value coordinate)) : Hq) +
        fourierMean coordinate • (CenteredCountingDual.logarithm : Hq))
      (CountingForcing.integerSource coordinate : Hq) =
        ∑' j : ℕ, ∑' k : ℕ, star (combinedCoefficient coordinate j) *
          ArithmeticForcingKernel.arithmeticCoefficient coordinate k *
            (2 * (q : ℂ) ^ (2 * j + 2 * k + 1) *
              (1 / (2 * (j : ℂ) + 2 * (k : ℂ) + 1) -
                1 / ((2 * (j : ℂ) + 1) * (2 * (k : ℂ) + 1)))) := by
    calc
      _ = ∑' j : ℕ, inner ℂ (combinedCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq))
          (CountingForcing.integerSource coordinate : Hq) := leftRead.tsum_eq.symm
      _ = _ := by
        apply tsum_congr
        intro j
        have rightRead := (ArithmeticForcingKernel.forcingSeries_interval coordinate).mapL
          (innerSL ℂ (combinedCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq)))
        calc
          _ = ∑' k : ℕ, inner ℂ (combinedCoefficient coordinate j • (ArithmeticMomentGram.centeredPower j : Hq))
              (ArithmeticForcingKernel.arithmeticCoefficient coordinate k • (ArithmeticMomentGram.centeredPower k : Hq)) :=
            rightRead.tsum_eq.symm
          _ = _ := tsum_congr (fun k => gram_entry coordinate j k)
  have logRead : inner ℂ (CenteredCountingDual.logarithm : Hq) (CountingForcing.integerSource coordinate : Hq) =
      ∑' k : ℕ, ArithmeticForcingKernel.arithmeticCoefficient coordinate k *
        (4 * (k : ℂ) * (q : ℂ) ^ (2 * k + 1) / (2 * (k : ℂ) + 1) ^ 2) :=
    ArithmeticLogGram.original_log_pair coordinate
  rw [inner_add_left, inner_smul_left, logRead] at whole
  simp only [starRingEnd_apply] at whole
  linear_combination whole

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ReturnedArithmeticKernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

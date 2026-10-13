import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseAction
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.ExteriorRaw
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.InverseTail

open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszFinitePairing InverseAction

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

local instance : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def returnMass (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ∫ x : ℝ, ‖burnolRieszReturnRaw coordinate x‖ ∂μq

def smoothFourier (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  Constructor.fourierRaw (burnolRieszReturnRaw coordinate)

private theorem quarter_integral (raw : ℝ → ℂ) :
    (∫ x : ℝ, raw x ∂μq) = ∫ x : ℝ in (-q)..q, raw x := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  rfl

theorem return_mean_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ, burnolRieszReturnRaw coordinate x ∂μq) = 0 := by
  rw [quarter_integral, Constructor.return_integral_zero]

theorem return_first_moment_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ, (x : ℂ) * burnolRieszReturnRaw coordinate x ∂μq) = 0 := by
  rw [quarter_integral]
  have reflected := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => (x : ℂ) * burnolRieszReturnRaw coordinate x) (a := -q) (b := q)
  simp only [neg_neg, Complex.ofReal_neg, return_raw_even, neg_mul,
    intervalIntegral.integral_neg] at reflected
  linear_combination -reflected / 2

def phaseLinear (scale x y : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) * Complex.I * ((x / scale : ℝ) : ℂ) * (y : ℂ)

private theorem phase_exp (scale x y : ℝ) :
    Constructor.phase (x / scale) y = Complex.exp (phaseLinear scale x y) := by
  unfold Constructor.phase phaseLinear
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem phase_remainder_bound (scale : ℝ) (large : 1 ≤ scale)
    {x y : ℝ} (insideX : |x| ≤ q) (insideY : |y| ≤ q) :
    ‖Constructor.phase (x / scale) y - 1 - phaseLinear scale x y‖ ≤ scale⁻¹ ^ 2 := by
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  have bound : ‖phaseLinear scale x y‖ ≤ scale⁻¹ := by
    unfold phaseLinear
    simp only [norm_mul, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, abs_of_pos Real.pi_pos, abs_div, abs_of_pos positive]
    calc
      2 * Real.pi * (|x| / scale) * |y| ≤ 2 * 4 * (q / scale) * q := by
        gcongr
        exact Real.pi_le_four
      _ = (1 / 2 : ℝ) * scale⁻¹ := by ring
      _ ≤ scale⁻¹ := by nlinarith [inv_pos.mpr positive]
  have inverseBound : scale⁻¹ ≤ 1 := (inv_le_one₀ positive).mpr large
  rw [phase_exp]
  exact (Complex.norm_exp_sub_one_sub_id_le (bound.trans inverseBound)).trans
    (by gcongr)

private theorem continuous_integrable (raw : ℝ → ℂ) (regular : Continuous raw) :
    Integrable raw μq := by
  simpa only [symmetricInterval] using! regular.integrableOn_Icc

theorem smoothFourier_remainder (coordinate : BurnolCompletedMellinCoordinate)
    (scale x : ℝ) :
    smoothFourier coordinate (x / scale) =
      ∫ y : ℝ, (Constructor.phase (x / scale) y - 1 - phaseLinear scale x y) *
        burnolRieszReturnRaw coordinate y ∂μq := by
  have sourceContinuous := burnolRieszReturnRaw_continuous coordinate
  have phaseContinuous := Constructor.phaseContinuous (x / scale)
  have linearContinuous : Continuous (fun y : ℝ => phaseLinear scale x y *
      burnolRieszReturnRaw coordinate y) := by
    unfold phaseLinear
    fun_prop
  have remainderSplit : (fun y : ℝ =>
      (Constructor.phase (x / scale) y - 1 - phaseLinear scale x y) *
        burnolRieszReturnRaw coordinate y) = fun y =>
      (Constructor.phase (x / scale) y * burnolRieszReturnRaw coordinate y -
        burnolRieszReturnRaw coordinate y) -
          phaseLinear scale x y * burnolRieszReturnRaw coordinate y := by
    funext y
    ring
  have moment : (∫ y : ℝ, phaseLinear scale x y * burnolRieszReturnRaw coordinate y ∂μq) = 0 := by
    have factor : (fun y : ℝ => phaseLinear scale x y * burnolRieszReturnRaw coordinate y) =
        fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * ((x / scale : ℝ) : ℂ)) *
          ((y : ℂ) * burnolRieszReturnRaw coordinate y) := by
      funext y
      unfold phaseLinear
      ring
    rw [factor, integral_const_mul, return_first_moment_zero, mul_zero]
  rw [remainderSplit, integral_sub
    (f := fun y => Constructor.phase (x / scale) y * burnolRieszReturnRaw coordinate y -
      burnolRieszReturnRaw coordinate y)
    (g := fun y => phaseLinear scale x y * burnolRieszReturnRaw coordinate y)
    ((continuous_integrable _ (phaseContinuous.mul sourceContinuous)).sub
      (continuous_integrable _ sourceContinuous))
    (continuous_integrable _ linearContinuous),
    integral_sub (f := fun y => Constructor.phase (x / scale) y * burnolRieszReturnRaw coordinate y)
      (g := burnolRieszReturnRaw coordinate)
      (continuous_integrable _ (phaseContinuous.mul sourceContinuous))
      (continuous_integrable _ sourceContinuous), return_mean_zero, moment, sub_zero, sub_zero]
  rw [smoothFourier, Constructor.fourierRaw_integral, quarter_integral]

theorem smoothFourier_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) {x : ℝ} (inside : |x| ≤ q) :
    ‖smoothFourier coordinate (x / scale)‖ ≤ scale⁻¹ ^ 2 * returnMass coordinate := by
  rw [smoothFourier_remainder]
  have majorant : Integrable (fun y : ℝ => scale⁻¹ ^ 2 * ‖burnolRieszReturnRaw coordinate y‖) μq :=
    ((continuous_integrable _ (burnolRieszReturnRaw_continuous coordinate)).norm).const_mul _
  calc
    _ ≤ ∫ y : ℝ, scale⁻¹ ^ 2 * ‖burnolRieszReturnRaw coordinate y‖ ∂μq := by
      apply norm_integral_le_of_norm_le majorant
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (phase_remainder_bound scale large inside (abs_le.mpr hy)) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; rfl

theorem original_square_centered (coordinate : BurnolCompletedMellinCoordinate) :
    squareRaw (burnolRieszSingleFourierSourceRaw coordinate) = centeredRaw (smoothFourier coordinate) := by
  rw [← square_raw (burnolRieszSingleFourierSource coordinate)
    (burnolRieszSingleFourierSourceRaw coordinate) (burnolRieszSingleFourierSource_ae_raw coordinate)]
  exact meanZeroFourier_raw _ _ (Constructor.returnState_read coordinate)

private theorem quarter_volume : (μq).real univ = (1 / 2 : ℝ) := by
  convert! burnolRadiusInterval_measureReal_univ (by norm_num : (0 : ℝ) < q) using 1
  norm_num

private theorem shrink_inside (scale : ℝ) (large : 1 ≤ scale)
    {x : ℝ} (inside : x ∈ symmetricInterval q) : x / scale ∈ symmetricInterval q := by
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  apply abs_le.mp
  rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
  have bounded := abs_le.mpr inside
  nlinarith

/-- The actual fixed-window mean cancels the constant Fourier return before
any decay bound is applied. -/
theorem centered_counting_cancel_constant (scale : ℝ) (large : 1 ≤ scale)
    (raw : ℝ → ℂ) (regular : Continuous raw) {x : ℝ} (inside : x ∈ symmetricInterval q) :
    centeredRaw (countingRaw scale (centeredRaw raw)) x =
      (scale : ℂ)⁻¹ * centeredRaw (fun y : ℝ => raw (y / scale)) x := by
  let moved := fun y : ℝ => raw (y / scale)
  have movedRegular : Continuous moved := regular.comp (by fun_prop)
  have read (y : ℝ) (insideY : y ∈ symmetricInterval q) :
      countingRaw scale (centeredRaw raw) y =
        (scale : ℂ)⁻¹ * (moved y - rawMean raw) := by
    rw [countingRaw, indicator_of_mem (shrink_inside scale large insideY)]
    rfl
  have meanRead : rawMean (countingRaw scale (centeredRaw raw)) =
      (scale : ℂ)⁻¹ * (rawMean moved - rawMean raw) := by
    unfold rawMean
    rw [integral_congr_ae (show (countingRaw scale (centeredRaw raw)) =ᵐ[μq]
      (fun y => (scale : ℂ)⁻¹ * (moved y - rawMean raw)) from by
        filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y insideY
        exact read y insideY), integral_const_mul,
      integral_sub (continuous_integrable moved movedRegular) (integrable_const _),
      integral_const, quarter_volume, Complex.real_smul]
    norm_num
    unfold rawMean
    ring
  rw [centeredRaw, read x inside, meanRead]
  change _ = (scale : ℂ)⁻¹ * (moved x - rawMean moved)
  ring

theorem smooth_inverse_counting_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) {x : ℝ} (inside : x ∈ symmetricInterval q) :
    ‖centeredRaw (countingRaw scale (squareRaw (burnolRieszSingleFourierSourceRaw coordinate))) x‖ ≤
      2 * returnMass coordinate * scale⁻¹ ^ 3 := by
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  have massNonnegative : 0 ≤ returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
  let bound := scale⁻¹ ^ 2 * returnMass coordinate
  have boundNonnegative : 0 ≤ bound := mul_nonneg (sq_nonneg _) massNonnegative
  have meanBound : ‖rawMean (fun y : ℝ => smoothFourier coordinate (y / scale))‖ ≤ bound := by
    have integralBound : ‖∫ y : ℝ, smoothFourier coordinate (y / scale) ∂μq‖ ≤
        bound * (1 / 2 : ℝ) := by
      rw [← quarter_volume]
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y insideY
      exact smoothFourier_bound coordinate scale large (abs_le.mpr insideY)
    unfold rawMean
    rw [norm_mul]
    norm_num
    linarith
  rw [original_square_centered, centered_counting_cancel_constant scale large (smoothFourier coordinate)
    (Constructor.fourierRaw_continuous _ (burnolRieszReturnRaw_continuous coordinate)) inside,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  unfold centeredRaw
  calc
    scale⁻¹ * ‖smoothFourier coordinate (x / scale) -
        rawMean (fun y : ℝ => smoothFourier coordinate (y / scale))‖ ≤
      scale⁻¹ * (‖smoothFourier coordinate (x / scale)‖ +
        ‖rawMean (fun y : ℝ => smoothFourier coordinate (y / scale))‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr positive.le)
    _ ≤ scale⁻¹ * (bound + bound) := by
      gcongr
      exact smoothFourier_bound coordinate scale large (abs_le.mpr inside)
    _ = _ := by dsimp only [bound]; ring

theorem original_inverse_counting_ae_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    ∀ᵐ x : ℝ ∂μq,
      ‖(centeredCounting scale (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))) : ℝ → ℂ) x‖ ≤
          2 * returnMass coordinate * scale⁻¹ ^ 3 := by
  have squareRead : (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) :
        ℝ → ℂ) =ᵐ[μq] squareRaw (burnolRieszSingleFourierSourceRaw coordinate) := by
    rw [← square_raw _ _ (burnolRieszSingleFourierSource_ae_raw coordinate)]
    exact burnolMeanZeroFourier_ae_raw _
  have read := centeredCounting_raw scale (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large)
    _ _ squareRead
  filter_upwards [read, ae_restrict_mem (measurableSet_symmetricInterval q)] with x actual inside
  rw [actual]
  exact smooth_inverse_counting_bound coordinate scale large inside

theorem original_inverse_counting_norm_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    ‖centeredCounting scale (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))‖ ≤
        2 * returnMass coordinate * scale⁻¹ ^ 3 := by
  let value : BurnolQuarterIntervalL2 := centeredCounting scale (burnolMeanZeroTruncatedFourier
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))
  let bound := 2 * returnMass coordinate * scale⁻¹ ^ 3
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  have massNonnegative : 0 ≤ returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
  have boundNonnegative : 0 ≤ bound := mul_nonneg (mul_nonneg (by norm_num) massNonnegative)
    (pow_nonneg (inv_nonneg.mpr positive.le) _)
  have compared : ‖value‖ ≤ bound * ‖intervalConstant q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [original_inverse_counting_ae_bound coordinate scale large,
      intervalConstant_coeFn q] with x bounded constant
    rw [constant, norm_one, mul_one]
    exact bounded
  have constantBound : ‖intervalConstant q‖ ≤ (1 : ℝ) := by
    have square : ‖intervalConstant q‖ ^ 2 = 2 * q := by
      exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
    norm_num at square
    nlinarith [norm_nonneg (intervalConstant q)]
  exact compared.trans (by nlinarith)

/-- The smooth inverse part has a genuinely summable counting tail. -/
theorem original_inverse_counting_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun n : ℕ => centeredCounting (n : ℝ) (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)))) := by
  have powers : Summable (fun n : ℕ => (n : ℝ)⁻¹ ^ 3) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ)))
  apply (powers.mul_left (2 * returnMass coordinate)).of_norm_bounded
  intro n
  by_cases zero : n = 0
  · subst n
    simp [centeredCounting, countingWindow]
  · exact original_inverse_counting_norm_bound coordinate (n : ℝ)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)

/-- The same original inverse equation separates the actual counted source
into its explicit forcing and the newly controlled smooth tail. -/
theorem original_source_counting_split (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) :
    centeredCounting scale (burnolRieszSingleFourierSource coordinate) =
      centeredCounting scale
        (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)) +
      centeredCounting scale (burnolMeanZeroTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))) := by
  have source := burnolRieszSingleFourierSource_equation coordinate
  change burnolRieszSingleFourierSource coordinate - burnolMeanZeroTruncatedFourier
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) = _ at source
  have actual := eq_add_of_sub_eq source
  have moved := congrArg (centeredCounting scale) actual
  rw [moved]
  simp only [centeredCounting, countingWindow, Submodule.coe_add, map_add, smul_add]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.InverseTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingPrimitive
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseAction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ForcingTail

open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward.InverseAction ForcingPrimitive

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

local instance : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem quarter_volume : (μq).real univ = (1 / 2 : ℝ) := by
  convert! burnolRadiusInterval_measureReal_univ (by norm_num : (0 : ℝ) < q) using 1
  norm_num

private theorem quarter_integral (raw : ℝ → ℂ) :
    (∫ x : ℝ, raw x ∂μq) = ∫ x : ℝ in (-q)..q, raw x := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  rfl

private theorem fourier_one (frequency : ℝ) :
    burnolRadiusTruncatedFourierRaw q (intervalConstant q) frequency =
      ∫ y : ℝ, Constructor.phase frequency y ∂μq := by
  have raw := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  rw [← Constructor.fourierRaw_state, congrFun raw frequency, Constructor.fourierRaw_integral,
    quarter_integral]
  simp only [mul_one]

def phaseLinear (frequency position : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ) * (position : ℂ)

def phaseRemainder (frequency position : ℝ) : ℂ :=
  Constructor.phase frequency position - 1 - phaseLinear frequency position

private theorem phase_exp (frequency position : ℝ) :
    Constructor.phase frequency position = Complex.exp (phaseLinear frequency position) := by
  unfold Constructor.phase phaseLinear
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem phase_remainder_bound {frequency position : ℝ}
    (small : |frequency| ≤ q) (inside : |position| ≤ q) :
    ‖phaseRemainder frequency position‖ ≤ 4 * frequency ^ 2 := by
  have bound : ‖phaseLinear frequency position‖ ≤ 2 * |frequency| := by
    unfold phaseLinear
    simp only [norm_mul, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, abs_of_pos Real.pi_pos]
    calc
      2 * Real.pi * |frequency| * |position| ≤ 2 * 4 * |frequency| * q := by
        gcongr
        exact Real.pi_le_four
      _ = 2 * |frequency| := by ring
  have smallPhase : ‖phaseLinear frequency position‖ ≤ 1 := by linarith
  rw [phaseRemainder, phase_exp]
  calc
    _ ≤ ‖phaseLinear frequency position‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le smallPhase
    _ ≤ (2 * |frequency|) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, sq_abs]; ring

private theorem continuous_integrable (raw : ℝ → ℂ) (regular : Continuous raw) :
    Integrable raw μq := by
  simpa only [symmetricInterval] using! regular.integrableOn_Icc

private theorem linear_integral_zero (frequency : ℝ) :
    (∫ y : ℝ, phaseLinear frequency y ∂μq) = 0 := by
  rw [quarter_integral]
  have reflected := intervalIntegral.integral_comp_neg
    (f := phaseLinear frequency) (a := -q) (b := q)
  have parity : (fun y : ℝ => phaseLinear frequency (-y)) = fun y => -phaseLinear frequency y := by
    funext y
    unfold phaseLinear
    push_cast
    ring
  rw [parity, intervalIntegral.integral_neg, neg_neg] at reflected
  linear_combination -reflected / 2

/-- Both endpoint exponentials and the full T1 normalization have their
constant and linear terms removed by the original symmetric source. -/
theorem edge_remainder (frequency : ℝ) :
    Edge.raw q frequency = (q : ℂ) * (phaseRemainder frequency q + phaseRemainder frequency (-q)) -
      ∫ y : ℝ, phaseRemainder frequency y ∂μq := by
  have linearContinuous : Continuous (phaseLinear frequency) := by unfold phaseLinear; fun_prop
  have integralRead : (∫ y : ℝ, phaseRemainder frequency y ∂μq) =
      (∫ y : ℝ, Constructor.phase frequency y ∂μq) - (1 / 2 : ℂ) := by
    unfold phaseRemainder
    rw [integral_sub (f := fun y => Constructor.phase frequency y - 1)
      (g := phaseLinear frequency)
      ((continuous_integrable _ (Constructor.phaseContinuous frequency)).sub (integrable_const _))
      (continuous_integrable _ linearContinuous),
      integral_sub (f := Constructor.phase frequency) (g := fun _ : ℝ => (1 : ℂ))
        (continuous_integrable _ (Constructor.phaseContinuous frequency)) (integrable_const _),
      linear_integral_zero, sub_zero, integral_const, quarter_volume, Complex.real_smul]
    norm_num
  have endpointRead : phaseRemainder frequency q + phaseRemainder frequency (-q) =
      Constructor.phase frequency q + Constructor.phase frequency (-q) - 2 := by
    unfold phaseRemainder phaseLinear
    push_cast
    ring
  rw [Edge.raw_apply, fourier_one, integralRead, endpointRead]
  norm_num
  ring

theorem edge_quadratic_bound {frequency : ℝ} (small : |frequency| ≤ q) :
    ‖Edge.raw q frequency‖ ≤ 4 * frequency ^ 2 := by
  have plus := phase_remainder_bound small (by norm_num : |q| ≤ q)
  have minus := phase_remainder_bound small (by norm_num : |-q| ≤ q)
  have integralBound : ‖∫ y : ℝ, phaseRemainder frequency y ∂μq‖ ≤
      (4 * frequency ^ 2) * (1 / 2 : ℝ) := by
    rw [← quarter_volume]
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inside
    exact phase_remainder_bound small (abs_le.mpr inside)
  rw [edge_remainder]
  calc
    _ ≤ ‖(q : ℂ) * (phaseRemainder frequency q + phaseRemainder frequency (-q))‖ +
      ‖∫ y : ℝ, phaseRemainder frequency y ∂μq‖ := norm_sub_le _ _
    _ ≤ (q : ℝ) * (‖phaseRemainder frequency q‖ + ‖phaseRemainder frequency (-q)‖) +
      ‖∫ y : ℝ, phaseRemainder frequency y ∂μq‖ := by
      rw [norm_mul]
      norm_num
      exact norm_add_le _ _
    _ ≤ (q : ℝ) * ((4 * frequency ^ 2) + (4 * frequency ^ 2)) +
      (4 * frequency ^ 2) * (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

theorem edge_zero : Edge.raw q 0 = 0 := by
  simpa using edge_quadratic_bound (frequency := 0) (by norm_num)

def edgeRemainder (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (star coordinate.value - 1) * edgePrimitive coordinate |x|

def forcingRemainder (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ForcingWhole.coefficient coordinate * edgeRemainder coordinate x

private theorem primitive_bound (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (small : x ≤ q) :
    ‖edgePrimitive coordinate x‖ ≤
      4 * x ^ (3 - coordinate.value.re) / (3 - coordinate.value.re) := by
  have exponent : -1 < 2 - coordinate.value.re := by linarith [coordinate.belowOne]
  have powerIntegrable : IntegrableOn (fun t : ℝ => t ^ (2 - coordinate.value.re)) (Ioc 0 x) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := x) exponent).1
  have powerIntegral : (∫ t : ℝ in Ioc 0 x, t ^ (2 - coordinate.value.re)) =
      x ^ (3 - coordinate.value.re) / (3 - coordinate.value.re) := by
    rw [← intervalIntegral.integral_of_le positive.le, integral_rpow (Or.inl exponent),
      show 2 - coordinate.value.re + 1 = 3 - coordinate.value.re by ring,
      Real.zero_rpow (by linarith [coordinate.belowOne] : 3 - coordinate.value.re ≠ 0), sub_zero]
  unfold edgePrimitive
  rw [intervalIntegral.integral_of_le positive.le]
  calc
    _ ≤ ∫ t : ℝ in Ioc 0 x, 4 * t ^ (2 - coordinate.value.re) := by
      apply norm_integral_le_of_norm_le (powerIntegrable.const_mul 4)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos inside.1]
      simp only [neg_re, star_def, conj_re]
      calc
        t ^ (-coordinate.value.re) * ‖Edge.raw q t‖ ≤
            t ^ (-coordinate.value.re) * (4 * t ^ 2) := by
          exact mul_le_mul_of_nonneg_left
            (edge_quadratic_bound (by rw [abs_of_pos inside.1]; exact inside.2.trans small))
            (Real.rpow_nonneg inside.1.le _)
        _ = 4 * t ^ (2 - coordinate.value.re) := by
          rw [← Real.rpow_natCast t 2]
          calc
            _ = 4 * (t ^ (-coordinate.value.re) * t ^ (2 : ℝ)) := by ring
            _ = _ := by rw [← Real.rpow_add inside.1]; congr 2; ring
    _ = _ := by rw [integral_const_mul, powerIntegral]; ring

theorem edgeRemainder_bound (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (small : |x| ≤ q) : ‖edgeRemainder coordinate x‖ ≤ 4 * x ^ 2 := by
  by_cases zero : x = 0
  · subst x
    simp [edgeRemainder, edgePrimitive]
  have positive : 0 < |x| := abs_pos.mpr zero
  have denominator : 0 < 3 - coordinate.value.re := by linarith [coordinate.belowOne]
  have powers : |x| ^ (coordinate.value.re - 1) * |x| ^ (3 - coordinate.value.re) = x ^ 2 := by
    rw [← Real.rpow_add positive, show (coordinate.value.re - 1) + (3 - coordinate.value.re) = 2 by ring,
      Real.rpow_two, sq_abs]
  unfold edgeRemainder
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive]
  simp only [sub_re, star_def, conj_re, one_re]
  calc
    _ ≤ |x| ^ (coordinate.value.re - 1) *
        (4 * |x| ^ (3 - coordinate.value.re) / (3 - coordinate.value.re)) := by
      gcongr
      exact primitive_bound coordinate |x| positive small
    _ = 4 * x ^ 2 / (3 - coordinate.value.re) := by
      calc
        _ = 4 * (|x| ^ (coordinate.value.re - 1) * |x| ^ (3 - coordinate.value.re)) /
          (3 - coordinate.value.re) := by ring
        _ = _ := by rw [powers]
    _ ≤ 4 * x ^ 2 := by
      rw [div_le_iff₀ denominator]
      nlinarith [sq_nonneg x, coordinate.belowOne]

theorem forcingRemainder_bound (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (small : |x| ≤ q) :
    ‖forcingRemainder coordinate x‖ ≤ 4 * ‖ForcingWhole.coefficient coordinate‖ * x ^ 2 := by
  rw [forcingRemainder, norm_mul]
  exact (mul_le_mul_of_nonneg_left (edgeRemainder_bound coordinate small) (norm_nonneg _)).trans_eq (by ring)

/-- The original source consists of its generated singular term, the controlled
edge remainder, its original mean, and its original smooth Fourier return. -/
theorem original_source_read (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    burnolRieszSingleFourierSourceRaw coordinate x =
      leadingCoefficient coordinate * (x : ℂ) ^ (star coordinate.value - 1) +
        forcingRemainder coordinate x - ForcingMeanZero.mean coordinate +
          Constructor.secondReturnRaw coordinate x := by
  rw [ForcingPrimitive.original_source_read coordinate x positive]
  unfold forcingRemainder edgeRemainder
  rw [abs_of_pos positive]
  ring

private theorem edgePrimitive_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (edgePrimitive coordinate) := by
  have exponent : -1 < (-star coordinate.value).re := by
    simpa only [neg_re, star_def, conj_re] using (neg_lt_neg coordinate.belowOne)
  exact intervalIntegral.continuous_primitive (fun a b =>
    (intervalIntegral.intervalIntegrable_cpow' (a := a) (b := b) exponent).mul_continuousOn
      (Edge.raw_continuous q).continuousOn) 0

theorem forcingRemainder_measurable (coordinate : BurnolCompletedMellinCoordinate) :
    Measurable (forcingRemainder coordinate) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  have nonzero : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
  have power := Complex.continuousAt_ofReal_cpow_const |x| (star coordinate.value - 1)
    (Or.inr (abs_pos.mpr nonzero).ne')
  exact (continuousAt_const.mul ((power.comp continuous_abs.continuousAt).mul
    ((edgePrimitive_continuous coordinate).continuousAt.comp continuous_abs.continuousAt))).continuousWithinAt

theorem forcingRemainder_memLp (coordinate : BurnolCompletedMellinCoordinate) :
    MemLp (forcingRemainder coordinate) 2 μq := by
  apply MemLp.of_bound (forcingRemainder_measurable coordinate).aestronglyMeasurable
    (4 * ‖ForcingWhole.coefficient coordinate‖)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  have squareBound : x ^ 2 ≤ 1 := by nlinarith [inside.1, inside.2]
  exact (forcingRemainder_bound coordinate (abs_le.mpr inside)).trans
    (by nlinarith [norm_nonneg (ForcingWhole.coefficient coordinate)])

def forcingRemainderState (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  (forcingRemainder_memLp coordinate).toLp (forcingRemainder coordinate)

theorem forcingRemainderState_ae_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (forcingRemainderState coordinate : ℝ → ℂ) =ᵐ[μq] forcingRemainder coordinate :=
  MemLp.coeFn_toLp _

def centeredForcingCounting (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) :
    BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (countingWindow scale (forcingRemainderState coordinate))

private theorem counting_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) {x : ℝ} (inside : x ∈ symmetricInterval q) :
    ‖countingRaw scale (forcingRemainder coordinate) x‖ ≤
      4 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3 := by
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  have moved : x / scale ∈ symmetricInterval q := by
    apply abs_le.mp
    rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
    have bounded := abs_le.mpr inside
    nlinarith
  have squareBound : x ^ 2 ≤ 1 := by nlinarith [inside.1, inside.2]
  rw [countingRaw, indicator_of_mem moved, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ scale⁻¹ * (4 * ‖ForcingWhole.coefficient coordinate‖ * (x / scale) ^ 2) :=
      mul_le_mul_of_nonneg_left (forcingRemainder_bound coordinate (abs_le.mpr moved))
        (inv_nonneg.mpr positive.le)
    _ = (4 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3) * x ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      have nonnegative : 0 ≤ 4 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3 := by positivity
      exact (mul_le_mul_of_nonneg_left squareBound nonnegative).trans_eq (mul_one _)

theorem centered_counting_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) {x : ℝ} (inside : x ∈ symmetricInterval q) :
    ‖centeredRaw (countingRaw scale (forcingRemainder coordinate)) x‖ ≤
      8 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3 := by
  let bound := 4 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3
  have meanBound : ‖rawMean (countingRaw scale (forcingRemainder coordinate))‖ ≤ bound := by
    have integralBound : ‖∫ y : ℝ, countingRaw scale (forcingRemainder coordinate) y ∂μq‖ ≤
        bound * (1 / 2 : ℝ) := by
      rw [← quarter_volume]
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y insideY
      exact counting_bound coordinate scale large insideY
    unfold rawMean
    rw [norm_mul]
    norm_num
    linarith
  unfold centeredRaw
  calc
    _ ≤ ‖countingRaw scale (forcingRemainder coordinate) x‖ +
      ‖rawMean (countingRaw scale (forcingRemainder coordinate))‖ := norm_sub_le _ _
    _ ≤ bound + bound := add_le_add (counting_bound coordinate scale large inside) meanBound
    _ = _ := by dsimp only [bound]; ring

theorem centeredForcingCounting_ae_raw (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (positive : 0 < scale) :
    (centeredForcingCounting coordinate scale : ℝ → ℂ) =ᵐ[μq]
      centeredRaw (countingRaw scale (forcingRemainder coordinate)) := by
  let value := countingWindow scale (forcingRemainderState coordinate)
  have read := countingWindow_raw scale positive _ _ (forcingRemainderState_ae_raw coordinate)
  have mean : burnolQuarterMeanCoefficient value =
      rawMean (countingRaw scale (forcingRemainder coordinate)) := by
    rw [Constructor.mean_integral, integral_congr_ae read]
    rfl
  change ((Constructor.zeroMean value : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq] _
  rw [Constructor.zeroMean_read]
  filter_upwards [Lp.coeFn_sub value (burnolQuarterMeanCoefficient value • intervalConstant q),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient value) (intervalConstant q), read,
    intervalConstant_coeFn q] with x subAt scaled actual constant
  rw [subAt]
  change value x - (burnolQuarterMeanCoefficient value • intervalConstant q : BurnolQuarterIntervalL2) x = _
  rw [scaled]
  change value x - burnolQuarterMeanCoefficient value * intervalConstant q x = _
  rw [actual, mean, constant, mul_one]
  rfl

theorem centeredForcingCounting_norm_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    ‖centeredForcingCounting coordinate scale‖ ≤
      8 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3 := by
  let value : BurnolQuarterIntervalL2 := centeredForcingCounting coordinate scale
  let bound := 8 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have compared : ‖value‖ ≤ bound * ‖intervalConstant q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [centeredForcingCounting_ae_raw coordinate scale positive,
      ae_restrict_mem (measurableSet_symmetricInterval q), intervalConstant_coeFn q] with x read inside constant
    rw [constant, norm_one, mul_one]
    change ‖(centeredForcingCounting coordinate scale : ℝ → ℂ) x‖ ≤ _
    rw [read]
    exact centered_counting_bound coordinate scale large inside
  have constantBound : ‖intervalConstant q‖ ≤ (1 : ℝ) := by
    have square : ‖intervalConstant q‖ ^ 2 = 2 * q := by
      exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
    norm_num at square
    nlinarith [norm_nonneg (intervalConstant q)]
  exact compared.trans (by nlinarith)

/-- Summability is obtained for the actual edge-generated forcing remainder,
without imposing regularity on the original singular source b. -/
theorem centeredForcingCounting_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun n : ℕ => centeredForcingCounting coordinate (n : ℝ)) := by
  have powers : Summable (fun n : ℕ => (n : ℝ)⁻¹ ^ 3) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ)))
  apply (powers.mul_left (8 * ‖ForcingWhole.coefficient coordinate‖)).of_norm_bounded
  intro n
  by_cases zero : n = 0
  · subst n
    simp [centeredForcingCounting, countingWindow]
  · exact centeredForcingCounting_norm_bound coordinate (n : ℝ)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)

def meanZeroRemainder (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (forcingRemainderState coordinate)

/-- Input centering and output centering differ by this original clipped
constant-window contact. The identity retains it at every scale. -/
theorem input_mean_contact (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) :
    centeredCounting scale (meanZeroRemainder coordinate) =
      centeredForcingCounting coordinate scale -
        burnolQuarterMeanCoefficient (forcingRemainderState coordinate) •
          Constructor.zeroMean (countingWindow scale (intervalConstant q)) := by
  have input : (meanZeroRemainder coordinate : BurnolQuarterIntervalL2) =
      forcingRemainderState coordinate - burnolQuarterMeanCoefficient (forcingRemainderState coordinate) •
        intervalConstant q := Constructor.zeroMean_read _
  unfold centeredCounting
  rw [input]
  simp only [countingWindow, map_sub, map_smul, smul_sub, smul_smul, centeredForcingCounting]
  module

theorem constant_counting_zero (scale : ℝ) (large : 1 ≤ scale) :
    Constructor.zeroMean (countingWindow scale (intervalConstant q)) = 0 := by
  have positive : 0 < scale := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) large
  have actual : countingWindow scale (intervalConstant q) = (scale : ℂ)⁻¹ • intervalConstant q := by
    apply Lp.ext
    filter_upwards [countingWindow_raw scale positive _ _ (intervalConstant_coeFn q),
      Lp.coeFn_smul ((scale : ℂ)⁻¹) (intervalConstant q), intervalConstant_coeFn q,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x read scaled constant inside
    rw [read, scaled]
    have moved : x / scale ∈ symmetricInterval q := by
      apply abs_le.mp
      rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
      have bounded := abs_le.mpr inside
      nlinarith
    simp only [countingRaw, indicator_of_mem moved, Pi.smul_apply, smul_eq_mul, constant, mul_one]
  rw [actual, map_smul, Constructor.zeroMean_constant, smul_zero]

/-- On a≥1 the input projection's actual constant contact vanishes; this is
the exact equality used to transfer the tail bound to the original b split. -/
theorem input_counting_eq (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    centeredCounting scale (meanZeroRemainder coordinate) = centeredForcingCounting coordinate scale := by
  rw [input_mean_contact, constant_counting_zero scale large, smul_zero, sub_zero]

theorem input_counting_norm_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    ‖centeredCounting scale (meanZeroRemainder coordinate)‖ ≤
      8 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 3 := by
  rw [input_counting_eq coordinate scale large]
  exact centeredForcingCounting_norm_bound coordinate scale large

theorem input_counting_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun n : ℕ => centeredCounting (n : ℝ) (meanZeroRemainder coordinate)) := by
  apply (centeredForcingCounting_summable coordinate).congr
  intro n
  by_cases zero : n = 0
  · subst n
    simp [centeredCounting, centeredForcingCounting, countingWindow]
  · exact (input_counting_eq coordinate (n : ℝ)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ForcingTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

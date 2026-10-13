import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingTail
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseTail
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Regularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ReciprocalTail

open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszSourceGreen
open OriginalRieszFinitePairing.CoPoisson.Ward.InverseTail

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

def weight (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : ℂ :=
  burnolRieszSingleFourierSourceRaw coordinate u⁻¹ / (u : ℂ)

def weightedSlope (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star coordinate.value * ForcingWhole.raw coordinate x +
    ForcingWhole.coefficient coordinate * Edge.raw q x - ForcingMeanZero.mean coordinate +
    Constructor.secondReturnRaw coordinate x +
    (x : ℂ) * Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x

private theorem source_split (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszSingleFourierSourceRaw coordinate x = ForcingWhole.raw coordinate x -
      ForcingMeanZero.mean coordinate + Constructor.secondReturnRaw coordinate x := by
  change burnolRieszFourierForcingRaw coordinate x + Constructor.secondReturnRaw coordinate x = _
  rw [ForcingMeanZero.forcingRaw_eq]

theorem weightedSource_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * burnolRieszSingleFourierSourceRaw coordinate y)
      (weightedSlope coordinate x) x := by
  have actual := ((forcing_weighted_hasDerivAt coordinate x positive.ne').sub
    (Complex.ofRealCLM.hasDerivAt.mul_const (ForcingMeanZero.mean coordinate))).add
      (Complex.ofRealCLM.hasDerivAt.mul (Constructor.secondReturnRaw_hasDerivAt coordinate x))
  convert! actual using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Complex.ofRealCLM_apply]
    rw [source_split]
    ring
  · simp only [weightedSlope, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    ring

theorem weight_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (positive : 0 < u) :
    HasDerivAt (weight coordinate)
      (-((u : ℂ)⁻¹ ^ 2) * weightedSlope coordinate u⁻¹) u := by
  have inverse := (hasDerivAt_id u).inv positive.ne'
  have actual := (weightedSource_hasDerivAt coordinate u⁻¹ (inv_pos.mpr positive)).scomp u inverse
  convert! actual using 1
  · funext v
    simp only [weight, Function.comp_apply, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  · simp only [Complex.real_smul, id_eq]
    push_cast
    simp only [div_eq_mul_inv, inv_pow]
    ring

theorem weight_deriv_measurable (coordinate : BurnolCompletedMellinCoordinate) :
    Measurable (deriv (weight coordinate)) := measurable_deriv _

theorem weight_eq_neg_fourierWeight (coordinate : BurnolCompletedMellinCoordinate) :
    weight coordinate = -OriginalRieszFinitePairing.CoPoisson.fourierWeight coordinate 0 := by
  funext u
  unfold weight OriginalRieszFinitePairing.CoPoisson.fourierWeight
    OriginalRieszFinitePairing.CoPoisson.reciprocalWeight
  norm_num
  ring

theorem weight_deriv_continuousOn (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (deriv (weight coordinate)) (Ioi 0) := by
  rw [weight_eq_neg_fourierWeight]
  change ContinuousOn (fun u => deriv (-OriginalRieszFinitePairing.CoPoisson.fourierWeight coordinate 0) u) (Ioi 0)
  simp only [deriv.neg]
  exact (OriginalRieszFinitePairing.CoPoisson.fourierWeight_deriv_continuousOn coordinate 0).neg

theorem weight_measurable (coordinate : BurnolCompletedMellinCoordinate) :
    Measurable (weight coordinate) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro u outside
  have nonzero : u ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
  exact (((burnolRieszSingleFourierSourceRaw_continuousAt coordinate (inv_ne_zero nonzero)).comp
    (continuousAt_inv₀ nonzero)).div Complex.continuous_ofReal.continuousAt
      (Complex.ofReal_ne_zero.mpr nonzero)).continuousWithinAt

private theorem return_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (burnolRieszReturnRaw coordinate) μq := by
  simpa only [symmetricInterval] using! (burnolRieszReturnRaw_continuous coordinate).integrableOn_Icc

private theorem quarter_integral (raw : ℝ → ℂ) :
    (∫ x : ℝ, raw x ∂μq) = ∫ x : ℝ in (-q)..q, raw x := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  rfl

theorem smoothFourier_uniform_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖smoothFourier coordinate x‖ ≤ returnMass coordinate :=
  VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 μq (innerₗ ℝ) (burnolRieszReturnRaw coordinate) x

theorem smoothDerivative_uniform_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x‖ ≤ 2 * returnMass coordinate := by
  rw [Constructor.fourierDerivative_integral _ (burnolRieszReturnRaw_continuous coordinate), ← quarter_integral]
  calc
    _ ≤ ∫ y : ℝ, 2 * ‖burnolRieszReturnRaw coordinate y‖ ∂μq := by
      apply norm_integral_le_of_norm_le ((return_integrable coordinate).norm.const_mul 2)
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inside
      simp only [norm_mul, Constructor.phase, Circle.norm_coe, one_mul, norm_neg,
        norm_ofNat, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one, abs_of_pos Real.pi_pos]
      have bound : 2 * Real.pi * |y| ≤ 2 := by
        calc
          _ ≤ 2 * 4 * q := by gcongr; exact Real.pi_le_four; exact abs_le.mpr inside
          _ = 2 := by ring
      exact mul_le_mul_of_nonneg_right bound (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; rfl

def returnMeanNorm (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ‖burnolQuarterMeanCoefficient (burnolTruncatedFourier (Constructor.returnState coordinate : BurnolQuarterIntervalL2))‖

theorem secondReturn_uniform_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖Constructor.secondReturnRaw coordinate x‖ ≤ returnMass coordinate + returnMeanNorm coordinate := by
  rw [Constructor.secondReturnRaw_eq_fourier]
  exact (norm_sub_le _ _).trans (add_le_add (smoothFourier_uniform_bound coordinate x) le_rfl)

def valueConstant (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  4 * ‖ForcingWhole.coefficient coordinate‖ + ‖ForcingMeanZero.mean coordinate‖ +
    returnMass coordinate + returnMeanNorm coordinate

def slopeConstant (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  4 * ‖star coordinate.value‖ * ‖ForcingWhole.coefficient coordinate‖ +
    4 * ‖ForcingWhole.coefficient coordinate‖ + ‖ForcingMeanZero.mean coordinate‖ +
      3 * returnMass coordinate + returnMeanNorm coordinate

private theorem returnMass_nonnegative (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)

theorem valueConstant_nonnegative (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ valueConstant coordinate := by
  have mass := returnMass_nonnegative coordinate
  unfold valueConstant returnMeanNorm
  positivity

theorem slopeConstant_nonnegative (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ slopeConstant coordinate := by
  have mass := returnMass_nonnegative coordinate
  unfold slopeConstant returnMeanNorm
  positivity

private theorem forcing_expansion (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    ForcingWhole.raw coordinate x =
      ForcingPrimitive.leadingCoefficient coordinate * (x : ℂ) ^ (star coordinate.value - 1) +
        ForcingTail.forcingRemainder coordinate x := by
  rw [ForcingPrimitive.forcing_read coordinate x positive]
  unfold ForcingTail.forcingRemainder ForcingTail.edgeRemainder
  rw [abs_of_pos positive]
  ring

theorem forcing_local_bound (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (small : x ≤ q) :
    ‖ForcingWhole.raw coordinate x‖ ≤
      ‖ForcingPrimitive.leadingCoefficient coordinate‖ * x ^ (coordinate.value.re - 1) +
        4 * ‖ForcingWhole.coefficient coordinate‖ := by
  have squareBound : x ^ 2 ≤ 1 := by nlinarith
  rw [forcing_expansion coordinate x positive]
  calc
    _ ≤ ‖ForcingPrimitive.leadingCoefficient coordinate * (x : ℂ) ^ (star coordinate.value - 1)‖ +
      ‖ForcingTail.forcingRemainder coordinate x‖ := norm_add_le _ _
    _ ≤ ‖ForcingPrimitive.leadingCoefficient coordinate‖ * x ^ (coordinate.value.re - 1) +
        (4 * ‖ForcingWhole.coefficient coordinate‖) * x ^ 2 := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive]
      simp only [sub_re, star_def, conj_re, one_re]
      exact add_le_add le_rfl (ForcingTail.forcingRemainder_bound coordinate
        (by rw [abs_of_pos positive]; exact small))
    _ ≤ _ := by
      apply add_le_add le_rfl
      exact (mul_le_mul_of_nonneg_left squareBound (by positivity)).trans_eq (mul_one _)

theorem source_local_bound (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (small : x ≤ q) :
    ‖burnolRieszSingleFourierSourceRaw coordinate x‖ ≤
      ‖ForcingPrimitive.leadingCoefficient coordinate‖ * x ^ (coordinate.value.re - 1) + valueConstant coordinate := by
  rw [source_split]
  calc
    _ ≤ ‖ForcingWhole.raw coordinate x - ForcingMeanZero.mean coordinate‖ +
      ‖Constructor.secondReturnRaw coordinate x‖ := norm_add_le _ _
    _ ≤ (‖ForcingWhole.raw coordinate x‖ + ‖ForcingMeanZero.mean coordinate‖) +
      ‖Constructor.secondReturnRaw coordinate x‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖ForcingPrimitive.leadingCoefficient coordinate‖ * x ^ (coordinate.value.re - 1) +
      4 * ‖ForcingWhole.coefficient coordinate‖) + ‖ForcingMeanZero.mean coordinate‖) +
        (returnMass coordinate + returnMeanNorm coordinate) := by
      exact add_le_add (add_le_add (forcing_local_bound coordinate x positive small) le_rfl)
        (secondReturn_uniform_bound coordinate x)
    _ = _ := by unfold valueConstant; ring

theorem weightedSlope_local_bound (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) (small : x ≤ q) :
    ‖weightedSlope coordinate x‖ ≤
      (‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        x ^ (coordinate.value.re - 1) + slopeConstant coordinate := by
  have edgeBound : ‖Edge.raw q x‖ ≤ 4 := by
    have actual := ForcingTail.edge_quadratic_bound (frequency := x) (by rw [abs_of_pos positive]; exact small)
    have square : x ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have massNonnegative := returnMass_nonnegative coordinate
  unfold weightedSlope
  calc
    _ ≤ ‖star coordinate.value * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x - ForcingMeanZero.mean coordinate +
        Constructor.secondReturnRaw coordinate x‖ +
      ‖(x : ℂ) * Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x‖ := norm_add_le _ _
    _ ≤ (‖star coordinate.value * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x - ForcingMeanZero.mean coordinate‖ +
      ‖Constructor.secondReturnRaw coordinate x‖) +
      ‖(x : ℂ) * Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖star coordinate.value * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x‖ + ‖ForcingMeanZero.mean coordinate‖) +
      ‖Constructor.secondReturnRaw coordinate x‖) +
      ‖(x : ℂ) * Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (((‖star coordinate.value * ForcingWhole.raw coordinate x‖ +
        ‖ForcingWhole.coefficient coordinate * Edge.raw q x‖) + ‖ForcingMeanZero.mean coordinate‖) +
      ‖Constructor.secondReturnRaw coordinate x‖) +
      ‖(x : ℂ) * Constructor.fourierDerivative (burnolRieszReturnRaw coordinate) x‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((‖star coordinate.value‖ *
        (‖ForcingPrimitive.leadingCoefficient coordinate‖ * x ^ (coordinate.value.re - 1) +
          4 * ‖ForcingWhole.coefficient coordinate‖) + ‖ForcingWhole.coefficient coordinate‖ * 4) +
        ‖ForcingMeanZero.mean coordinate‖) + (returnMass coordinate + returnMeanNorm coordinate)) +
        x * (2 * returnMass coordinate) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
      gcongr
      · exact forcing_local_bound coordinate x positive small
      · exact secondReturn_uniform_bound coordinate x
      · exact smoothDerivative_uniform_bound coordinate x
    _ ≤ (((‖star coordinate.value‖ *
        (‖ForcingPrimitive.leadingCoefficient coordinate‖ * x ^ (coordinate.value.re - 1) +
          4 * ‖ForcingWhole.coefficient coordinate‖) + ‖ForcingWhole.coefficient coordinate‖ * 4) +
        ‖ForcingMeanZero.mean coordinate‖) + (returnMass coordinate + returnMeanNorm coordinate)) +
        (2 * returnMass coordinate) := by
      apply add_le_add le_rfl
      exact (mul_le_mul_of_nonneg_right (by linarith : x ≤ 1)
        (mul_nonneg (by norm_num) massNonnegative)).trans_eq (one_mul _)
    _ = _ := by unfold slopeConstant; ring

private theorem reciprocal_small (u : ℝ) (large : 4 ≤ u) : u⁻¹ ≤ q := by
  have positive : 0 < u := by linarith
  rw [inv_eq_one_div, div_le_iff₀ positive]
  nlinarith

private theorem inverse_power_product (u : ℝ) (positive : 0 < u) (exponent : ℝ) (k : ℕ) :
    u⁻¹ ^ k * u⁻¹ ^ exponent = u ^ (-(k : ℝ) - exponent) := by
  rw [← Real.rpow_natCast u⁻¹ k, ← Real.rpow_add (inv_pos.mpr positive),
    ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

theorem weight_bound (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (large : 4 ≤ u) :
    ‖weight coordinate u‖ ≤ ‖ForcingPrimitive.leadingCoefficient coordinate‖ * u ^ (-coordinate.value.re) +
      valueConstant coordinate * u⁻¹ := by
  have positive : 0 < u := by linarith
  have source := source_local_bound coordinate u⁻¹ (inv_pos.mpr positive) (reciprocal_small u large)
  rw [weight, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ (‖ForcingPrimitive.leadingCoefficient coordinate‖ * u⁻¹ ^ (coordinate.value.re - 1) +
        valueConstant coordinate) / u := (div_le_div_iff_of_pos_right positive).mpr source
    _ = ‖ForcingPrimitive.leadingCoefficient coordinate‖ * (u⁻¹ ^ (1 : ℕ) * u⁻¹ ^ (coordinate.value.re - 1)) +
        valueConstant coordinate * u⁻¹ := by rw [div_eq_mul_inv, pow_one]; ring
    _ = _ := by
      rw [inverse_power_product u positive _ 1]
      simp only [Nat.cast_one]
      rw [
        show -(1 : ℝ) - (coordinate.value.re - 1) = -coordinate.value.re by ring]

theorem derivative_bound (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (large : 4 ≤ u) :
    ‖deriv (weight coordinate) u‖ ≤
      (‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        u ^ (-coordinate.value.re - 1) + slopeConstant coordinate * u⁻¹ ^ 2 := by
  have positive : 0 < u := by linarith
  rw [(weight_hasDerivAt coordinate u positive).deriv,
    norm_mul, norm_neg, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ u⁻¹ ^ 2 * ((‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        u⁻¹ ^ (coordinate.value.re - 1) + slopeConstant coordinate) :=
      mul_le_mul_of_nonneg_left
        (weightedSlope_local_bound coordinate u⁻¹ (inv_pos.mpr positive) (reciprocal_small u large)) (sq_nonneg _)
    _ = (‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        (u⁻¹ ^ 2 * u⁻¹ ^ (coordinate.value.re - 1)) + slopeConstant coordinate * u⁻¹ ^ 2 := by ring
    _ = _ := by
      rw [inverse_power_product u positive _ 2]
      simp only [Nat.cast_ofNat]
      rw [
        show -(2 : ℝ) - (coordinate.value.re - 1) = -coordinate.value.re - 1 by ring]

private theorem sqrt_bound (u : ℝ) (large : 4 ≤ u) : Real.sqrt u + 2 ≤ 3 * Real.sqrt u := by
  have rootLarge : 1 ≤ Real.sqrt u := (Real.one_le_sqrt).mpr (by linarith)
  linarith

private theorem power_times_sqrt (u : ℝ) (positive : 0 < u) (exponent : ℝ) :
    u ^ exponent * Real.sqrt u = u ^ (exponent + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add positive]

theorem derivative_weight_bound (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (large : 4 ≤ u) :
    ‖deriv (weight coordinate) u‖ * (Real.sqrt u + 2) ≤
      (3 * ‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        u ^ (-coordinate.value.re - 1 / 2) +
      (3 * slopeConstant coordinate) * u ^ (-(3 / 2 : ℝ)) := by
  have positive : 0 < u := by linarith
  have regularPower : u⁻¹ ^ 2 * Real.sqrt u = u ^ (-(3 / 2 : ℝ)) := by
    have inversePower : u⁻¹ ^ 2 = u ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow]
    rw [inversePower, power_times_sqrt u positive, show (-2 : ℝ) + 1 / 2 = -(3 / 2 : ℝ) by ring]
  have mainPower : u ^ (-coordinate.value.re - 1) * Real.sqrt u = u ^ (-coordinate.value.re - 1 / 2) := by
    rw [power_times_sqrt u positive]
    congr 1
    ring
  calc
    _ ≤ ((‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        u ^ (-coordinate.value.re - 1) + slopeConstant coordinate * u⁻¹ ^ 2) * (3 * Real.sqrt u) := by
      apply mul_le_mul (derivative_bound coordinate u large) (sqrt_bound u large)
        (by positivity) (by
          have nonnegative := slopeConstant_nonnegative coordinate
          positivity)
    _ = 3 * (‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖) *
        (u ^ (-coordinate.value.re - 1) * Real.sqrt u) +
        (3 * slopeConstant coordinate) * (u⁻¹ ^ 2 * Real.sqrt u) := by ring
    _ = _ := by rw [regularPower, mainPower]; ring

theorem derivative_weight_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun u : ℝ => ‖deriv (weight coordinate) u‖ * (Real.sqrt u + 2)) (Ioi 4) := by
  have first := (integrableOn_Ioi_rpow_of_lt
    (by linarith [coordinate.rightHalf] : -coordinate.value.re - 1 / 2 < -1)
    (by norm_num : (0 : ℝ) < 4)).const_mul
      (3 * ‖star coordinate.value‖ * ‖ForcingPrimitive.leadingCoefficient coordinate‖)
  have second := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : -(3 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 4)).const_mul
      (3 * slopeConstant coordinate)
  apply (first.add second).mono'
    (((weight_deriv_measurable coordinate).norm.mul
      (Real.continuous_sqrt.measurable.add_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u large
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖deriv (weight coordinate) u‖ * (Real.sqrt u + 2))]
  exact derivative_weight_bound coordinate u large.le

theorem head_bound (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (large : 4 ≤ u) :
    Real.sqrt u * ‖weight coordinate u‖ ≤
      ‖ForcingPrimitive.leadingCoefficient coordinate‖ * u ^ (1 / 2 - coordinate.value.re) +
        valueConstant coordinate * u ^ (-(1 / 2 : ℝ)) := by
  have positive : 0 < u := by linarith
  have leadingPower : u ^ (-coordinate.value.re) * Real.sqrt u = u ^ (1 / 2 - coordinate.value.re) := by
    rw [power_times_sqrt u positive]
    congr 1
    ring
  have regularPower : u⁻¹ * Real.sqrt u = u ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one u, power_times_sqrt u positive]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt u * (‖ForcingPrimitive.leadingCoefficient coordinate‖ * u ^ (-coordinate.value.re) +
        valueConstant coordinate * u⁻¹) :=
      mul_le_mul_of_nonneg_left (weight_bound coordinate u large) (Real.sqrt_nonneg _)
    _ = ‖ForcingPrimitive.leadingCoefficient coordinate‖ * (u ^ (-coordinate.value.re) * Real.sqrt u) +
        valueConstant coordinate * (u⁻¹ * Real.sqrt u) := by ring
    _ = _ := by rw [leadingPower, regularPower]

/-- The half-density head of the original source programme vanishes precisely
using the source coordinate's right-half exponent. -/
theorem head_tendsto_zero (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun u : ℝ => Real.sqrt u * ‖weight coordinate u‖) atTop (𝓝 0) := by
  have leading := (tendsto_rpow_neg_atTop
    (by linarith [coordinate.rightHalf] : 0 < coordinate.value.re - 1 / 2)).const_mul
      ‖ForcingPrimitive.leadingCoefficient coordinate‖
  have regular := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (valueConstant coordinate)
  apply squeeze_zero'
    (Eventually.of_forall (fun u : ℝ => mul_nonneg (Real.sqrt_nonneg u) (norm_nonneg _)))
    (show ∀ᶠ u : ℝ in atTop, Real.sqrt u * ‖weight coordinate u‖ ≤
      ‖ForcingPrimitive.leadingCoefficient coordinate‖ * u ^ (1 / 2 - coordinate.value.re) +
        valueConstant coordinate * u ^ (-(1 / 2 : ℝ)) from
      (eventually_ge_atTop (4 : ℝ)).mono (fun u large => head_bound coordinate u large))
  simpa only [neg_sub, mul_zero, zero_add] using leading.add regular

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ReciprocalTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

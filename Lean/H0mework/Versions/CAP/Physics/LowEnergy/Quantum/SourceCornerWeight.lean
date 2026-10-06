import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceSignedRadiusBalance
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceRelativePowerTail

/-! A source-generated joint-corner localizer keeps the original finite cutoff sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceCornerWeight
open GaussCoreHilbert GaussCoreDifferential GaussNativeEnergy GaussNativePotential
open GaussYukawaCoefficient GaussRadialDomain GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumNativeDimensions
open scoped ContDiff Topology InnerProductSpace

def gaugeRow (z : SourceCoordinateSlice) (i : Fin 3) : NativeLie :=
  ![z.1 0 • connectionField z 0,
    z.1 1 • connectionField z 0 + z.1 2 • connectionField z 1,
    z.1 3 • connectionField z 0 + z.1 4 • connectionField z 1 +
      z.1 5 • connectionField z 2] i

theorem gauge_row_source (z : SourceCoordinateSlice) (i : Fin 3) :
    gaugeRow z i = ∑ j : Fin 3, triad z.1 i j • connectionField z j := by
  fin_cases i <;> simp [gaugeRow, triad, Fin.sum_univ_succ, add_assoc]

private theorem gauge_row_smooth (i : Fin 3) :
    ContDiff ℝ ∞ (fun z => gaugeRow z i) := by
  have h0 := connectionField_smooth 0
  have h1 := connectionField_smooth 1
  have h2 := connectionField_smooth 2
  fin_cases i <;> dsimp [gaugeRow] <;> fun_prop

def gaugeSquare (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 3, inner ℝ (gaugeRow z i) (gaugeRow z i)

theorem gauge_square_nonneg (z : SourceCoordinateSlice) : 0 ≤ gaugeSquare z :=
  Finset.sum_nonneg (fun _ _ => real_inner_self_nonneg)

private theorem gauge_square_pos (z : physicalChart) : 0 < gaugeSquare z.val := by
  have hA : connectionField z.val 0 ≠ 0 := by
    intro he
    have hf := congrArg (fun A : NativeLie => (nativeCoordinates A).1 1) he
    change firstGauge (z.val.2.2 : Gauge) = (nativeCoordinates 0).1 1 at hf
    simp only [map_zero] at hf
    exact (ne_of_gt z.property.2.2.2.2.1) hf
  have hrow : gaugeRow z.val 0 ≠ 0 := by
    simpa only [gaugeRow, Matrix.cons_val_zero] using
      smul_ne_zero (ne_of_gt z.property.1) hA
  have hi : 0 < inner ℝ (gaugeRow z.val 0) (gaugeRow z.val 0) :=
    real_inner_self_pos.mpr hrow
  exact hi.trans_le (Finset.single_le_sum (fun i _ => real_inner_self_nonneg)
    (Finset.mem_univ (0 : Fin 3)))

private theorem gauge_square_smooth : ContDiff ℝ ∞ gaugeSquare :=
  ContDiff.sum (fun i _ => ContDiff.inner ℝ (gauge_row_smooth i) (gauge_row_smooth i))

def hardyWeight (z : SourceCoordinateSlice) : ℝ := Real.sqrt (gaugeSquare z)

theorem hardy_weight_square (z : SourceCoordinateSlice) :
    hardyWeight z ^ 2 = gaugeSquare z := Real.sq_sqrt (gauge_square_nonneg z)

private theorem hardy_weight_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ hardyWeight z.val :=
  gauge_square_smooth.contDiffAt.sqrt (ne_of_gt (gauge_square_pos z))

def localizer (z : SourceCoordinateSlice) : ℝ :=
  volume z ^ 2 / ((1 + volume z) * (1 + volume z * radius z ^ 2) *
    (volume z ^ 2 + gaugeSquare z))

def coefficient (z : SourceCoordinateSlice) : ℝ := hardyWeight z * localizer z * radius z

private theorem denominator_pos (z : physicalChart) :
    0 < (1 + volume z.val) * (1 + volume z.val * radius z.val ^ 2) *
      (volume z.val ^ 2 + gaugeSquare z.val) := by
  have hv := volume_pos z
  have hg := gauge_square_nonneg z.val
  positivity

private theorem localizer_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ localizer z.val := by
  unfold localizer
  apply (volume_smooth.contDiffAt.pow 2).div _ (ne_of_gt (denominator_pos z))
  exact ((contDiffAt_const.add volume_smooth.contDiffAt).mul
    (contDiffAt_const.add (volume_smooth.contDiffAt.mul (radius_smooth.contDiffAt.pow 2)))).mul
      ((volume_smooth.contDiffAt.pow 2).add gauge_square_smooth.contDiffAt)

private theorem coefficient_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ coefficient z.val :=
  ((hardy_weight_smooth z).mul (localizer_smooth z)).mul radius_smooth.contDiffAt

private theorem product_cost (u r w : ℝ) (hu : 0 ≤ u) (hr : 0 ≤ r) (hw : 0 ≤ w) :
    8 * (u ^ 4 * r * w) ≤ (1 + u ^ 2) * (1 + u ^ 2 * r ^ 2) * (u ^ 4 + w ^ 2) := by
  have h1 : 2 * u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u-1)]
  have h2 : 2 * u * r ≤ 1 + u ^ 2 * r ^ 2 := by nlinarith [sq_nonneg (u*r-1)]
  have h3 : 2 * u ^ 2 * w ≤ u ^ 4 + w ^ 2 := by nlinarith [sq_nonneg (u^2-w)]
  calc
    _ = (2*u) * (2*u*r) * (2*u^2*w) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
      (by positivity) (by positivity)

theorem coefficient_bounds (z : physicalChart) :
    0 ≤ coefficient z.val ∧ coefficient z.val ≤ 1/8 := by
  have hv := volume_pos z
  have hr := radius_pos z.val
  have hw : 0 ≤ hardyWeight z.val := Real.sqrt_nonneg _
  have hu : 0 ≤ Real.sqrt (volume z.val) := Real.sqrt_nonneg _
  have hu2 := Real.sq_sqrt hv.le
  have hcost := product_cost _ _ _ hu hr.le hw
  have hu4 : Real.sqrt (volume z.val)^4 = volume z.val^2 := by nlinarith [sq_nonneg (volume z.val)]
  rw [hu2, hu4, hardy_weight_square] at hcost
  have hd := denominator_pos z
  constructor
  · unfold coefficient localizer
    positivity
  · change hardyWeight z.val * (volume z.val^2 /
      ((1+volume z.val)*(1+volume z.val*radius z.val^2)*
        (volume z.val^2+gaugeSquare z.val))) * radius z.val ≤ 1/8
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    rw [←mul_div_assoc, div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_le_one hd).mpr
    nlinarith [hcost]

def fiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (coefficient z : ℂ) • ContinuousLinearMap.id ℂ FockFiber

private theorem fiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ fiber z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (coefficient_smooth z)).smul contDiffAt_const

private theorem fiber_commutes (z : physicalChart) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (fiber z.val) :=
  (Commute.one_right _).smul_right _

private theorem fiber_bound (z : physicalChart) (f : FockFiber) :
    ‖fiber z.val f‖ ≤ (1/8 : ℝ) * ‖f‖ := by
  change ‖(coefficient z.val : ℂ) • f‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coefficient_bounds z).1]
  exact mul_le_mul_of_nonneg_right (coefficient_bounds z).2 (norm_nonneg f)

def multiplier : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension fiber fiber_smooth fiber_commutes (1/8) (by norm_num) fiber_bound

theorem multiplier_norm : ‖multiplier‖ ≤ 1/8 :=
  GaussBoundedMultiplier.extension_norm fiber fiber_smooth fiber_commutes (1/8) (by norm_num) fiber_bound

theorem multiplier_core (f : QuantumTest) :
    multiplier (embed f) = embed (GaussNativeForm.multiply coefficient coefficient_smooth f) :=
  GaussBoundedMultiplier.extension_core fiber fiber_smooth fiber_commutes (1/8) (by norm_num) fiber_bound f

def forcingAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  GaussNativeForm.multiply (fun z => hardyWeight z * localizer z)
    (fun z => (hardy_weight_smooth z).mul (localizer_smooth z))

/-- This multiplier is the physical Hardy weight times the generated localizer. -/
theorem multiplier_inverse_core (f : QuantumTest) :
    multiplier (inverseRadius (embed f)) = embed (forcingAction f) := by
  rw [inverse_core, multiplier_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (coefficient z : ℂ) • ((reciprocal z : ℂ) • f z) =
    ((hardyWeight z * localizer z : ℝ) : ℂ) • f z
  rw [smul_smul, ←Complex.ofReal_mul]
  congr 2
  unfold coefficient reciprocal
  field_simp [(radius_pos z).ne']

end LowEnergy.SourceCornerWeight

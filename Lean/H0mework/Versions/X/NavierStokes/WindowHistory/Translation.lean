import H0mework.Versions.X.NavierStokes.WindowHistory.Current
import H0mework.Versions.X.NavierStokes.PhysicalTranslation.Spectral

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryTranslation
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativePhysicalFourier NativePhysicalGradient NativeSpatialTranslation
open NativeWindowHistoryGNS NativeForwardWindowPairingReadout
noncomputable section

theorem multiplier_sub (wave external : IntegerWavevector) (direction : Coordinate) :
    multiplier (wave-external) direction = multiplier wave direction-multiplier external direction := by
  simp only [multiplier, complexWavevector, Pi.sub_apply, Int.cast_sub]
  push_cast
  ring

theorem multiplier_neg (wave : IntegerWavevector) (direction : Coordinate) :
    multiplier (-wave) direction = -multiplier wave direction := by
  simp only [multiplier, complexWavevector, Pi.neg_apply, Int.cast_neg]
  push_cast
  ring

theorem phase_sub (direction : Coordinate) (displacement : ℝ) (wave external : IntegerWavevector) :
    phase direction displacement (wave-external) =
      phase direction displacement (-external)*phase direction displacement wave := by
  simp only [phase, frequency, Pi.sub_apply, Pi.neg_apply, Int.cast_sub, Int.cast_neg]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def translation (external : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) :
    ScalarSequence →L[ℂ] ScalarSequence :=
  lp.mapCLM 2 (fun wave : IntegerWavevector => phase direction displacement (wave-external) • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one (fun wave => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun value => by
      change ‖phase direction displacement (wave-external)*value‖ ≤ 1*‖value‖
      rw [norm_mul,phase_norm]))

theorem translation_apply (external : IntegerWavevector) (direction : Coordinate) (displacement : ℝ)
    (value : ScalarSequence) (wave : IntegerWavevector) :
    translation external direction displacement value wave = phase direction displacement (wave-external)*value wave := rfl

theorem translation_zero (external : IntegerWavevector) (direction : Coordinate) (value : ScalarSequence) :
    translation external direction 0 value = value := by
  apply lp.ext
  funext wave
  rw [translation_apply,phase_zero,one_mul]

theorem translation_original (external : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) (value : ScalarSequence) :
    translation external direction displacement value =
      phase direction displacement (-external) • NativeSpatialTranslation.translate direction displacement value := by
  apply lp.ext
  funext wave
  change phase direction displacement (wave-external)*value wave =
    phase direction displacement (-external)*(phase direction displacement wave*value wave)
  rw [phase_sub,mul_assoc]

theorem translation_hasDerivAt_zero (external : IntegerWavevector) (direction : Coordinate) (value derivative : ScalarSequence)
    (generated : ∀ wave, derivative wave = multiplier (wave-external) direction*value wave) :
    HasDerivAt (fun displacement => translation external direction displacement value) derivative 0 := by
  let ordinary := derivative+multiplier external direction • value
  have ordinary_read (wave : IntegerWavevector) : ordinary wave = multiplier wave direction*value wave := by
    change derivative wave+multiplier external direction*value wave = _
    rw [generated,multiplier_sub]
    ring
  have actual := (phase_hasDerivAt direction (-external) 0).smul
    (NativeSpatialTranslation.translate_hasDerivAt_zero direction value ordinary ordinary_read)
  simp only [phase_zero,mul_one,NativeSpatialTranslation.translate_zero,one_smul,multiplier_neg] at actual
  have same : ordinary+-multiplier external direction • value = derivative := by
    dsimp [ordinary]
    rw [neg_smul]
    abel
  rw [same] at actual
  simpa only [translation_original] using! actual

theorem quotient_bound (external : IntegerWavevector) (direction : Coordinate) (value derivative : ScalarSequence)
    (generated : ∀ wave, derivative wave = multiplier (wave-external) direction*value wave) (displacement : ℝ) :
    ‖displacement⁻¹ • (translation external direction displacement value-value)‖ ≤ ‖derivative‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  have row : (displacement⁻¹ • (translation external direction displacement value-value) : ScalarSequence) wave =
      ((displacement : ℂ)⁻¹*(phase direction displacement (wave-external)-1))*value wave := by
    change displacement⁻¹ • (phase direction displacement (wave-external)*value wave-value wave) = _
    simp only [Complex.real_smul, Complex.ofReal_inv]
    ring
  rw [row,generated]
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right
    (phase_quotient_bound direction (wave-external) displacement) (norm_nonneg (value wave))

def action (external : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) : HistoryHilbert →L[ℂ] HistoryHilbert :=
  (translation external direction displacement).compLpL 2 averageMeasure

theorem action_ae (external : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) (value : HistoryHilbert) :
    action external direction displacement value =ᵐ[averageMeasure] fun shift => translation external direction displacement (value shift) :=
  (translation external direction displacement).coeFn_compLpL value

theorem action_zero (external : IntegerWavevector) (direction : Coordinate) (value : HistoryHilbert) : action external direction 0 value = value := by
  apply Lp.ext
  filter_upwards [action_ae external direction 0 value] with shift same
  rw [same,translation_zero]

theorem norm_square (value : HistoryHilbert) : ‖value‖^2 = ∫ shift, ‖value shift‖^2 ∂averageMeasure := by
  have same := norm_sq_eq_re_inner (𝕜 := ℂ) value
  rw [L2.inner_def] at same
  simp_rw [inner_self_eq_norm_sq_to_K] at same
  simp only [← map_pow] at same
  rw [integral_ofReal] at same
  exact same

theorem action_hasDerivAt_zero (external : IntegerWavevector) (direction : Coordinate) (value derivative : HistoryHilbert)
    (generated : ∀ᵐ shift ∂averageMeasure, ∀ wave, derivative shift wave = multiplier (wave-external) direction*value shift wave) :
    HasDerivAt (fun displacement => action external direction displacement value) derivative 0 := by
  let error (displacement shift : ℝ) := displacement⁻¹ •
    (translation external direction displacement (value shift)-value shift)-derivative shift
  have measurable (displacement : ℝ) : AEStronglyMeasurable (fun shift => ‖error displacement shift‖^2) averageMeasure :=
    ((((translation external direction displacement).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable value)).sub
      (Lp.aestronglyMeasurable value)).const_smul displacement⁻¹ |>.sub (Lp.aestronglyMeasurable derivative)).norm.pow 2
  have square := (Lp.memLp derivative).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have dominated (displacement : ℝ) : ∀ᵐ shift ∂averageMeasure, ‖‖error displacement shift‖^2‖ ≤ 4*‖derivative shift‖^2 := by
    filter_upwards [generated] with shift actual
    have quotient := quotient_bound external direction (value shift) (derivative shift) actual displacement
    have subtraction : ‖error displacement shift‖ ≤ 2*‖derivative shift‖ :=
      (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (error displacement shift), norm_nonneg (derivative shift)]
  have convergence := tendsto_integral_filter_of_dominated_convergence
    (fun shift => 4*‖derivative shift‖^2) (Eventually.of_forall measurable) (Eventually.of_forall dominated)
    (square.const_mul 4) (by
      filter_upwards [generated] with shift actual
      have point := (translation_hasDerivAt_zero external direction (value shift) (derivative shift) actual).tendsto_slope_zero
      simp only [zero_add,translation_zero] at point
      have zero := (tendsto_iff_norm_sub_tendsto_zero.mp point).pow 2
      simpa only [error,zero_pow (by decide : (2 : ℕ) ≠ 0)] using! zero)
  have identity (displacement : ℝ) :
      ‖displacement⁻¹ • (action external direction displacement value-value)-derivative‖^2 =
        ∫ shift, ‖error displacement shift‖^2 ∂averageMeasure := by
    rw [norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (displacement⁻¹ • (action external direction displacement value-value)) derivative,
      Lp.coeFn_smul displacement⁻¹ (action external direction displacement value-value),
      Lp.coeFn_sub (action external direction displacement value) value, action_ae external direction displacement value]
      with shift subtract scale difference translated
    rw [subtract,Pi.sub_apply,scale,Pi.smul_apply,difference,Pi.sub_apply,translated]
  have squares : Tendsto (fun displacement => ‖displacement⁻¹ • (action external direction displacement value-value)-derivative‖^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simp only [identity]
    simpa only [integral_zero] using! convergence
  have normLimit := Real.continuous_sqrt.continuousAt.tendsto.comp squares
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] at normLimit
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add,action_zero] using! (tendsto_iff_norm_sub_tendsto_zero.mpr normLimit)

theorem phase_relative (direction : Coordinate) (displacement : ℝ) (wave left right : IntegerWavevector) :
    star (phase direction displacement (wave-left))*phase direction displacement (wave-right) =
      phase direction displacement (left-right) := by
  change starRingEnd ℂ (Complex.exp _) * Complex.exp _ = Complex.exp _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [frequency,map_mul,Complex.conj_I,Complex.conj_ofReal,Pi.sub_apply,Int.cast_sub]
  push_cast
  ring

theorem translation_relative_inner (left right : IntegerWavevector) (direction : Coordinate) (displacement : ℝ)
    (first last : ScalarSequence) :
    inner ℂ (translation left direction displacement first) (translation right direction displacement last) =
      phase direction displacement (left-right)*inner ℂ first last := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,← tsum_mul_left]
  apply tsum_congr
  intro wave
  simp only [translation_apply,RCLike.inner_apply,starRingEnd_apply]
  rw [star_mul]
  calc
    _ = (star (phase direction displacement (wave-left))*phase direction displacement (wave-right))*(last wave*star (first wave)) := by ring
    _ = _ := by rw [phase_relative]

theorem action_relative_inner (left right : IntegerWavevector) (direction : Coordinate) (displacement : ℝ)
    (first last : HistoryHilbert) :
    inner ℂ (action left direction displacement first) (action right direction displacement last) =
      phase direction displacement (left-right)*inner ℂ first last := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ shift, inner ℂ (translation left direction displacement (first shift))
        (translation right direction displacement (last shift)) ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [action_ae left direction displacement first,action_ae right direction displacement last] with shift a b
      rw [a,b]
    _ = _ := by simp_rw [translation_relative_inner]; rw [integral_const_mul]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryTranslation

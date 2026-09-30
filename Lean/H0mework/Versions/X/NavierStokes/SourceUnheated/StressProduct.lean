import H0mework.NavierStokes.StressMovingSource.ProductScalar
import H0mework.Versions.X.NavierStokes.StressAction.StressDynamicsBilinear

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedStressProduct
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeHigherTimeJets NativeMovingCriticalProductScalar NativeCompleteStressCarrier
noncomputable section

def amplitude (value : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ℝ :=
  ‖euclideanCoordinateRow (value wave)‖
def density (value : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ℝ :=
  integerWaveNormSq wave * amplitude value wave ^ 2
def gradientMass (value : ComplexVorticityHilbertState) : ℝ := ∑' wave, density value wave
abbrev H1 (value : ComplexVorticityHilbertState) : Prop := Summable (density value)
def constant : ℝ := ∑' wave, weight wave ^ 2

theorem constant_nonnegative : 0 ≤ constant := tsum_nonneg fun _ => sq_nonneg _
theorem density_nonnegative (value : ComplexVorticityHilbertState) (wave : IntegerWavevector) : 0 ≤ density value wave :=
  mul_nonneg (integerWaveNormSq_nonneg _) (sq_nonneg _)

theorem finite_mass (value : ComplexVorticityHilbertState) (zero : value 0 = 0) (F : Finset IntegerWavevector) :
    mass F (fun wave => (weight wave)⁻¹) (amplitude value) = ∑ wave ∈ F, density value wave := by
  apply Finset.sum_congr rfl
  intro wave _
  by_cases atZero : wave = 0
  · subst wave; simp [weight, amplitude, density, zero, euclideanCoordinateRow]
  · simp [weight, atZero, density]

theorem finite_row_bound (F : Finset IntegerWavevector) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖mixedFlux (complexSharpSupportProjection F left) (complexSharpSupportProjection F right) wave output input‖ ≤
      convolution F (amplitude left) (amplitude right) wave := by
  rw [mixedFlux, norm_neg, tsum_eq_sum (s := F) (fun first outside => by
    simp [complexSharpSupportProjection_apply, outside])]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro first inside
  by_cases second : wave - first ∈ F
  · simp only [complexSharpSupportProjection_apply, if_pos inside, if_pos second, norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le (euclideanCoordinateRow (left first)) input)
      (PiLp.norm_apply_le (euclideanCoordinateRow (right (wave - first))) output) (norm_nonneg _)
      (norm_nonneg _)
  · simp [complexSharpSupportProjection_apply, second]

theorem finite_control (F : Finset IntegerWavevector) (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) (leftH1 : H1 left) (rightH1 : H1 right)
    (output input : Coordinate) :
    (∑ wave ∈ F, ‖mixedFlux (complexSharpSupportProjection F left)
      (complexSharpSupportProjection F right) wave output input‖ ^ 2) ≤ constant * gradientMass left * gradientMass right := by
  have summable : Summable (fun wave => ((weight wave)⁻¹)⁻¹ ^ 2) := by simpa using weight_summable
  have paid := convolution_bound F (fun wave => (weight wave)⁻¹) (amplitude left) (amplitude right)
    (fun wave => inv_nonneg.mpr (weight_pos wave).le) (fun wave _ => inv_pos.mpr (weight_pos wave)) summable
  simp only [inv_inv] at paid
  rw [finite_mass left leftZero, finite_mass right rightZero] at paid
  have rows := Finset.sum_le_sum (s := F) fun wave _ =>
    pow_le_pow_left₀ (norm_nonneg _) (finite_row_bound F left right wave output input) 2
  exact (rows.trans paid).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (leftH1.sum_le_tsum F (fun wave _ => density_nonnegative left wave)) constant_nonnegative)
    (rightH1.sum_le_tsum F (fun wave _ => density_nonnegative right wave))
    (Finset.sum_nonneg fun wave _ => density_nonnegative right wave)
    (mul_nonneg constant_nonnegative (tsum_nonneg (density_nonnegative left))))

theorem observed_control (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) (leftH1 : H1 left) (rightH1 : H1 right)
    (observed : Finset IntegerWavevector) (output input : Coordinate) :
    (∑ wave ∈ observed, ‖mixedFlux left right wave output input‖ ^ 2) ≤ constant * gradientMass left * gradientMass right := by
  have limit (wave : IntegerWavevector) : Tendsto
      (fun radius => ‖mixedFlux (complexSharpSupportProjection (integerWaveFrequencyCube radius) left)
        (complexSharpSupportProjection (integerWaveFrequencyCube radius) right) wave output input‖ ^ 2)
      atTop (𝓝 (‖mixedFlux left right wave output input‖ ^ 2)) := by
    have continuous : Continuous (fun pair : ComplexVorticityHilbertState × ComplexVorticityHilbertState =>
        mixedFlux pair.1 pair.2 wave output input) :=
      ((mixedFluxCLM wave output input).continuous.comp continuous_fst).clm_apply continuous_snd
    exact (continuous.tendsto _ |>.comp ((complexSharpSupportProjection_frequencyCube_tendsto left).prodMk_nhds
      (complexSharpSupportProjection_frequencyCube_tendsto right))).norm.pow 2
  apply le_of_tendsto (tendsto_finsetSum observed (fun wave _ => limit wave))
  have included : ∀ᶠ radius in atTop, observed ⊆ integerWaveFrequencyCube radius := by
    exact (eventually_all_finset observed).mpr (fun wave _ => integerWave_eventually_mem_frequencyCube wave)
  filter_upwards [included] with radius subset
  exact (Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => sq_nonneg _)).trans
    (finite_control (integerWaveFrequencyCube radius) left right leftZero rightZero leftH1 rightH1 output input)

theorem tensor_observed_control (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) (leftH1 : H1 left) (rightH1 : H1 right)
    (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed, ‖tensor (mixedFlux left right wave)‖ ^ 2) ≤ 9 * constant * gradientMass left * gradientMass right := by
  simp only [tensor_norm_sq]
  rw [Finset.sum_comm]
  have each (output : Coordinate) :
      (∑ wave ∈ observed, ∑ input : Coordinate, ‖mixedFlux left right wave output input‖ ^ 2) ≤
        ∑ _input : Coordinate, constant * gradientMass left * gradientMass right := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
      observed_control left right leftZero rightZero leftH1 rightH1 observed output input
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ => each output
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    ← mul_assoc, show (3 : ℝ) * 3 = 9 by norm_num] using bound

theorem tensor_summable (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) (leftH1 : H1 left) (rightH1 : H1 right) :
    Summable (fun wave => ‖tensor (mixedFlux left right wave)‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (tensor_observed_control left right leftZero rightZero leftH1 rightH1)

def unweighted (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) (leftH1 : H1 left) (rightH1 : H1 right) : Space :=
  ⟨fun wave => tensor (mixedFlux left right wave), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using tensor_summable left right leftZero rightZero leftH1 rightH1⟩

theorem unweighted_row (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) (leftH1 : H1 left) (rightH1 : H1 right) (wave : IntegerWavevector) :
    unweighted left right leftZero rightZero leftH1 rightH1 wave = tensor (mixedFlux left right wave) := rfl

theorem unweighted_bound (value : ComplexVorticityHilbertState) (zero : value 0 = 0) (regular : H1 value) :
    ‖unweighted value value zero zero regular regular‖ ≤ 3 * Real.sqrt constant * gradientMass value := by
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (density_nonnegative value)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [constant_nonnegative])).mp
  have normed := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (unweighted value value zero zero regular regular)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, unweighted_row] at normed
  rw [normed]
  have paid := (tensor_summable value value zero zero regular regular).tsum_le_of_sum_le
    (tensor_observed_control value value zero zero regular regular)
  convert paid using 1
  simp only [mul_pow, Real.sq_sqrt constant_nonnegative]
  ring


def observe (observed : Finset IntegerWavevector) (stress :
    ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressFourierState) :
    EuclideanSpace ℂ (observed × (Coordinate × Coordinate)) :=
  WithLp.toLp 2 fun entry => stress entry.1.1 entry.2.1 entry.2.2

theorem observe_norm_sq (observed : Finset IntegerWavevector) (stress :
    ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressFourierState) :
    ‖observe observed stress‖ ^ 2 = ∑ wave ∈ observed, ‖tensor (stress wave)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  change (∑ wave : observed, ∑ pair : Coordinate × Coordinate, ‖stress wave.1 pair.1 pair.2‖ ^ 2) = _
  rw [← Finset.sum_attach observed (fun wave => ‖tensor (stress wave)‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro wave _
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem observe_bound (observed : Finset IntegerWavevector) (value : ComplexVorticityHilbertState)
    (zero : value 0 = 0) (regular : H1 value) :
    ‖observe observed (mixedFlux value value)‖ ≤ 3 * Real.sqrt constant * gradientMass value := by
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (density_nonnegative value)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [constant_nonnegative])).mp
  rw [observe_norm_sq]
  convert! tensor_observed_control value value zero zero regular regular observed using 1
  simp only [mul_pow, Real.sq_sqrt constant_nonnegative]
  ring

def observeCLM (observed : Finset IntegerWavevector) :
    Space →L[ℝ] EuclideanSpace ℂ (observed × (Coordinate × Coordinate)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : observed × (Coordinate × Coordinate) => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun entry => readCLM entry.1.1 entry.2.1 entry.2.2)

theorem observeCLM_apply (observed : Finset IntegerWavevector) (value : Space) :
    observeCLM observed value = observe observed (read value) := rfl


theorem projection_H1 (F : Finset IntegerWavevector) (value : ComplexVorticityHilbertState) :
    H1 (complexSharpSupportProjection F value) :=
  summable_of_ne_finset_zero (s := F) fun wave outside => by
    simp [density, amplitude, complexSharpSupportProjection_apply, outside, euclideanCoordinateRow]

theorem projection_zero (F : Finset IntegerWavevector) (value : ComplexVorticityHilbertState) (zero : value 0 = 0) :
    complexSharpSupportProjection F value 0 = 0 := by
  simp only [complexSharpSupportProjection_apply, zero, ite_self]

theorem projection_mass (F : Finset IntegerWavevector) (value : ComplexVorticityHilbertState) :
    gradientMass (complexSharpSupportProjection F value) = ∑ wave ∈ F, density value wave := by
  rw [gradientMass, tsum_eq_sum (s := F) (fun wave outside => by
    simp [density, amplitude, complexSharpSupportProjection_apply, outside, euclideanCoordinateRow])]
  apply Finset.sum_congr rfl
  intro wave inside
  simp only [density, amplitude, complexSharpSupportProjection_apply, if_pos inside]

end
end SaturationMonoid.NavierStokes.NativeUnheatedStressProduct

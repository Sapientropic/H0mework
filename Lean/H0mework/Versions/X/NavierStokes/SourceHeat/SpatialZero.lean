import H0mework.Versions.X.NavierStokes.SourceHeat.WindowZero
import H0mework.Versions.X.NavierStokes.PhysicalJets.CorrectionPhysical
import Mathlib.Analysis.Normed.Group.Tannery

/-! Uniform removal of the existing heat action in every ordinary spatial derivative.
A common Fourier envelope pays the limit for an arbitrary family of the same source. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeHeatSpatialZero
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open NativeFullOrderAction NativeFullOrderSynthesis NativeEndpointVelocityCarrier
open NativeCompleteHeatTransport NativeUnifiedHeatAction
noncomputable section

theorem amplitude_euclidean (value : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    vorticityRowAmplitude value wave = ‖euclideanCoordinateRow (value wave)‖ := by
  change Real.sqrt (complexCoordinateAmplitudeSq (value wave)) = _
  rw [← euclideanCoordinateRow_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem amplitude_heat (nu : Viscosity) (lag : ℝ≥0)
    (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    vorticityRowAmplitude (wholeVelocity (heatCLM nu lag value)) wave =
      finiteStateVorticityHeatMultiplier nu.coeff lag wave * vorticityRowAmplitude (wholeVelocity value) wave := by
  rw [amplitude_euclidean, velocity_heat, amplitude_euclidean]
  change ‖finiteStateVorticityHeatMultiplier nu.coeff lag wave •
    euclideanCoordinateRow (wholeVelocity value wave)‖ = _
  rw [norm_smul, Real.norm_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]

theorem amplitude_error (nu : Viscosity) (lag : ℝ≥0)
    (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    vorticityRowAmplitude (wholeVelocity (heatCLM nu lag value) - wholeVelocity value) wave =
      (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * vorticityRowAmplitude (wholeVelocity value) wave := by
  rw [amplitude_euclidean, amplitude_euclidean]
  have row : (wholeVelocity (heatCLM nu lag value) - wholeVelocity value) wave =
      (finiteStateVorticityHeatMultiplier nu.coeff lag wave - 1) • wholeVelocity value wave := by
    rw [lp.coeFn_sub, Pi.sub_apply, velocity_heat, sub_smul, one_smul]
  rw [row]
  change ‖(finiteStateVorticityHeatMultiplier nu.coeff lag wave - 1) •
    euclideanCoordinateRow (wholeVelocity value wave)‖ = _
  erw [norm_smul, Real.norm_eq_abs, abs_of_nonpos
    (sub_nonpos.mpr (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave))]
  exact congrArg (fun scalar : ℝ => scalar * ‖euclideanCoordinateRow (wholeVelocity value wave)‖)
    (neg_sub _ _)

theorem heat_moments (nu : Viscosity) (lag : ℝ≥0)
    (value : WholeRestartVelocityEndpointState) (order : ℕ)
    (paid : Summable fun wave => frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave) :
    Summable fun wave => frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity (heatCLM nu lag value)) wave := by
  apply paid.of_nonneg_of_le (fun wave => mul_nonneg
    (pow_nonneg (frequencySize_nonneg wave) order) (vorticityRowAmplitude_nonneg _ _))
  intro wave
  erw [amplitude_heat]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (vorticityRowAmplitude_nonneg _ _)
      (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave))
    (pow_nonneg (frequencySize_nonneg wave) order)

theorem error_moments (nu : Viscosity) (lag : ℝ≥0)
    (value : WholeRestartVelocityEndpointState) (order : ℕ)
    (paid : Summable fun wave => frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave) :
    Summable fun wave => frequencySize wave ^ order *
      vorticityRowAmplitude (wholeVelocity (heatCLM nu lag value) - wholeVelocity value) wave := by
  apply paid.of_nonneg_of_le (fun wave => mul_nonneg
    (pow_nonneg (frequencySize_nonneg wave) order) (vorticityRowAmplitude_nonneg _ _))
  intro wave
  erw [amplitude_error]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (vorticityRowAmplitude_nonneg _ _) (sub_le_self 1 (finiteStateVorticityHeatMultiplier_nonneg nu.coeff (lag : ℝ) wave)))
    (pow_nonneg (frequencySize_nonneg wave) order)

def errorBudget (nu : Viscosity) (lag : ℝ≥0) (order : ℕ) (envelope : IntegerWavevector → ℝ) : ℝ :=
  (2 * Real.pi) ^ order * ∑' wave,
    (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * envelope wave

theorem jet_error_bound (nu : Viscosity) (lag : ℝ≥0)
    (value : WholeRestartVelocityEndpointState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave)
    (order : ℕ) (envelope : IntegerWavevector → ℝ) (summable : Summable envelope)
    (bound : ∀ wave, frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave ≤ envelope wave)
    (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (spatialField (wholeVelocity (heatCLM nu lag value))) point -
      iteratedFDeriv ℝ order (spatialField (wholeVelocity value)) point‖ ≤ errorBudget nu lag order envelope := by
  have allHeat := fun n => heat_moments nu lag value n (moments n)
  have allError := fun n => error_moments nu lag value n (moments n)
  have smooth (u : ComplexVorticityHilbertState)
      (hp : ∀ n : ℕ, Summable fun wave => frequencySize wave ^ n * vorticityRowAmplitude u wave) :
      ContDiff ℝ order (spatialField u) := (spatialField_smooth u hp).of_le
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  rw [← iteratedFDeriv_sub_apply (smooth _ allHeat).contDiffAt (smooth _ moments).contDiffAt,
    ← NativeCorrectionPhysical.spatialField_sub _ _
      (by simpa only [pow_zero, one_mul, amplitude] using allHeat 0)
      (by simpa only [pow_zero, one_mul, amplitude] using moments 0)]
  refine (spatialField_iterated_bound _ allError order point).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have nonnegative (wave : IntegerWavevector) : 0 ≤ envelope wave :=
    (mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order) (vorticityRowAmplitude_nonneg _ _)).trans (bound wave)
  have dominated : Summable fun wave =>
      (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * envelope wave := by
    apply summable.of_nonneg_of_le (fun wave => mul_nonneg
      (sub_nonneg.mpr (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave)) (nonnegative wave))
    intro wave
    exact mul_le_of_le_one_left (nonnegative wave) (sub_le_self 1 (finiteStateVorticityHeatMultiplier_nonneg nu.coeff (lag : ℝ) wave))
  apply (allError order).tsum_le_tsum _ dominated
  intro wave
  erw [amplitude_error]
  calc _ = (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) *
        (frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bound wave)
      (sub_nonneg.mpr (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave))

theorem errorBudget_zero (nu : Viscosity) (order : ℕ) (envelope : IntegerWavevector → ℝ)
    (summable : Summable envelope) (nonnegative : ∀ wave, 0 ≤ envelope wave) :
    Tendsto (fun lag : ℝ≥0 => errorBudget nu lag order envelope) (𝓝 0) (𝓝 0) := by
  have limit := tendsto_tsum_of_dominated_convergence (bound := envelope) (g := fun _ => (0 : ℝ))
    (𝓕 := 𝓝 (0 : ℝ≥0))
    (f := fun lag wave => (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * envelope wave) summable
    (fun wave => ?_) (Eventually.of_forall fun lag wave => ?_)
  · simpa only [errorBudget, tsum_zero, mul_zero] using limit.const_mul ((2 * Real.pi) ^ order)
  · have rowContinuous : Continuous (fun lag : ℝ≥0 =>
        (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * envelope wave) := by
      unfold finiteStateVorticityHeatMultiplier
      fun_prop
    simpa only [NNReal.coe_zero, finiteStateVorticityHeatMultiplier, mul_zero, neg_zero,
      Real.exp_zero, sub_self, zero_mul] using rowContinuous.tendsto (0 : ℝ≥0)
  · erw [Real.norm_of_nonneg (mul_nonneg
      (sub_nonneg.mpr (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave)) (nonnegative wave))]
    exact mul_le_of_le_one_left (nonnegative wave) (sub_le_self 1 (finiteStateVorticityHeatMultiplier_nonneg nu.coeff (lag : ℝ) wave))

theorem family_jets_uniform_zero {Parameter : Type*} (nu : Viscosity)
    (family : Parameter → WholeRestartVelocityEndpointState)
    (envelope : ℕ → IntegerWavevector → ℝ)
    (summable : ∀ order, Summable (envelope order))
    (nonnegative : ∀ order wave, 0 ≤ envelope order wave)
    (bounded : ∀ parameter order wave, frequencySize wave ^ order *
      vorticityRowAmplitude (wholeVelocity (family parameter)) wave ≤ envelope order wave)
    (order : ℕ) :
    TendstoUniformly (fun lag : ℝ≥0 => fun pair : Parameter × PhysicalSpace =>
      iteratedFDeriv ℝ order (spatialField (wholeVelocity (heatCLM nu lag (family pair.1)))) pair.2)
      (fun pair => iteratedFDeriv ℝ order (spatialField (wholeVelocity (family pair.1))) pair.2) (𝓝 0) := by
  have moments (parameter : Parameter) (rank : ℕ) :
      Summable fun wave => frequencySize wave ^ rank *
        vorticityRowAmplitude (wholeVelocity (family parameter)) wave :=
    (summable rank).of_nonneg_of_le (fun wave => mul_nonneg
      (pow_nonneg (frequencySize_nonneg wave) rank) (vorticityRowAmplitude_nonneg _ _)) (bounded parameter rank)
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon positive
  filter_upwards [(errorBudget_zero nu order (envelope order) (summable order)
    (nonnegative order)).eventually (gt_mem_nhds positive)] with lag small
  intro pair
  rw [dist_comm, dist_eq_norm]
  exact (jet_error_bound nu lag (family pair.1) (moments pair.1) order
    (envelope order) (summable order) (bounded pair.1 order) pair.2).trans_lt small

theorem jet_bound (nu : Viscosity) (lag : ℝ≥0) (value : WholeRestartVelocityEndpointState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave)
    (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (spatialField (wholeVelocity (heatCLM nu lag value))) point‖ ≤
      (2 * Real.pi) ^ order * ∑' wave, frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity value) wave := by
  refine (spatialField_iterated_bound _ (fun n => heat_moments nu lag value n (moments n)) order point).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (heat_moments nu lag value order (moments order)).tsum_le_tsum _ (moments order)
  intro wave
  change frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity (heatCLM nu lag value)) wave ≤ _
  rw [amplitude_heat]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (vorticityRowAmplitude_nonneg _ _)
      (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave))
    (pow_nonneg (frequencySize_nonneg wave) order)

end
end SaturationMonoid.NavierStokes.NativeHeatSpatialZero

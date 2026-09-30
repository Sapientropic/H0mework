import H0mework.NavierStokes.WindowSourceSobolev.UniformTail
import H0mework.NavierStokes.PhysicalReadout.Gradient
import H0mework.NavierStokes.SourceWindow.PairingReadout

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowCompleteDensityCoefficient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressCarrier NativePhysicalFourier NativePhysicalGradient
open NativeWindowSobolevStress (quarter quarter_nonnegative quarter_positive quarter_sq)
noncomputable section

def traceCLM : Tensor →L[ℂ] ℂ := ∑ i : Coordinate, PiLp.proj (𝕜 := ℂ) 2 (fun _ : Coordinate × Coordinate => ℂ) (i,i)

theorem trace_bound (value : Tensor) : ‖traceCLM value‖ ≤ 3*‖value‖ := by
  change ‖∑ i : Coordinate, value (i,i)‖ ≤ _
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le value (i,i))).trans_eq (by simp))

def factor (direction : Coordinate) (wave : IntegerWavevector) : ℂ :=
  -multiplier wave direction/(8*(quarter wave : ℂ)^2)

theorem multiplier_bound (direction : Coordinate) (wave : IntegerWavevector) :
    ‖multiplier wave direction‖ ≤ (2*Real.pi)*quarter wave^2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [quarter_positive wave])).mp
  rw [multiplier_norm_sq,quarter_sq]
  conv_rhs => rw [mul_pow,Real.sq_sqrt (by positivity [integerWaveNormSq_nonneg wave])]
  have component : (wave direction : ℝ)^2 ≤ integerWaveNormSq wave :=
    Finset.single_le_sum (fun i _ => sq_nonneg (wave i : ℝ)) (Finset.mem_univ direction)
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

theorem factor_bound (direction : Coordinate) (wave : IntegerWavevector) : ‖factor direction wave‖ ≤ (2*Real.pi)/8 := by
  rw [factor,norm_div,norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (quarter_nonnegative wave)]
  norm_num only [show ‖(8 : ℂ)‖ = (8 : ℝ) by norm_num]
  apply (div_le_iff₀ (by positivity [quarter_positive wave] : 0 < 8*quarter wave^2)).mpr
  exact (multiplier_bound direction wave).trans_eq (by ring)

def cap : ℝ := 3*(2*Real.pi)/8
theorem cap_positive : 0 < cap := by unfold cap; positivity

def rowMap (direction : Coordinate) (wave : IntegerWavevector) : Tensor →L[ℂ] ℂ := factor direction wave • traceCLM

theorem rowMap_bound (direction : Coordinate) (wave : IntegerWavevector) : ‖rowMap direction wave‖ ≤ cap := by
  apply ContinuousLinearMap.opNorm_le_bound _ cap_positive.le
  intro value
  change ‖factor direction wave*traceCLM value‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul (factor_bound direction wave) (trace_bound value) (norm_nonneg _)
    (by positivity)).trans_eq (by unfold cap; ring)

def coefficientMap (direction : Coordinate) : Space →L[ℂ] ScalarSequence :=
  lp.mapCLM 2 (rowMap direction) cap_positive.le (rowMap_bound direction)

theorem coefficientMap_row (direction : Coordinate) (value : Space) (wave : IntegerWavevector) :
    coefficientMap direction value wave = factor direction wave*∑ i : Coordinate, value wave (i,i) := rfl

theorem coefficientMap_bound (direction : Coordinate) (value : Space) : ‖coefficientMap direction value‖ ≤ cap*‖value‖ :=
  ((coefficientMap direction).le_opNorm value).trans (mul_le_mul_of_nonneg_right
    (lp.norm_mapCLM_le 2 (rowMap direction) cap_positive.le (rowMap_bound direction)) (norm_nonneg _))

def high (F : Finset IntegerWavevector) (value : ScalarSequence) : ScalarSequence :=
  ⟨fun wave => if wave ∈ F then 0 else value wave, (lp.memℓp value).mono' fun wave => by split_ifs <;> simp⟩

theorem map_high (direction : Coordinate) (F : Finset IntegerWavevector) (value : Space) :
    coefficientMap direction (NativeWindowSobolevUniformTail.high F value) = high F (coefficientMap direction value) := by
  apply lp.ext
  funext wave
  simp only [coefficientMap_row,NativeWindowSobolevUniformTail.high,high]
  split_ifs <;> simp

variable {nu : Viscosity}

def coefficient (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (direction : Coordinate) : ScalarSequence := coefficientMap direction (NativeWindowSobolevStress.state seed order time valid)

theorem source_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (direction : Coordinate) (wave : IntegerWavevector) :
    (quarter wave : ℂ)*coefficient seed order time valid direction wave =
      -multiplier wave direction*(∑ i : Coordinate, read (NativeForwardWindowJets.jet seed order time).snd wave i i)/8 := by
  rw [coefficient,coefficientMap_row]
  simp only [NativeWindowSobolevStress.state_row,Complex.real_smul,← Finset.mul_sum]
  have positive : (quarter wave : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (quarter_positive wave).ne'
  unfold factor
  field_simp

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem baseline_derivative (direction : Coordinate) (wave : IntegerWavevector) :
    multiplier wave direction*NativePairedCurrentFourier.baseline wave = 0 := by
  have orthogonal := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 3))) wave 0
  have mean : (∫ point : Torus, UnitAddTorus.mFourier (-wave) point) = if wave = 0 then (1 : ℂ) else 0 := by
    simpa [ContinuousMap.inner_toLp,← UnitAddTorus.mFourier_neg,UnitAddTorus.mFourier_zero] using orthogonal
  unfold NativePairedCurrentFourier.baseline UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul,integral_mul_const,mean]
  by_cases zero : wave=0 <;> simp [zero,multiplier,complexWavevector]

theorem current_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (direction : Coordinate) (wave : IntegerWavevector) :
    (quarter wave : ℂ)*coefficient seed 0 time valid direction wave = multiplier wave direction*
      NativePairedCurrentFourier.coefficient (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
        (read (NativeForwardWindowSource.source seed time).snd) 0 wave := by
  rw [source_row]
  change -multiplier wave direction*(∑ i : Coordinate, read (NativeForwardWindowSource.source seed time).snd wave i i)/8 =
    multiplier wave direction*(NativePairedCurrentFourier.baseline wave-(∑ i : Coordinate, read (NativeForwardWindowSource.source seed time).snd wave i i)/8)
  rw [mul_sub,baseline_derivative]
  ring

theorem residual_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (direction : Coordinate) (wave : IntegerWavevector) :
    coefficient seed order time valid direction wave = factor direction wave*∑ i : Coordinate, quarter wave •
      (NativeUnheatedWindowResidual.coefficients seed order time wave i i+
        NativeHigherTimeJets.mixedTimeSum (NativeUnheatedWindowResidual.velocity seed) (NativeUnheatedWindowResidual.velocity seed)
          order time wave i i) := by
  rw [coefficient,coefficientMap_row]
  simp only [NativeWindowSobolevStress.state_residual_split]

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 ≤ time) (before : time ≤ horizon) (direction : Coordinate) :
    ‖coefficient seed order time valid direction‖ ≤ cap*|NativeWindowSobolevStress.budget seed order horizon| := by
  apply (coefficientMap_bound direction _).trans
  apply mul_le_mul_of_nonneg_left _ cap_positive.le
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs]
  have actual := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (NativeWindowSobolevStress.state seed order time valid)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,NativeWindowSobolevStress.state,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,quarter_sq] at actual
  change ‖NativeWindowSobolevStress.state seed order time valid‖^2 = _ at actual
  rw [actual]
  exact NativeWindowSobolevStress.moment_bound_on_interval seed order time horizon valid before

theorem coefficient_next (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (direction : Coordinate) :
    coefficient seed order (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) direction =
      coefficient step.1 order time (by linarith) direction := by
  rw [coefficient,coefficient,NativeWindowSobolevStress.state_next seed order step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowCompleteDensityCoefficient

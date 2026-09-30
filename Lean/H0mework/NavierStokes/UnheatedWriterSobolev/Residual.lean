import H0mework.NavierStokes.UnheatedWriterSobolev.Product
import H0mework.NavierStokes.UnheatedWriterSobolev.Velocity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowSobolevResidual
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeEndpointVelocityCarrier NativeCompleteStressCarrier NativeCompleteStressAction
open NativeForwardWindowJets NativeForwardWindowEvolution NativeHigherTimeJets NativeUnheatedStressProduct
open NativeUnheatedWindowResidual (velocity coefficients)
noncomputable section
variable {nu : Viscosity}

theorem velocity_mass_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time ≤ horizon) :
    gradientMass (velocity seed order time) ≤ NativeWindowSobolevVelocity.budget seed order horizon := by
  apply (Summable.tsum_le_tsum (fun wave => ?_)
    (NativeUnheatedWindowResidual.velocity_H1 seed order time valid.le)
    (NativeWindowSobolevVelocity.whole_summable seed order time valid)).trans
      (NativeWindowSobolevVelocity.whole_bound_on_interval seed order time horizon valid before)
  change integerWaveNormSq wave*‖euclideanCoordinateRow (wholeVelocity (velocityJet seed order time) wave)‖^2 ≤
    (1+integerWaveNormSq wave)*Real.sqrt (1+integerWaveNormSq wave)*
      complexCoordinateAmplitudeSq (wholeVelocity (velocityJet seed order time) wave)
  rw [← euclideanCoordinateRow_norm_sq]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have root : 1 ≤ Real.sqrt (1+integerWaveNormSq wave) :=
    Real.le_sqrt_of_sq_le (by nlinarith [integerWaveNormSq_nonneg wave])
  have scaled := mul_le_mul_of_nonneg_left root
    (show 0 ≤ 1+integerWaveNormSq wave by positivity [integerWaveNormSq_nonneg wave])
  nlinarith

def mixedState (seed : GeneratedWholeRestartCurrent nu) (first last : ℕ) (time : ℝ) (valid : -1 < time) : Space :=
  NativeWindowSobolevProduct.state (velocity seed first time) (velocity seed last time)
    (wholeVelocity_zero _) (wholeVelocity_zero _)
    (NativeUnheatedWindowResidual.velocity_H1 seed first time valid.le)
    (NativeUnheatedWindowResidual.velocity_H1 seed last time valid.le)

theorem mixedState_row (seed : GeneratedWholeRestartCurrent nu) (first last : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    mixedState seed first last time valid wave (output,input) = NativeWindowSobolevStress.quarter wave •
      mixedFlux (velocity seed first time) (velocity seed last time) wave output input := rfl

theorem mixedState_bound (seed : GeneratedWholeRestartCurrent nu) (first last : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time ≤ horizon) :
    ‖mixedState seed first last time valid‖ ≤ 6*Real.sqrt NativeUnheatedRieszKernel.constant*
      (NativeWindowSobolevVelocity.budget seed first horizon+NativeWindowSobolevVelocity.budget seed last horizon) := by
  apply (NativeWindowSobolevProduct.state_bound _ _ _ _ _ _).trans
  exact mul_le_mul_of_nonneg_left (add_le_add
    (velocity_mass_on_interval seed first time horizon valid before)
    (velocity_mass_on_interval seed last time horizon valid before)) (by positivity)

def state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) : Space :=
  NativeWindowSobolevStress.state seed order time valid.le-
    ∑ rank ∈ Finset.range (order+1), (order.choose rank : ℝ) • mixedState seed rank (order-rank) time valid

theorem state_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    state seed order time valid wave (output,input) =
      NativeWindowSobolevStress.quarter wave • coefficients seed order time wave output input := by
  let evaluate : Space →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate × Coordinate => ℂ) (output,input)).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave)
  change evaluate (state seed order time valid) = _
  rw [state,map_sub,map_sum]
  simp only [map_smul]
  change NativeWindowSobolevStress.quarter wave • NativeUnheatedWindowStress.stress seed order time wave output input-
    (∑ rank ∈ Finset.range (order+1), (order.choose rank : ℝ) •
      (NativeWindowSobolevStress.quarter wave • mixedFlux (velocity seed rank time) (velocity seed (order-rank) time) wave output input)) = _
  simp only [NativeUnheatedWindowResidual.coefficients,Pi.sub_apply,mixedTimeSum,smul_sub,Finset.smul_sum,
    Complex.real_smul,Complex.ofReal_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro rank _
  ring

theorem state_tensor (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : IntegerWavevector) : state seed order time valid wave =
      NativeWindowSobolevStress.quarter wave • tensor (coefficients seed order time wave) := by
  ext entry
  exact state_row seed order time valid wave entry.1 entry.2

theorem restore_state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    (NativeWindowSobolevStress.quarter wave)⁻¹ • state seed order time valid wave (output,input) =
      iteratedDeriv order (fun actual => NativeCompleteCorrectionRead.residual
        (NativeForwardWindowSource.source seed actual) wave output input) time := by
  rw [state_row,inv_smul_smul₀ (NativeWindowSobolevStress.quarter_positive wave).ne',
    NativeUnheatedWindowResidual.coefficients_iteratedDeriv]

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  NativeWindowSobolevStress.budget seed order horizon+∑ rank ∈ Finset.range (order+1),
    (order.choose rank : ℝ)*(6*Real.sqrt NativeUnheatedRieszKernel.constant*
      (NativeWindowSobolevVelocity.budget seed rank horizon+NativeWindowSobolevVelocity.budget seed (order-rank) horizon))

theorem stress_norm_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time ≤ horizon) :
    ‖NativeWindowSobolevStress.state seed order time valid.le‖ ≤ NativeWindowSobolevStress.budget seed order horizon := by
  have nonnegative : 0 ≤ NativeWindowSobolevStress.budget seed order horizon :=
    (norm_nonneg _).trans (NativeWindowSobolevStress.observed_bound_on_interval seed order time horizon valid.le before ∅)
  apply (sq_le_sq₀ (norm_nonneg _) nonnegative).mp
  have original := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (NativeWindowSobolevStress.state seed order time valid.le)
  have row (wave : IntegerWavevector) : NativeWindowSobolevStress.state seed order time valid.le wave =
      NativeWindowSobolevStress.quarter wave • tensor (NativeUnheatedWindowStress.stress seed order time wave) := rfl
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,row,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,NativeWindowSobolevStress.quarter_sq] at original
  rw [original]
  exact NativeWindowSobolevStress.moment_bound_on_interval seed order time horizon valid.le before

theorem state_bound_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time ≤ horizon) : ‖state seed order time valid‖ ≤ budget seed order horizon := by
  apply (norm_sub_le _ _).trans
  apply add_le_add (stress_norm_on_interval seed order time horizon valid before)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro rank _
  rw [norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (mixedState_bound seed rank (order-rank) time horizon valid before) (Nat.cast_nonneg _)

theorem summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    Summable (fun wave => Real.sqrt (1+integerWaveNormSq wave)*‖tensor (coefficients seed order time wave)‖^2) := by
  have actual := (lp.memℓp (state seed order time valid)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,state_tensor,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,NativeWindowSobolevStress.quarter_sq] using actual

theorem moment_bound_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time ≤ horizon) :
    (∑' wave, Real.sqrt (1+integerWaveNormSq wave)*‖tensor (coefficients seed order time wave)‖^2) ≤ budget seed order horizon^2 := by
  have original := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (state seed order time valid)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,state_tensor,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,NativeWindowSobolevStress.quarter_sq] at original
  rw [← original]
  exact pow_le_pow_left₀ (norm_nonneg _) (state_bound_on_interval seed order time horizon valid before) 2

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem state_next (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    state seed order (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) =
      state response.1 order time (by linarith) := by
  have next (rank : ℕ) := jet_next seed rank response generated time nonnegative
  have same : coefficients seed order (response.2.clockAdvance+time) = coefficients response.1 order time := by
    funext wave output input
    simp only [NativeUnheatedWindowResidual.coefficients,Pi.sub_apply,mixedTimeSum,
      NativeUnheatedWindowStress.stress,NativeUnheatedWindowResidual.velocity,velocityJet,next]
  apply lp.ext
  funext wave
  rw [state_tensor,state_tensor,same]

end
end SaturationMonoid.NavierStokes.NativeWindowSobolevResidual

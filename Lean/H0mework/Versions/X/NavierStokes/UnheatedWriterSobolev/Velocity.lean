import H0mework.Versions.X.NavierStokes.UnheatedWriterSobolev.Stress

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowSobolevVelocity
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier NativeTimeJetCarrier
open NativeFullOrderStress
open NativeForwardWindowEvolution NativeForwardWindowJets
noncomputable section
variable {nu : Viscosity}

def multiplier (wave : IntegerWavevector) : ℝ :=
  Real.sqrt (1+integerWaveNormSq wave)*NativeWindowSobolevStress.quarter wave

theorem multiplier_sq (wave : IntegerWavevector) : multiplier wave^2 =
    (1+integerWaveNormSq wave)*Real.sqrt (1+integerWaveNormSq wave) := by
  rw [multiplier,mul_pow,NativeWindowSobolevStress.quarter_sq,Real.sq_sqrt]
  positivity [integerWaveNormSq_nonneg wave]

theorem projected_square (stress : NativeFluidStressFourierState) (wave : NonzeroIntegerWavevector) :
    ‖euclideanCLM (projectedDivergenceCLM wave.1 (stress wave.1))‖^2 ≤
      (2*Real.pi)^2*integerWaveNormSq wave.1*‖tensor (stress wave.1)‖^2 := by
  have actual := (transverseProjection_amplitudeSq_le wave.1 wave.2
    (nativeFluidStressDivergenceCoefficient stress wave.1)).trans (divergence_amplitude_le stress wave.1)
  change ‖euclideanCoordinateRow (transverseProjection wave.1 (nativeFluidStressDivergenceCoefficient stress wave.1))‖^2 ≤ _
  rw [euclideanCoordinateRow_norm_sq]
  have same : (∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (stress wave.1 output input)) =
      ‖tensor (stress wave.1)‖^2 := by
    rw [tensor_norm_sq]
    simp only [Complex.normSq_eq_norm_sq]
  rw [same] at actual
  exact actual

theorem momentum_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : NonzeroIntegerWavevector) :
    (nu.coeff*(2*Real.pi)^2*integerWaveNormSq wave.1) • velocityJet seed order time wave =
      euclideanCLM (projectedDivergenceCLM wave.1 (NativeUnheatedWindowStress.stress seed order time wave.1))-
        velocityJet seed (order+1) time wave := by
  have actual := congrArg (fun value : WholeRestartVelocityEndpointState => integerWaveNormSq wave.1^2 • value wave)
    (source_physical_word seed order time valid)
  rw [NativeNegativeFourMomentum.embed_reconstruct,NativeCompleteActionOperator.momentum_complete_row] at actual
  change velocityJet seed (order+1) time wave = integerWaveNormSq wave.1^2 •
    (NativeNegativeFourMomentum.weight wave.1 • euclideanCoordinateRow (NativeCompleteAction.momentum nu (jet seed order time) wave.1)) at actual
  rw [NativeNegativeFourMomentum.weight,smul_smul,← mul_pow,mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne',one_pow,one_smul] at actual
  change velocityJet seed (order+1) time wave = euclideanCLM
    (projectedDivergenceCLM wave.1 (NativeUnheatedWindowStress.stress seed order time wave.1)-
      (nu.coeff*integerWaveViscousMultiplier wave.1) • wholeVelocity (velocityJet seed order time) wave.1) at actual
  rw [map_sub,map_smul] at actual
  have row : euclideanCLM (wholeVelocity (velocityJet seed order time) wave.1) = velocityJet seed order time wave := by
    ext coordinate
    exact wholeVelocity_nonzero _ wave coordinate
  rw [row,integerWaveViscousMultiplier] at actual
  rw [actual]
  module

private theorem ratio_bound {frequency : ℝ} (large : 1 ≤ frequency) :
    Real.sqrt (1+frequency)/frequency ≤ 2 := by
  have positive : 0 < frequency := by linarith
  apply (div_le_iff₀ positive).mpr
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

theorem row_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : NonzeroIntegerWavevector) :
    (1+integerWaveNormSq wave.1)*Real.sqrt (1+integerWaveNormSq wave.1)*‖velocityJet seed order time wave‖^2 ≤
      (nu.coeff*(2*Real.pi)^2)^(-2 : ℤ)*
        (4*(2*Real.pi)^2*Real.sqrt (1+integerWaveNormSq wave.1)*
          ‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+
            8*‖velocityJet seed (order+1) time wave‖^2) := by
  let c := nu.coeff*(2*Real.pi)^2
  let f := integerWaveNormSq wave.1
  let h := Real.sqrt (1+f)
  have cpos : 0 < c := by dsimp [c]; positivity [nu.coeff_pos]
  have fpos : 0 < f := integerWaveNormSq_pos wave.2
  have flarge : 1 ≤ f := one_le_integerWaveNormSq wave.1 wave.2
  have h0 : 0 ≤ h := Real.sqrt_nonneg _
  have physical := momentum_row seed order time valid wave
  let d := euclideanCLM (projectedDivergenceCLM wave.1 (NativeUnheatedWindowStress.stress seed order time wave.1))
  let r := velocityJet seed (order+1) time wave
  have energy : c^2*f^2*‖velocityJet seed order time wave‖^2 ≤ 2*‖d‖^2+2*‖r‖^2 := by
    have triangle := norm_sub_le d r
    have normed : ‖(c*f) • velocityJet seed order time wave‖=‖d-r‖ := congrArg norm physical
    rw [norm_smul,Real.norm_of_nonneg (mul_nonneg cpos.le fpos.le)] at normed
    have square := pow_le_pow_left₀ (norm_nonneg _) triangle 2
    rw [← normed,mul_pow,mul_pow] at square
    nlinarith [sq_nonneg (‖d‖-‖r‖)]
  have forcing := projected_square (NativeUnheatedWindowStress.stress seed order time) wave
  have total : c^2*f^2*‖velocityJet seed order time wave‖^2 ≤
      2*(2*Real.pi)^2*f*‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+2*‖r‖^2 := by
    dsimp only [d] at energy
    nlinarith
  have compensated : c^2*((1+f)*h*‖velocityJet seed order time wave‖^2) ≤
      4*(2*Real.pi)^2*h*‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+8*‖r‖^2 := by
    calc
      _ ≤ 2*(c^2*f*h*‖velocityJet seed order time wave‖^2) := by
        have scale := mul_nonneg (mul_nonneg (sq_nonneg c) h0) (sq_nonneg ‖velocityJet seed order time wave‖)
        nlinarith
      _ = (2*h/f)*(c^2*f^2*‖velocityJet seed order time wave‖^2) := by field_simp
      _ ≤ (2*h/f)*(2*(2*Real.pi)^2*f*‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+2*‖r‖^2) :=
        mul_le_mul_of_nonneg_left total (by positivity)
      _ = 4*(2*Real.pi)^2*h*‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+4*(h/f)*‖r‖^2 := by field_simp; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (ratio_bound flarge) (sq_nonneg ‖r‖)]
  have divided : (1+f)*h*‖velocityJet seed order time wave‖^2 ≤
      (4*(2*Real.pi)^2*h*‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+8*‖r‖^2)/c^2 :=
    (le_div_iff₀ (sq_pos_of_pos cpos)).mpr (by nlinarith [compensated])
  simpa only [c,f,h,r,zpow_neg,zpow_ofNat,div_eq_mul_inv,mul_comm] using divided

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : ℝ :=
  (nu.coeff*(2*Real.pi)^2)^(-2 : ℤ)*
    (4*(2*Real.pi)^2*NativeWindowSobolevStress.budget seed order time^2+8*NativeForwardWindowJets.budget seed (order+1)^2)

theorem weighted_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    Summable (fun wave : NonzeroIntegerWavevector =>
      (1+integerWaveNormSq wave.1)*Real.sqrt (1+integerWaveNormSq wave.1)*‖velocityJet seed order time wave‖^2) := by
  have stress := (NativeWindowSobolevStress.stress_summable seed order time valid.le).subtype (fun wave => wave ≠ 0)
  have rate : Summable (fun wave : NonzeroIntegerWavevector => ‖velocityJet seed (order+1) time wave‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp (velocityJet seed (order+1) time)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  exact (((stress.mul_left (4*(2*Real.pi)^2)).add (rate.mul_left 8)).mul_left
    ((nu.coeff*(2*Real.pi)^2)^(-2 : ℤ))).of_nonneg_of_le
      (fun wave => by positivity [integerWaveNormSq_nonneg wave.1]) (fun wave => by
        simpa only [mul_assoc,Function.comp_apply] using row_bound seed order time valid wave)

theorem moment_bound_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ) (valid : -1 < time) (before : time ≤ horizon) :
    (∑' wave : NonzeroIntegerWavevector,
      (1+integerWaveNormSq wave.1)*Real.sqrt (1+integerWaveNormSq wave.1)*‖velocityJet seed order time wave‖^2) ≤
        budget seed order horizon := by
  have stressFull := NativeWindowSobolevStress.stress_summable seed order time valid.le
  have stress : Summable (fun wave : NonzeroIntegerWavevector => Real.sqrt (1+integerWaveNormSq wave.1)*
      ‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2) := by
    simpa only [Function.comp_def] using! stressFull.subtype (fun wave => wave ≠ 0)
  have stressBound := (stressFull.tsum_subtype_le _ {wave | wave ≠ 0}
    (fun wave => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).trans
      (NativeWindowSobolevStress.moment_bound_on_interval seed order time horizon valid.le before)
  have rate : Summable (fun wave : NonzeroIntegerWavevector => ‖velocityJet seed (order+1) time wave‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp (velocityJet seed (order+1) time)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have rateBound : (∑' wave, ‖velocityJet seed (order+1) time wave‖^2) ≤ NativeForwardWindowJets.budget seed (order+1)^2 := by
    have original := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (velocityJet seed (order+1) time)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at original
    rw [← original]
    exact pow_le_pow_left₀ (norm_nonneg _) (velocityJet_bound seed (order+1) time) 2
  apply (weighted_summable seed order time valid).tsum_le_of_sum_le
  intro F
  have stressFinite : (∑ wave ∈ F, Real.sqrt (1+integerWaveNormSq wave.1)*
      ‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2) ≤ NativeWindowSobolevStress.budget seed order horizon^2 := by
    exact (stress.sum_le_tsum F
      (fun wave _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).trans stressBound
  have rateFinite := (rate.sum_le_tsum F (fun wave _ => sq_nonneg _)).trans rateBound
  calc
    _ ≤ ∑ wave ∈ F, (nu.coeff*(2*Real.pi)^2)^(-2 : ℤ)*
        (4*(2*Real.pi)^2*Real.sqrt (1+integerWaveNormSq wave.1)*
          ‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2+
            8*‖velocityJet seed (order+1) time wave‖^2) :=
      Finset.sum_le_sum fun wave _ => row_bound seed order time valid wave
    _ = (nu.coeff*(2*Real.pi)^2)^(-2 : ℤ)*
        (4*(2*Real.pi)^2*(∑ wave ∈ F, Real.sqrt (1+integerWaveNormSq wave.1)*
          ‖tensor (NativeUnheatedWindowStress.stress seed order time wave.1)‖^2)+
            8*∑ wave ∈ F, ‖velocityJet seed (order+1) time wave‖^2) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left stressFinite (by positivity))
      (mul_le_mul_of_nonneg_left rateFinite (by norm_num))) (by positivity [nu.coeff_pos])

theorem moment_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    (∑' wave : NonzeroIntegerWavevector,
      (1+integerWaveNormSq wave.1)*Real.sqrt (1+integerWaveNormSq wave.1)*‖velocityJet seed order time wave‖^2) ≤
        budget seed order time := moment_bound_on_interval seed order time time valid le_rfl

def state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    WholeRestartVelocityEndpointState :=
  ⟨fun wave => multiplier wave.1 • velocityJet seed order time wave, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,multiplier_sq]
      using weighted_summable seed order time valid⟩

theorem state_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : NonzeroIntegerWavevector) :
    state seed order time valid wave = multiplier wave.1 • velocityJet seed order time wave := rfl

theorem state_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    ‖state seed order time valid‖^2 ≤ budget seed order time := by
  have original := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (state seed order time valid)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,state_row,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,multiplier_sq] at original
  rw [original]
  exact moment_bound seed order time valid

def wholeDensity (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (wave : IntegerWavevector) : ℝ :=
  (1+integerWaveNormSq wave)*Real.sqrt (1+integerWaveNormSq wave)*
    complexCoordinateAmplitudeSq (wholeVelocity (velocityJet seed order time) wave)

theorem wholeDensity_support (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    Function.support (wholeDensity seed order time) ⊆ {wave | wave ≠ 0} := by
  intro wave included
  by_contra zero
  have atZero : wave=0 := not_ne_iff.mp zero
  subst wave
  simp [wholeDensity,wholeVelocity_zero,complexCoordinateAmplitudeSq] at included

theorem whole_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    Summable (wholeDensity seed order time) := by
  have punctured : Summable (fun wave : NonzeroIntegerWavevector => wholeDensity seed order time wave.1) := by
    simpa only [wholeDensity,NativeUnheatedWindowGradient.whole_row_mass] using weighted_summable seed order time valid
  exact ((hasSum_subtype_iff_of_support_subset (wholeDensity_support seed order time)).mp punctured.hasSum).summable

theorem whole_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 < time) :
    (∑' wave, wholeDensity seed order time wave) ≤ budget seed order time := by
  rw [← tsum_subtype_eq_of_support_subset (wholeDensity_support seed order time)]
  simpa only [wholeDensity,NativeUnheatedWindowGradient.whole_row_mass] using moment_bound seed order time valid

theorem whole_bound_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time ≤ horizon) :
    (∑' wave, wholeDensity seed order time wave) ≤ budget seed order horizon := by
  rw [← tsum_subtype_eq_of_support_subset (wholeDensity_support seed order time)]
  simpa only [wholeDensity,NativeUnheatedWindowGradient.whole_row_mass] using
    moment_bound_on_interval seed order time horizon valid before

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem state_next (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    state seed order (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) =
      state response.1 order time (by linarith) := by
  apply lp.ext
  funext wave
  simp only [state_row,velocityJet,jet_next seed order response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowSobolevVelocity

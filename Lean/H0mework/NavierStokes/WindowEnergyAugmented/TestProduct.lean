import H0mework.NavierStokes.WindowEnergyAugmented.Green

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedTestProduct
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open NativeCommonAdvectorAction
open NativePhysicalFourier NativePhysicalContinuous NativeFiniteActionResolvent NativeWindowStressOseenTest
open NativeUnheatedStressProduct
open NativeWindowFiniteGramFourier (fourierRead)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem evaluate_original (M F : Finset IntegerWavevector) (value : physicalSpace M) (coordinate : Coordinate) :
    evaluate M F coordinate value=(Complex.reCLM.compLeftContinuous ℝ Torus)
      (scalarContinuous (complexSharpSupportProjection F value.1) coordinate) := by
  rw [evaluate_apply,scalarContinuous,tsum_eq_sum (s := F)]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro wave inside
    simp only [complexSharpSupportProjection_apply,if_pos inside]
    rfl
  · intro wave outside
    simp only [complexSharpSupportProjection_apply,if_neg outside,Pi.zero_apply]
    exact zero_smul ℂ (UnitAddTorus.mFourier wave)

theorem product_fourier (M F : Finset IntegerWavevector) (value : physicalSpace M)
    (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (output input : Coordinate) (wave : IntegerWavevector) :
    fourierRead wave (evaluate M F output value*evaluate M F input value)=
      -NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection F value.1)
        (complexSharpSupportProjection F value.1) wave output input := by
  let u:=complexSharpSupportProjection F value.1
  have amplitude : Summable (NativeFullOrderAction.amplitude u) := NativeCorrectionPhysical.finite_amplitude_paid F value.1
  have reality := complexSharpSupportProjection_reality F value.1 closedF (physical_reality (fun {_} inside => closedM _ inside) value)
  have same (coordinate : Coordinate) : scalarField u coordinate=ᵐ[volume]
      fun point => (evaluate M F coordinate value point : ℂ) := by
    filter_upwards [scalarContinuous_ae u coordinate amplitude,scalarField_real u reality coordinate] with point continuous real
    rw [evaluate_original]
    change _=((scalarContinuous u coordinate point).re : ℂ)
    rw [← continuous]
    apply Complex.ext
    · rfl
    · simpa using real
  rw [NativeWindowFiniteGramFourier.fourierRead_apply,NativeHigherTimeJets.mixedFlux_diagonal]
  rw [← physical_flux_fourier u output input wave]
  change (∫ point : Torus,_) = -(∫ point : Torus,_)
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [same output,same input] with point first last
  rw [first,last]
  simp only [ContinuousMap.mul_apply,Complex.ofReal_mul,smul_eq_mul]
  ring

theorem product_bound (M F : Finset IntegerWavevector) (value : physicalSpace M)
    (zero : 0∉M) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (output input : Coordinate) :
    ‖NativeWindowStressHeatSource.physical (evaluate M F output value*evaluate M F input value)‖≤
      12*Real.sqrt NativeUnheatedRieszKernel.constant*gradientMass (complexSharpSupportProjection F value.1) := by
  let u:=complexSharpSupportProjection F value.1
  have atZero : u 0=0 := projection_zero F value.1 (physical_supported value 0 zero)
  have regular : H1 u := projection_H1 F value.1
  let stress:=NativeWindowSobolevProduct.state u u atZero atZero regular regular
  have normed : ‖NativeWindowStressHeatSource.physical (evaluate M F output value*evaluate M F input value)‖≤‖stress‖ := by
    rw [← (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.norm_map]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro wave
    rw [UnitAddTorus.mFourierBasis_repr]
    have physical (f : C(Torus,ℝ)) : UnitAddTorus.mFourierCoeff (NativeWindowStressHeatSource.physical f) wave=fourierRead wave f := by
      change UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) f).toLp 2 volume ℂ) wave=_
      rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
      rfl
    rw [physical,product_fourier M F value closedM closedF,norm_neg]
    have component := PiLp.norm_apply_le (stress wave) (output,input)
    change ‖NativeWindowSobolevStress.quarter wave • NativeHigherTimeJets.mixedFlux u u wave output input‖≤‖stress wave‖ at component
    apply le_trans ?_ component
    rw [norm_smul,Real.norm_of_nonneg (NativeWindowSobolevStress.quarter_nonnegative wave)]
    apply le_mul_of_one_le_left (norm_nonneg _)
    unfold NativeWindowSobolevStress.quarter
    rw [Real.one_le_sqrt,Real.one_le_sqrt]
    linarith [integerWaveNormSq_nonneg wave]
  exact normed.trans ((NativeWindowSobolevProduct.state_bound u u atZero atZero regular regular).trans_eq (by ring))

theorem curl_original (M : Finset IntegerWavevector) (value : physicalSpace M) (zero : 0∉M) :
    curlPair M value.1 value.1=(2*Real.pi)^2*gradientMass (complexSharpSupportProjection M value.1) := by
  rw [curlPair,projection_mass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave inside
  rw [← curl_pair_row wave (fun same => zero (same ▸ inside)) _ _
    (physical_transverse value wave inside) (physical_transverse value wave inside),complexCoordinateRealInner_self]
  simp only [density,amplitude,euclideanCoordinateRow_norm_sq,integerWaveViscousMultiplier]
  change _=(2*Real.pi)^2*(integerWaveNormSq wave*complexCoordinateVectorNormSq (value.1 wave))
  ring

theorem projected_gradient_le (M F : Finset IntegerWavevector) (value : physicalSpace M) :
    gradientMass (complexSharpSupportProjection F value.1)≤gradientMass (complexSharpSupportProjection M value.1) := by
  rw [projection_mass,projection_mass]
  have outside (wave : IntegerWavevector) (absent : wave∉M) : density value.1 wave=0 := by
    simp [density,amplitude,physical_supported value wave absent,euclideanCoordinateRow]
  have same : (∑' wave,density value.1 wave)=∑ wave∈M,density value.1 wave := tsum_eq_sum outside
  have finite : Summable (density value.1) := summable_of_ne_finset_zero outside
  rw [← same]
  exact finite.sum_le_tsum F (fun wave _ => density_nonnegative value.1 wave)

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedTestProduct

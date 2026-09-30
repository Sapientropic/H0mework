import H0mework.Versions.X.NavierStokes.WindowSourceGreen.SpatialForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherCoefficientSpectrum
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeUnheatedSexticLatticePower (radical radical_square radical_fourth radical_positive)
open NativePhysicalFourier (ScalarSequence ScalarField)
open NativeWindowGreenSourceForm (velocity)
noncomputable section
variable {nu : Viscosity}

def spatialRow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (j i : Coordinate) (k : IntegerWavevector) : ℂ :=
  (radical k : ℂ)*NativePhysicalGradient.multiplier k j*velocity seed time k i

theorem spatial_square (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (j i : Coordinate) (k : IntegerWavevector) :
    ‖spatialRow seed time j i k‖^2 ≤ (2*Real.pi)^2*NativeWindowSobolevVelocity.wholeDensity seed 0 time k := by
  have component:‖velocity seed time k i‖^2 ≤ complexCoordinateAmplitudeSq (velocity seed time k) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have coordinate:(k j:ℝ)^2 ≤ 1+integerWaveNormSq k :=
    (Finset.single_le_sum (fun r _ => sq_nonneg ((k r:ℝ))) (Finset.mem_univ j)).trans
      (show integerWaveNormSq k ≤ 1+integerWaveNormSq k by linarith)
  have target:=mul_le_mul (mul_le_mul_of_nonneg_left coordinate (Real.sqrt_nonneg (1+integerWaveNormSq k)))
    component (sq_nonneg _) (by positivity [integerWaveNormSq_nonneg k])
  have paid:=mul_le_mul_of_nonneg_left target (sq_nonneg (2*Real.pi))
  simpa only [spatialRow,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,radical_square,
    NativePhysicalGradient.multiplier_norm_sq,NativeUnheatedSexticLatticePower.mass,
    NativeWindowSobolevVelocity.wholeDensity,mul_assoc,mul_left_comm,mul_comm,velocity] using paid

theorem spatial_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j i : Coordinate) :
    Summable (fun k => ‖spatialRow seed time j i k‖^2) :=
  ((NativeWindowSobolevVelocity.whole_summable seed 0 time valid).mul_left ((2*Real.pi)^2)).of_nonneg_of_le
    (fun _ => sq_nonneg _) (spatial_square seed time j i)

def spatial (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j i : Coordinate) : ScalarSequence :=
  ⟨spatialRow seed time j i,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using spatial_summable seed time valid j i)⟩

theorem spatial_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (j i : Coordinate) (k : IntegerWavevector) :
    spatial seed time valid j i k=(radical k:ℂ)*UnitAddTorus.mFourierCoeff
      (NativeWindowHistoryFirstJet.physicalJet seed time valid.le j i) k := by
  rw [NativeWindowHistoryFirstJet.physicalJet_fourier]
  change (radical k:ℂ)*NativePhysicalGradient.multiplier k j*velocity seed time k i=_
  simp only [velocity,NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_zero,mul_assoc]

theorem spatial_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (j i : Coordinate) :
    ‖spatial seed time valid j i‖^2 ≤ (2*Real.pi)^2*NativeWindowSobolevVelocity.budget seed 0 horizon := by
  rw [NativeWindowGreenTestForm.norm_square]
  apply ((spatial_summable seed time valid j i).tsum_le_tsum (spatial_square seed time j i)
    ((NativeWindowSobolevVelocity.whole_summable seed 0 time valid).mul_left ((2*Real.pi)^2))).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (NativeWindowSobolevVelocity.whole_bound_on_interval seed 0 time horizon valid before) (sq_nonneg _)

def temporalRow (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (i : Coordinate) (k : IntegerWavevector) : ℂ :=
  (radical k:ℂ)*NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) k i

theorem temporal_square (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (i : Coordinate) (k : IntegerWavevector) :
    ‖temporalRow seed order time i k‖^2 ≤ NativeWindowSobolevVelocity.wholeDensity seed order time k := by
  have component:‖NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) k i‖^2 ≤
      complexCoordinateAmplitudeSq (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) k) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [temporalRow,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,radical_square]
  apply (mul_le_mul_of_nonneg_left component (Real.sqrt_nonneg _)).trans
  change Real.sqrt (1+integerWaveNormSq k)*_ ≤ (1+integerWaveNormSq k)*Real.sqrt (1+integerWaveNormSq k)*_
  have nonnegative:0 ≤ complexCoordinateAmplitudeSq (NativeEndpointVelocityCarrier.wholeVelocity
      (NativeForwardWindowEvolution.velocityJet seed order time) k) := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (by nlinarith only [mul_nonneg (integerWaveNormSq_nonneg k) (Real.sqrt_nonneg (1+integerWaveNormSq k))]) nonnegative

theorem temporal_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time) (i : Coordinate) :
    Summable (fun k => ‖temporalRow seed order time i k‖^2) :=
  (NativeWindowSobolevVelocity.whole_summable seed order time valid).of_nonneg_of_le
    (fun _ => sq_nonneg _) (temporal_square seed order time i)

def temporal (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time) (i : Coordinate) : ScalarSequence :=
  ⟨temporalRow seed order time i,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using temporal_summable seed order time valid i)⟩

theorem temporal_fourier (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time)
    (i : Coordinate) (k : IntegerWavevector) :
    temporal seed order time valid i k=(radical k:ℂ)*UnitAddTorus.mFourierCoeff
      (NativePhysicalFourier.scalarField (NativeEndpointVelocityCarrier.wholeVelocity
        (NativeForwardWindowEvolution.velocityJet seed order time)) i) k := by
  rw [NativePhysicalFourier.scalarField_fourier]
  rfl

theorem temporal_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (i : Coordinate) :
    ‖temporal seed order time valid i‖^2 ≤ NativeWindowSobolevVelocity.budget seed order horizon := by
  rw [NativeWindowGreenTestForm.norm_square]
  exact ((temporal_summable seed order time valid i).tsum_le_tsum (temporal_square seed order time i)
    (NativeWindowSobolevVelocity.whole_summable seed order time valid)).trans
      (NativeWindowSobolevVelocity.whole_bound_on_interval seed order time horizon valid before)

def hOneRow (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (i : Coordinate) (k : IntegerWavevector) : ℂ :=
  (radical k:ℂ)^2*NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) k i

theorem hOne_square (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (i : Coordinate) (k : IntegerWavevector) :
    ‖hOneRow seed order time i k‖^2 ≤ NativeWindowSobolevVelocity.wholeDensity seed order time k := by
  have component:‖NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) k i‖^2 ≤
      complexCoordinateAmplitudeSq (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) k) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have root:1 ≤ Real.sqrt (1+integerWaveNormSq k) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 ≤ 1+integerWaveNormSq k by linarith [integerWaveNormSq_nonneg k])
  have nonnegative:0 ≤ complexCoordinateAmplitudeSq (NativeEndpointVelocityCarrier.wholeVelocity
      (NativeForwardWindowEvolution.velocityJet seed order time) k) := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  rw [hOneRow,norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,← pow_mul,
    show (2:ℕ)*2=4 from rfl,radical_fourth]
  dsimp only [NativeUnheatedSexticLatticePower.mass]
  apply (mul_le_mul_of_nonneg_left component (by positivity [integerWaveNormSq_nonneg k])).trans
  apply mul_le_mul_of_nonneg_right _ nonnegative
  simpa only [mul_one] using mul_le_mul_of_nonneg_left root (show 0 ≤ 1+integerWaveNormSq k by positivity [integerWaveNormSq_nonneg k])

theorem hOne_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time) (i : Coordinate) :
    Summable (fun k => ‖hOneRow seed order time i k‖^2) :=
  (NativeWindowSobolevVelocity.whole_summable seed order time valid).of_nonneg_of_le
    (fun _ => sq_nonneg _) (hOne_square seed order time i)

def hOne (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time) (i : Coordinate) : ScalarSequence :=
  ⟨hOneRow seed order time i,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hOne_summable seed order time valid i)⟩

theorem hOne_fourier (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time)
    (i : Coordinate) (k : IntegerWavevector) :
    hOne seed order time valid i k=(radical k:ℂ)^2*UnitAddTorus.mFourierCoeff
      (NativePhysicalFourier.scalarField (NativeEndpointVelocityCarrier.wholeVelocity
        (NativeForwardWindowEvolution.velocityJet seed order time)) i) k := by
  rw [NativePhysicalFourier.scalarField_fourier]
  rfl

theorem hOne_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (i : Coordinate) :
    ‖hOne seed order time valid i‖^2 ≤ NativeWindowSobolevVelocity.budget seed order horizon := by
  rw [NativeWindowGreenTestForm.norm_square]
  exact ((hOne_summable seed order time valid i).tsum_le_tsum (hOne_square seed order time i)
    (NativeWindowSobolevVelocity.whole_summable seed order time valid)).trans
      (NativeWindowSobolevVelocity.whole_bound_on_interval seed order time horizon valid before)

end
end SaturationMonoid.NavierStokes.NativeWindowMotherCoefficientSpectrum

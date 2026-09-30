import H0mework.NavierStokes.WindowEnergyHighTransport.Forcing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportSpatial
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativePhysicalGradient NativeForwardWindowPairingReadout
open NativeWindowCrossHistoryAction NativeWindowHighTransportGreen NativeWindowHighTransportForcing
open NativeWindowFiniteGramFourier (fourierRead fourierRead_apply)
open NativeWindowStressHeatSource (polynomial)
open NativePhysicalTranslation (displacement character_add character_displacement)
open NativeSpatialTranslation (phase phase_hasDerivAt phase_zero)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def shift (direction : Coordinate) (parameter : ℝ) (f : C(Torus,ℝ)) : C(Torus,ℝ) :=
  ⟨fun point => f (point+displacement direction parameter),by fun_prop⟩

theorem shift_zero (direction : Coordinate) (f : C(Torus,ℝ)) : shift direction 0 f=f := by
  ext point
  simp [shift,displacement]

theorem fourier_shift (direction : Coordinate) (parameter : ℝ) (f : C(Torus,ℝ)) (wave : IntegerWavevector) :
    fourierRead wave (shift direction parameter f)=phase direction parameter wave*fourierRead wave f := by
  let offset := displacement direction parameter
  have translated := integral_add_right_eq_self
    (fun point : Torus => UnitAddTorus.mFourier (-wave) (point-offset)*(f point : ℂ)) offset (μ := volume)
  simp only [add_sub_cancel_right] at translated
  rw [fourierRead_apply,fourierRead_apply]
  change (∫ point : Torus,UnitAddTorus.mFourier (-wave) point*(f (point+offset) : ℂ))=_
  rw [translated]
  simp_rw [sub_eq_add_neg,character_add,NativePhysicalTranslation.character_neg_neg]
  rw [← character_displacement]
  change (∫ point : Torus,(UnitAddTorus.mFourier (-wave) point*UnitAddTorus.mFourier wave offset)*(f point : ℂ))=_
  simp only [mul_assoc,mul_comm _ (UnitAddTorus.mFourier wave offset)]
  rw [integral_const_mul]
  rfl

theorem fourier_derivative (direction : Coordinate) (f derivative : C(Torus,ℝ))
    (actual : HasDerivAt (fun r => shift direction r f) derivative 0) (wave : IntegerWavevector) :
    fourierRead wave derivative=multiplier wave direction*fourierRead wave f := by
  have source := (fourierRead wave).hasFDerivAt.comp_hasDerivAt 0 actual
  simp only [Function.comp_def,fourier_shift] at source
  have spectral := (phase_hasDerivAt direction wave 0).mul_const (fourierRead wave f)
  simp only [phase_zero,mul_one] at spectral
  exact source.unique spectral

theorem polynomial_shift_derivative (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (j : Coordinate) :
    HasDerivAt (fun r => polynomial F (fun k => phase j r k*a k) j 0) (polynomial F a j 1) 0 := by
  have source := HasDerivAt.sum (u := F) fun wave _ =>
    ((phase_hasDerivAt j wave 0).mul_const (a wave)).smul_const (UnitAddTorus.mFourier wave)
  simpa only [polynomial,pow_zero,one_mul,pow_one,phase_zero,mul_one,Finset.sum_fn] using source

theorem velocity_shift (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (i j : Coordinate) (parameter : ℝ) :
    shift j parameter (velocity seed F time i)=
      (Complex.reCLM.compLeftContinuous ℝ Torus)
        (polynomial F (fun k => phase j parameter k*velocityRead k i (NativeUnifiedCompleteSource.source seed time)) j 0) := by
  ext point
  change NativeWindowStressHeatTime.field seed F i time (point+displacement j parameter)=_
  rw [NativeWindowStressHeatTime.field_original,← NativeWindowStressHeatSource.jetRead_zero F j i,
    NativeWindowStressHeatSource.jetRead_apply]
  change (polynomial F (fun k => velocityRead k i (NativeUnifiedCompleteSource.source seed time)) j 0
    (point+displacement j parameter)).re=
      (polynomial F (fun k => phase j parameter k*velocityRead k i (NativeUnifiedCompleteSource.source seed time)) j 0 point).re
  simp only [polynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,pow_zero,one_mul,
    character_add,character_displacement]
  change (∑ k∈F,velocityRead k i (NativeUnifiedCompleteSource.source seed time)*
    (UnitAddTorus.mFourier k point*phase j parameter k)).re=
      (∑ k∈F,(phase j parameter k*velocityRead k i (NativeUnifiedCompleteSource.source seed time))*UnitAddTorus.mFourier k point).re
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem velocity_shift_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (i j : Coordinate) :
    HasDerivAt (fun r => shift j r (velocity seed F time i)) (gradient seed F time j i) 0 := by
  have source := (Complex.reCLM.compLeftContinuous ℝ Torus).hasFDerivAt.comp_hasDerivAt 0
    (polynomial_shift_derivative F (fun k => velocityRead k i (NativeUnifiedCompleteSource.source seed time)) j)
  simp only [velocity_shift]
  convert! source using 1
  ext point
  exact NativeWindowStressHeatSource.jetRead_apply F j 1 i _ point

theorem cubic_shift_derivative (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (time : ℝ) (j output input : Coordinate) :
    HasDerivAt (fun r => shift j r (NativeWindowHighTransportWork.cubic seed F A j output input time))
      (currentDerivative seed F A j output input time) 0 := by
  have source := (((velocity_shift_derivative seed F time j j).sub (velocity_shift_derivative seed A time j j)).mul
    (velocity_shift_derivative seed F time output j)).mul (velocity_shift_derivative seed F time input j)
  simp only [shift_zero] at source
  convert! source using 1
  ext point
  simp only [currentDerivative,drift,driftJet,Pi.sub_apply,Pi.mul_apply,shift_zero,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.mul_apply]
  ring


theorem currentDerivative_fourier (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (time : ℝ) (j output input : Coordinate) (wave : IntegerWavevector) :
    fourierRead wave (currentDerivative seed F A j output input time)=
      multiplier wave j*fourierRead wave (NativeWindowHighTransportWork.cubic seed F A j output input time) :=
  fourier_derivative j _ _ (cubic_shift_derivative seed F A time j output input) wave

theorem highWindow_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (F A : Finset IntegerWavevector) (output input : Coordinate) (wave : IntegerWavevector) :
    fourierRead wave (highWindow seed time F A output input)=
      ∑ j : Coordinate,multiplier wave j*fourierRead wave
        (NativeWindowHighTransportWork.physicalCurrent seed time F A j output input) := by
  rw [highWindow,← (fourierRead wave).integral_comp_comm (highPair_integrable seed time F A output input)]
  have actual : (fun shift => fourierRead wave (highPair seed F A output input (time-shift))) =ᵐ[averageMeasure]
      fun shift => ∑ j : Coordinate,multiplier wave j*fourierRead wave
        (NativeWindowHighTransportWork.cubic seed F A j output input (time-shift)) := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    rw [← divergence_pair seed F A (time-shift) (by linarith),map_sum]
    simp only [currentDerivative_fourier]
  rw [integral_congr_ae actual]
  have paid (j : Coordinate) : Integrable (fun shift => multiplier wave j*fourierRead wave
      (NativeWindowHighTransportWork.cubic seed F A j output input (time-shift))) averageMeasure :=
    ((fourierRead wave).integrable_comp (NativeWindowHighTransportWork.cubic_integrable seed time F A j output input)).const_mul _
  rw [integral_finsetSum Finset.univ (fun j _ => paid j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,(fourierRead wave).integral_comp_comm
    (NativeWindowHighTransportWork.cubic_integrable seed time F A j output input)]
  rfl

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportSpatial

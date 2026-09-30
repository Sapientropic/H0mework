import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.StrainPhysical
import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Heat
import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.Resolvent

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPressureStrainHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowHighPressureCurrent NativeWindowPressureStrainPhysical
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def sourcePressure (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (F : Finset IntegerWavevector) (time : ℝ) : C(Torus,ℝ) :=
  pressureScalar (value seed radius time) F

theorem sourcePressure_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (F : Finset IntegerWavevector) (time : ℝ) :
    ‖sourcePressure seed radius F time‖ ≤ pressureCap F*(NativeUnifiedCompleteSource.budget seed)^2 :=
  (pressureScalar_bound _ F).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (value_bound seed radius time) 2) (pressureCap_nonnegative F))

theorem pressure_memLp (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector) :
    MemLp (fun shift => sourcePressure seed radius F (time-shift)) 2 averageMeasure := by
  have source := (pressureScalar_continuous F).comp_aestronglyMeasurable (value_measurable seed radius)
  have moved := source.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)
  have measured := moved.mono_ac (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞)))
  exact MemLp.of_bound measured (pressureCap F*(NativeUnifiedCompleteSource.budget seed)^2)
    (Eventually.of_forall fun shift => sourcePressure_bound seed radius F (time-shift))

def pressureHistoryField (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector) :
    Lp C(Torus,ℝ) 2 averageMeasure :=
  (pressure_memLp seed radius time F).toLp (fun shift => sourcePressure seed radius F (time-shift))

def pressureHistory (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) : NativeWindowFiniteGramSource.H :=
  (ContinuousMap.evalCLM ℝ point).compLp (pressureHistoryField seed radius time F)

theorem pressureHistory_original (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) : pressureHistory seed radius time F point =ᵐ[averageMeasure]
      fun shift => sourcePressure seed radius F (time-shift) point := by
  filter_upwards [(ContinuousMap.evalCLM ℝ point).coeFn_compLp (pressureHistoryField seed radius time F),
    MemLp.coeFn_toLp (pressure_memLp seed radius time F)] with shift evaluated original
  change ((ContinuousMap.evalCLM ℝ point).compLp (pressureHistoryField seed radius time F)) shift=_
  change pressureHistoryField seed radius time F shift=sourcePressure seed radius F (time-shift) at original
  rw [evaluated,original]
  rfl

def highGradientHistory (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) (j i : Coordinate) : NativeWindowFiniteGramSource.H :=
  NativeWindowHighTransportHeat.gradientHistory seed time F point j i-
    NativeWindowHighTransportHeat.gradientHistory seed time (F∩integerWaveFrequencyCube radius) point j i

theorem highGradientHistory_original (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) (j i : Coordinate) : highGradientHistory seed radius time F point j i =ᵐ[averageMeasure]
      fun shift => gradient (value seed radius (time-shift)) F j i point := by
  filter_upwards [NativeWindowHighTransportHeat.gradientHistory_original seed time F point j i,
    NativeWindowHighTransportHeat.gradientHistory_original seed time (F∩integerWaveFrequencyCube radius) point j i,
    Lp.coeFn_sub (NativeWindowHighTransportHeat.gradientHistory seed time F point j i)
      (NativeWindowHighTransportHeat.gradientHistory seed time (F∩integerWaveFrequencyCube radius) point j i)] with shift first last difference
  change (NativeWindowHighTransportHeat.gradientHistory seed time F point j i-
    NativeWindowHighTransportHeat.gradientHistory seed time (F∩integerWaveFrequencyCube radius) point j i) shift=_
  rw [difference]
  simp only [Pi.sub_apply]
  rw [first,last,source_gradient]
  rfl

theorem strain_integrable (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : Integrable (fun shift => strain (value seed radius (time-shift)) F output input) averageMeasure := by
  let read := gradientRead F radius output input+gradientRead F radius input output
  have gradient := read.integrable_comp (NativeForwardWindowPairingReadout.original_integrable seed time)
  have pressure := pressure_memLp seed radius time F
  have paid := gradient.bdd_mul pressure.aestronglyMeasurable (Eventually.of_forall fun shift => sourcePressure_bound seed radius F (time-shift))
  apply paid.congr
  filter_upwards with shift
  simp only [read,add_apply,strain,sourcePressure,source_gradient]

def window (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∫ shift,strain (value seed radius (time-shift)) F output input ∂averageMeasure

theorem window_fourier (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ k,k ∈ F → waveNeg k ∈ F) (output input : Coordinate) (k : IntegerWavevector) :
    NativeWindowFiniteGramFourier.fourierRead k (window seed radius time F output input)=
      ∫ shift,strainRow (value seed radius (time-shift)) F k output input ∂averageMeasure := by
  rw [window,← (NativeWindowFiniteGramFourier.fourierRead k).integral_comp_comm (strain_integrable seed radius time F output input)]
  apply integral_congr_ae
  filter_upwards with shift
  exact source_strain_fourier seed radius (time-shift) F closed output input k

theorem window_history (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (F : Finset IntegerWavevector)
    (point : Torus) (output input : Coordinate) : window seed radius time F output input point=
      inner ℝ (pressureHistory seed radius time F point) (highGradientHistory seed radius time F point output input)+
      inner ℝ (pressureHistory seed radius time F point) (highGradientHistory seed radius time F point input output) := by
  change (ContinuousMap.evalCLM ℝ point) (∫ shift,strain (value seed radius (time-shift)) F output input ∂averageMeasure)=_
  rw [← (ContinuousMap.evalCLM ℝ point).integral_comp_comm (strain_integrable seed radius time F output input),← inner_add_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pressureHistory_original seed radius time F point,
    highGradientHistory_original seed radius time F point output input,
    highGradientHistory_original seed radius time F point input output,
    Lp.coeFn_add (highGradientHistory seed radius time F point output input) (highGradientHistory seed radius time F point input output)]
    with shift pressure first last sum
  rw [sum]
  simp only [Pi.add_apply]
  rw [pressure,first,last]
  simp only [strain,sourcePressure,ContinuousMap.evalCLM_apply,ContinuousMap.mul_apply,ContinuousMap.add_apply,RCLike.inner_apply,conj_trivial]
  ring

theorem window_trace_zero (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : (∑ i : Coordinate,window seed radius time F i i)=0 := by
  simp only [window]
  rw [← integral_finsetSum Finset.univ (fun i _ => strain_integrable seed radius time F i i)]
  apply integral_eq_zero_of_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
  exact source_strain_trace_zero seed radius (time-shift) (by linarith) F

def correction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowHighTransportRelative.primitiveField seed F radius 0 time output input-
    NativeWindowStressHeatEnergy.field (NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input)

def relative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatBalance.sigma seed F output input time-correction seed F radius time output input

def jointWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  -(∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
      (NativeWindowStressHeatSource.physical (window seed radius time F output input)))-
    2*nu.coeff*(∑ output : Coordinate,∑ input : Coordinate,inner ℝ (correction seed F radius time output input)
      (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.diffusion seed time F output input)))

private theorem physical_pairing (test : ScalarField) (field : C(Torus,ℝ)) :
    inner ℝ test (NativeWindowStressHeatSource.physical field)=∫ point : Torus,(test point).re*field point := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) field)] with point read
  change inner ℝ (test point) (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) field).toLp 2 volume ℂ point)=_
  rw [read]
  change inner ℝ (test point) (field point:ℂ)=_
  simp [Complex.inner,mul_comm]

theorem jointWork_history (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    jointWork seed F radius time=
      -(∑ output : Coordinate,∑ input : Coordinate,∫ point : Torus,(relative seed F radius time output input point).re*
        (inner ℝ (pressureHistory seed radius time F point) (highGradientHistory seed radius time F point output input)+
          inner ℝ (pressureHistory seed radius time F point) (highGradientHistory seed radius time F point input output)))-
        2*nu.coeff*(∑ output : Coordinate,∑ input : Coordinate,∫ point : Torus,(correction seed F radius time output input point).re*
          ∑ j : Coordinate,inner ℝ (NativeWindowHighTransportHeat.gradientHistory seed time F point j output)
            (NativeWindowHighTransportHeat.gradientHistory seed time F point j input)) := by
  simp only [jointWork,physical_pairing,window_history,NativeWindowHighTransportHeat.diffusion_history]

theorem isotropic_pressure_zero (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (test : ScalarField) :
    (∑ i : Coordinate,inner ℝ test (NativeWindowStressHeatSource.physical (window seed radius time F i i)))=0 := by
  rw [← inner_sum,← map_sum,window_trace_zero seed radius time nonnegative F,map_zero,inner_zero_right]

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem window_next (seed : GeneratedWholeRestartCurrent nu) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    window seed radius (step.2.clockAdvance+time) F output input=window step.1 radius time F output input := by
  unfold window
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
  rw [add_sub_assoc,source_strain_next seed step generated radius (time-shift) (by linarith) F output input]

theorem correction_next (seed : GeneratedWholeRestartCurrent nu) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : correction seed F radius (step.2.clockAdvance+time)=correction step.1 F radius time := by
  funext output input
  simp only [correction,NativeWindowHighTransportRelative.primitiveField,
    NativeWindowHighTransportResolvent.primitive_next seed F radius 0 step generated time nonnegative,
    NativeWindowHighPressureResolvent.primitive_next seed F radius 0 step generated time nonnegative]

theorem relative_next (seed : GeneratedWholeRestartCurrent nu) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : relative seed F radius (step.2.clockAdvance+time)=relative step.1 F radius time := by
  funext output input
  simp only [relative,correction_next seed step generated radius time nonnegative F,NativeWindowStressHeatBalance.sigma,
    NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative]

theorem jointWork_next (seed : GeneratedWholeRestartCurrent nu) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : jointWork seed F radius (step.2.clockAdvance+time)=jointWork step.1 F radius time := by
  have diffusion := congrArg (fun data => data.2.1) (NativeWindowStressHeatSource.whole_next seed step generated time nonnegative F)
  change NativeWindowStressHeatSource.diffusion seed (step.2.clockAdvance+time) F=NativeWindowStressHeatSource.diffusion step.1 time F at diffusion
  simp only [jointWork,relative_next seed step generated radius time nonnegative F,
    correction_next seed step generated radius time nonnegative F,window_next seed step generated radius time nonnegative F,diffusion]

end
end SaturationMonoid.NavierStokes.NativeWindowPressureStrainHistory

import H0mework.NavierStokes.WindowPhysics.WindowSource
import H0mework.NavierStokes.NativeAction.Pairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeForwardWindowPairingReadout

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowSource

noncomputable section

def meanRead : FullSpace →L[ℝ] WholeRestartVelocityEndpointState :=
  WithLp.fstL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space

def stressRead (wave : IntegerWavevector) (output input : Coordinate) : FullSpace →L[ℝ] ℂ :=
  (NativeCompleteStressCarrier.readCLM wave output input).comp
    (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space)

def velocityRead (wave : IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj coordinate).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
      (wholeVelocityCLM.comp meanRead))

variable {nu : Viscosity}

theorem linear_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (read : FullSpace →L[ℝ] E) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    read (source seed time) = ∫ shift : ℝ, kernel shift • read (NativeUnifiedCompleteSource.source seed (time - shift)) := by
  rw [source_integrand, ← read.integral_comp_comm (source_integrable seed time)]
  simp only [map_smul]

theorem linear_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (read : FullSpace →L[ℝ] E) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Integrable (fun shift : ℝ => kernel shift • read (NativeUnifiedCompleteSource.source seed (time - shift))) := by
  simpa only [map_smul] using read.integrable_comp (source_integrable seed time)

theorem velocity_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    wholeVelocity (source seed time).fst wave coordinate =
      ∫ shift : ℝ, kernel shift • wholeVelocity (NativeUnifiedCompleteSource.source seed (time - shift)).fst wave coordinate :=
  linear_integral (velocityRead wave coordinate) seed time

theorem stress_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    NativeCompleteStressCarrier.read (source seed time).snd wave output input =
      ∫ shift : ℝ, kernel shift • NativeCompleteStressCarrier.read
        (NativeUnifiedCompleteSource.source seed (time - shift)).snd wave output input :=
  linear_integral (stressRead wave output input) seed time

theorem mean_reality (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    WholeRestartVelocityEndpointReality (source seed time).fst := by
  intro wave coordinate
  have same : wholeVelocity (source seed time).fst (nonzeroIntegerWavevectorNeg wave).1 coordinate =
      star (wholeVelocity (source seed time).fst wave.1 coordinate) := by
    rw [velocity_integral, velocity_integral]
    have conjugated := integral_conj (μ := volume) (f := fun shift : ℝ => kernel shift •
      wholeVelocity (NativeUnifiedCompleteSource.source seed (time - shift)).fst wave.1 coordinate)
    simp only [starRingEnd_apply] at conjugated
    rw [← conjugated]
    apply integral_congr_ae
    filter_upwards with shift
    have original := congrFun (NativeEndpointVelocityCarrier.wholeVelocity_reality
      (NativeCompletePairedAction.source seed (time - shift)).mean
      (NativeCompletePairedAction.source seed (time - shift)).reality wave.1) coordinate
    change wholeVelocity (NativeUnifiedCompleteSource.source seed (time - shift)).fst
      (waveNeg wave.1) coordinate =
      star (wholeVelocity (NativeUnifiedCompleteSource.source seed (time - shift)).fst wave.1 coordinate) at original
    change kernel shift • wholeVelocity (NativeUnifiedCompleteSource.source seed (time - shift)).fst
      (waveNeg wave.1) coordinate = _
    rw [original]
    simp
  simpa only [wholeVelocity_nonzero] using same

theorem stress_symmetric (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    NativeCompleteStressCarrier.read (source seed time).snd wave output input =
      NativeCompleteStressCarrier.read (source seed time).snd wave input output := by
  rw [stress_integral, stress_integral]
  apply integral_congr_ae
  filter_upwards with shift
  exact congrArg (fun value : ℂ => kernel shift • value)
    (NativeCompletePairedAction.source_symmetric seed (time - shift) wave output input)

def currentLinear (direction : Fin 4) (wave : IntegerWavevector) : FullSpace →L[ℝ] ℂ :=
  Fin.cases ((-(1 / 8 : ℝ)) • ∑ coordinate : Coordinate, stressRead wave coordinate coordinate)
    (velocityRead wave) direction

def currentOffset (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  Fin.cases (NativePairedCurrentFourier.baseline wave) (fun _ => 0) direction

theorem current_split (value : FullSpace) (direction : Fin 4) (wave : IntegerWavevector) :
    NativePairedCurrentFourier.coefficient (wholeVelocity value.fst)
      (NativeCompleteStressCarrier.read value.snd) direction wave =
      currentOffset direction wave + currentLinear direction wave value := by
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · change NativePairedCurrentFourier.baseline wave -
      (∑ coordinate : Coordinate, NativeCompleteStressCarrier.read value.snd wave coordinate coordinate) / 8 = _
    simp only [currentOffset, currentLinear, Fin.cases_zero, smul_apply, sum_apply,
      stressRead, ContinuousLinearMap.comp_apply, WithLp.sndL_apply, NativeCompleteStressCarrier.readCLM_apply,
      Complex.real_smul]
    push_cast
    ring
  · change wholeVelocity value.fst wave coordinate = 0 + velocityRead wave coordinate value
    rw [zero_add]
    rfl

theorem current_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) :
    NativePairedCurrentFourier.coefficient (wholeVelocity (source seed time).fst)
      (NativeCompleteStressCarrier.read (source seed time).snd) direction wave =
      ∫ shift : ℝ, kernel shift • NativeHilbertDiracCurrent.diracCurrent
        (NativeCompletePairedAction.source seed (time - shift)) direction wave := by
  simp_rw [NativeCompletePairedAction.source_current, current_split, smul_add]
  rw [integral_add (kernel_integrable.smul_const _) (linear_integrable (currentLinear direction wave) seed time),
    integral_smul_const, kernel_mass, one_smul, ← linear_integral]

def density (shift : ℝ) : ℝ≥0 := ⟨kernel shift, kernel_nonnegative shift⟩

theorem density_measurable : Measurable density :=
  (kernel_smooth.continuous.subtype_mk (fun shift => kernel_nonnegative shift)).measurable

def averageMeasure : Measure ℝ := volume.withDensity (fun shift => (density shift : ℝ≥0∞))

instance average_probability : IsProbabilityMeasure averageMeasure where
  measure_univ := by
    have integrable : Integrable (fun shift => (density shift : ℝ)) (volume : Measure ℝ) := kernel_integrable
    rw [averageMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_coe_eq_integral density integrable]
    change ENNReal.ofReal (∫ shift, kernel shift) = 1
    rw [kernel_mass]
    norm_num

theorem density_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (field : ℝ → E) :
    (∫ shift, field shift ∂averageMeasure) = ∫ shift, kernel shift • field shift :=
  integral_withDensity_eq_integral_smul density_measurable field

theorem original_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Integrable (fun shift => NativeUnifiedCompleteSource.source seed (time - shift)) averageMeasure := by
  apply (integrable_withDensity_iff_integrable_smul density_measurable).2
  exact source_integrable seed time

theorem source_probability_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    source seed time = ∫ shift, NativeUnifiedCompleteSource.source seed (time - shift) ∂averageMeasure := by
  rw [density_integral, source_integrand]

theorem linear_probability_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (read : FullSpace →L[ℝ] E) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    read (source seed time) = ∫ shift, read (NativeUnifiedCompleteSource.source seed (time - shift)) ∂averageMeasure := by
  rw [source_probability_integral, ← read.integral_comp_comm (original_integrable seed time)]

end
end SaturationMonoid.NavierStokes.NativeForwardWindowPairingReadout

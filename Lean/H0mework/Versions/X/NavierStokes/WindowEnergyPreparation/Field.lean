import H0mework.Versions.X.NavierStokes.WindowStressHeat.Time
import H0mework.Versions.X.NavierStokes.WindowSourcePreparation.Write

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowStressPreparationField
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativePhysicalFourier
open NativeWindowStressHeatTime (field)
noncomputable section
variable {nu : Viscosity}

def row (wave : IntegerWavevector) (coordinate : Coordinate) : WholeRestartVelocityEndpointState →L[ℝ] ℂ :=
  integerWaveNormSq wave^2 • ((ContinuousLinearMap.proj coordinate).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp wholeVelocityCLM))

theorem row_embed (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) (coordinate : Coordinate) :
    row wave coordinate (NativeNegativeFourMomentum.embed value) = wholeVelocity value wave coordinate := by
  change integerWaveNormSq wave^2 • wholeVelocity (NativeNegativeFourMomentum.embed value) wave coordinate = _
  by_cases zero : wave=0
  · subst wave
    simp only [wholeVelocity_zero,Pi.zero_apply,smul_zero]
  · have actual := congrArg (fun state : ComplexCoordinateEuclidean => state coordinate)
      (NativeNegativeFourMomentum.embed_reconstruct value ⟨wave,zero⟩)
    rw [wholeVelocity_nonzero _ ⟨wave,zero⟩ coordinate,wholeVelocity_nonzero _ ⟨wave,zero⟩ coordinate]
    exact actual

def read (F : Finset IntegerWavevector) (coordinate : Coordinate) : WholeRestartVelocityEndpointState →L[ℝ] C(Torus,ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ Torus).comp
    (∑ wave ∈ F, ((ContinuousLinearMap.toSpanSingleton ℂ (UnitAddTorus.mFourier wave)).restrictScalars ℝ).comp
      (row wave coordinate))

theorem read_full (F : Finset IntegerWavevector) (coordinate : Coordinate) (source : FullSpace) :
    read F coordinate (NativeForwardWindowWrite.stateCLM source) = NativeWindowFiniteGramFourier.read F coordinate source := by
  unfold read NativeWindowFiniteGramFourier.read NativeWindowFiniteGramFourier.complexRead
  simp only [ContinuousLinearMap.comp_apply,sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro wave _
  rw [show NativeForwardWindowWrite.stateCLM source = NativeNegativeFourMomentum.embed source.fst from rfl,row_embed]
  rfl

theorem field_read (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (time : ℝ) :
    field seed F coordinate time = read F coordinate (NativeGlobalHilbertAction.sourceState seed time) := by
  rw [← NativeForwardWindowWrite.stateCLM_original,read_full,NativeWindowStressHeatTime.field_original]

theorem field_lipschitz (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate) :
    LipschitzWith (‖read F coordinate‖₊*NativeWindowPreparationAction.bound seed) (field seed F coordinate) := by
  simpa only [Function.comp_def,← field_read] using
    (read F coordinate).lipschitz.comp (NativeWindowPreparationAction.state_lipschitz seed)

def fullRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate)
    (time : ℝ) : C(Torus,ℝ) := read F coordinate (momentumCLM nu (NativeUnifiedCompleteSource.source seed time))

def rate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate)
    (time : ℝ) : C(Torus,ℝ) := read F coordinate (NativeWindowPreparationAction.action seed time)

theorem field_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (coordinate : Coordinate) :
    ∀ᵐ time : ℝ, HasDerivAt (field seed F coordinate) (rate seed F coordinate time) time := by
  filter_upwards [NativeWindowPreparationAction.state_derivative seed] with time actual
  simpa only [Function.comp_def,← field_read,rate] using! (read F coordinate).hasFDerivAt.comp_hasDerivAt time actual

theorem field_nonpositive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (time : ℝ) (before : time ≤ 0) : field seed F coordinate time = field seed F coordinate 0 := by
  rw [field_read,field_read,NativeWindowPreparationAction.state_nonpositive seed time before]

theorem fullRate_nonpositive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (time : ℝ) (before : time ≤ 0) : fullRate seed F coordinate time = fullRate seed F coordinate 0 := by
  rw [fullRate,fullRate,NativeWindowPreparationSource.complete_nonpositive seed time before]

theorem rate_correction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (time : ℝ) : rate seed F coordinate time = fullRate seed F coordinate time-
      NativeWindowPreparationWrite.inactive time • fullRate seed F coordinate 0 := by
  rw [rate,NativeWindowPreparationAction.action_correction,map_sub]
  by_cases before : time ≤ 0 <;> simp [NativeWindowPreparationWrite.inactive,before,fullRate]

theorem rate_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (a b : ℝ) : IntervalIntegrable (rate seed F coordinate) volume a b :=
  ⟨(read F coordinate).integrable_comp (NativeWindowPreparationAction.action_integrable seed a b).1,
    (read F coordinate).integrable_comp (NativeWindowPreparationAction.action_integrable seed a b).2⟩

theorem fullRate_original_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) : ∀ᵐ time : ℝ, 0 < time →
      fullRate seed F coordinate time = NativeWindowStressHeatTime.fieldRate seed F coordinate time := by
  filter_upwards [field_derivative seed F coordinate,NativeWindowStressHeatTime.field_hasDerivAt_ae seed F coordinate]
    with time first last positive
  have actual := first.unique (last positive)
  simpa only [rate,NativeWindowPreparationAction.action_positive seed time positive,fullRate] using actual

end
end SaturationMonoid.NavierStokes.NativeWindowStressPreparationField

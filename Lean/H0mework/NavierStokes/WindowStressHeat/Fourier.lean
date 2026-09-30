import H0mework.NavierStokes.WindowHistory.Current
import H0mework.NavierStokes.WindowStressHeat.FiniteSource
import H0mework.NavierStokes.WindowStressHeat.Energy
import H0mework.NavierStokes.PhysicalJets.CorrectionPhysical
import H0mework.NavierStokes.SourceUnheated.WindowStress

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowFiniteGramFourier
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowPairingReadout
open NativePhysicalFourier NativePhysicalContinuous NativeWindowFiniteGramSource
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def complexRead (F : Finset IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] C(Torus,ℂ) :=
  ∑ wave ∈ F, ((ContinuousLinearMap.toSpanSingleton ℂ (UnitAddTorus.mFourier wave)).restrictScalars ℝ).comp
    (velocityRead wave coordinate)

def read (F : Finset IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ Torus).comp (complexRead F coordinate)

theorem complexRead_original (F : Finset IntegerWavevector) (coordinate : Coordinate) (state : FullSpace) :
    complexRead F coordinate state = scalarContinuous (complexSharpSupportProjection F (wholeVelocity state.fst)) coordinate := by
  classical
  rw [scalarContinuous,tsum_eq_sum (s := F)]
  · simp only [complexRead,sum_apply]
    apply Finset.sum_congr rfl
    intro wave member
    simp only [complexSharpSupportProjection_apply,if_pos member]
    rfl
  · intro wave outside
    simp only [complexSharpSupportProjection_apply,if_neg outside,Pi.zero_apply]
    exact zero_smul ℂ (UnitAddTorus.mFourier wave)

theorem read_original (F : Finset IntegerWavevector) (coordinate : Coordinate) (state : FullSpace) (point : Torus) :
    read F coordinate state point = continuousField (complexSharpSupportProjection F (wholeVelocity state.fst)) point coordinate := by
  change (complexRead F coordinate state point).re = _
  rw [complexRead_original]
  rfl

theorem read_physical (F : Finset IntegerWavevector) (coordinate : Coordinate) (state : FullSpace) (point : PhysicalSpace) :
    read F coordinate state (NativeFullOrderSynthesis.circlePoint point) = fieldRead F point coordinate state := by
  rw [read_original,fieldRead_original]
  exact congrArg (fun value : PhysicalSpace => value coordinate)
    (congrFun (NativeCorrectionPhysical.spatialField_finite_compiler F (wholeVelocity state.fst)) point)

def pairRead (F : Finset IntegerWavevector) (output input : Coordinate) (state : FullSpace) : C(Torus,ℝ) :=
  read F output state*read F input state

theorem pair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) :
    Integrable (fun shift => pairRead F output input (NativeUnifiedCompleteSource.source seed (time-shift))) averageMeasure := by
  have left := (read F output).integrable_comp (original_integrable seed time)
  have right := (read F input).integrable_comp (original_integrable seed time)
  apply Integrable.of_bound (left.aestronglyMeasurable.mul right.aestronglyMeasurable)
    (‖read F output‖*‖read F input‖*NativeUnifiedCompleteSource.budget seed^2)
  filter_upwards with shift
  change ‖read F output _*read F input _‖ ≤ _
  apply (norm_mul_le _ _).trans
  have bounds (coordinate : Coordinate) : ‖read F coordinate (NativeUnifiedCompleteSource.source seed (time-shift))‖ ≤
      ‖read F coordinate‖*NativeUnifiedCompleteSource.budget seed :=
    ((read F coordinate).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (NativeUnifiedCompleteSource.source_bound seed _) (norm_nonneg _))
  exact (mul_le_mul (bounds output) (bounds input) (norm_nonneg _)
    (mul_nonneg (norm_nonneg (read F output)) ((norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed (time-shift))))).trans_eq (by ring)

def stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∫ shift, pairRead F output input (NativeUnifiedCompleteSource.source seed (time-shift)) ∂averageMeasure

theorem stress_apply (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) (point : Torus) : stress seed time F output input point =
      ∫ shift, read F output (NativeUnifiedCompleteSource.source seed (time-shift)) point*
        read F input (NativeUnifiedCompleteSource.source seed (time-shift)) point ∂averageMeasure := by
  exact ((ContinuousMap.evalCLM ℝ point).integral_comp_comm (pair_integrable seed time F output input)).symm

theorem stress_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) (point : PhysicalSpace) :
    stress seed time F output input (NativeFullOrderSynthesis.circlePoint point) =
      NativeWindowFiniteGramSource.stress seed time F point output input := by
  rw [stress_apply,NativeWindowFiniteGramSource.stress_original]
  simp only [read_physical]

def fourierRead (wave : IntegerWavevector) : C(Torus,ℝ) →L[ℝ] ℂ :=
  (((lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave).comp
      (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ)).restrictScalars ℝ |>.comp
      (Complex.ofRealCLM.compLeftContinuous ℝ Torus)

theorem fourierRead_apply (wave : IntegerWavevector) (field : C(Torus,ℝ)) :
    fourierRead wave field = UnitAddTorus.mFourierCoeff (fun point => (field point : ℂ)) wave := by
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr
    (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) field).toLp 2 volume ℂ) wave = _
  rw [UnitAddTorus.mFourierBasis_repr,UnitAddTorus.mFourierCoeff_toLp]
  rfl

theorem pair_fourier (F : Finset IntegerWavevector) (state : FullSpace)
    (reality : FiniteStateFourierReality (complexSharpSupportProjection F (wholeVelocity state.fst)))
    (output input : Coordinate) (wave : IntegerWavevector) :
    fourierRead wave (pairRead F output input state) =
      -NativeCompleteStressCarrier.read (NativeCompleteStressBilinear.mixed
        (complexSharpSupportProjection F (wholeVelocity state.fst))
        (complexSharpSupportProjection F (wholeVelocity state.fst))) wave output input := by
  have amplitude : Summable (NativeFullOrderAction.amplitude (complexSharpSupportProjection F (wholeVelocity state.fst))) :=
    NativeCorrectionPhysical.finite_amplitude_paid F (wholeVelocity state.fst)
  have same (coordinate : Coordinate) : scalarField (complexSharpSupportProjection F (wholeVelocity state.fst)) coordinate =ᵐ[volume]
      fun point => (read F coordinate state point : ℂ) := by
    filter_upwards [scalarContinuous_ae _ coordinate amplitude,scalarField_real _ reality coordinate] with point continuous real
    change _ = ((complexRead F coordinate state point).re : ℂ)
    rw [complexRead_original,← continuous]
    apply Complex.ext
    · rfl
    · simpa using real
  rw [fourierRead_apply,NativeCompleteStressBilinear.mixed_read,NativeHigherTimeJets.mixedFlux_diagonal]
  have paid := physical_flux_fourier (complexSharpSupportProjection F (wholeVelocity state.fst)) output input wave
  rw [← paid]
  change (∫ point : Torus, _) = -(∫ point : Torus, _)
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [same output,same input] with point first last
  rw [first,last]
  simp only [pairRead,ContinuousMap.mul_apply,Complex.ofReal_mul,smul_eq_mul]
  ring

theorem stress_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (stress seed time F output input point : ℂ)) wave =
      -(∫ shift, NativeCompleteStressCarrier.read (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) wave output input
        ∂averageMeasure) := by
  rw [← fourierRead_apply,stress,← (fourierRead wave).integral_comp_comm (pair_integrable seed time F output input),← integral_neg]
  apply integral_congr_ae
  filter_upwards with shift
  rw [pair_fourier F _ (complexSharpSupportProjection_reality _ _ closed
    (wholeVelocity_reality _ (NativeCompletePairedAction.source seed (time-shift)).reality))]
  rw [NativeUnifiedCompleteSource.velocity_read]
  rfl

def coefficients (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ := fourierRead wave (stress seed time F output input)

theorem coefficients_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (wave : IntegerWavevector) (output input : Coordinate) :
    coefficients seed time F wave output input =
      -(∫ shift, NativeCompleteStressCarrier.read (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) wave output input
        ∂averageMeasure) := by
  rw [coefficients,fourierRead_apply]
  exact stress_fourier seed time F closed output input wave

theorem coefficients_supported (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (wave : IntegerWavevector) (outside : wave ∉ F+F)
    (output input : Coordinate) : coefficients seed time F wave output input = 0 := by
  rw [coefficients_original seed time F closed]
  have zero (shift : ℝ) : NativeCompleteStressCarrier.read
      (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) wave output input = 0 := by
    rw [NativeUnheatedWindowStress.finiteStress,NativeCompleteStressBilinear.mixed_read,NativeHigherTimeJets.mixedFlux]
    have empty : (∑' first, NativeUnheatedWindowStress.projection seed F (time-shift) first input*
        NativeUnheatedWindowStress.projection seed F (time-shift) (wave-first) output) = 0 := by
      apply Eq.trans (b := ∑' _ : IntegerWavevector, (0 : ℂ)) _ tsum_zero
      apply tsum_congr
      intro first
      by_cases member : first ∈ F
      · have last : wave-first ∉ F := by
          intro present
          exact outside (Finset.mem_add.mpr ⟨first,member,wave-first,present,by abel⟩)
        simp [NativeUnheatedWindowStress.projection,last]
      · simp [NativeUnheatedWindowStress.projection,member]
    rw [empty,neg_zero]
  simp only [zero,integral_zero,neg_zero]

theorem stress_field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteSequence (F+F)
      (fun wave => coefficients seed time F wave output input)) =
      ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (stress seed time F output input)).toLp 2 volume ℂ := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  rw [NativeWindowStressHeatEnergy.field,LinearIsometryEquiv.apply_symm_apply]
  ext wave
  rw [NativeWindowStressHeatEnergy.finiteSequence_apply,UnitAddTorus.mFourierBasis_repr,UnitAddTorus.mFourierCoeff_toLp]
  change (if wave ∈ F+F then coefficients seed time F wave output input else 0) =
    UnitAddTorus.mFourierCoeff (fun point => (stress seed time F output input point : ℂ)) wave
  rw [← fourierRead_apply]
  by_cases inside : wave ∈ F+F
  · rw [if_pos inside]; rfl
  · rw [if_neg inside]
    exact (coefficients_supported seed time F closed wave inside output input).symm

theorem cube_closed (radius : ℕ) (wave : IntegerWavevector)
    (member : wave ∈ ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius) :
    waveNeg wave ∈ ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius := by
  rw [ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube,Fintype.mem_piFinset] at member ⊢
  intro coordinate
  have bounds := Finset.mem_Icc.mp (member coordinate)
  exact Finset.mem_Icc.mpr ⟨by simpa [waveNeg] using neg_le_neg bounds.2,
    by simpa [waveNeg] using neg_le_neg bounds.1⟩

theorem cube_stress_field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (radius : ℕ) (output input : Coordinate) :
    let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius
    NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteSequence (F+F)
      (fun wave => coefficients seed time F wave output input)) =
      ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (stress seed time F output input)).toLp 2 volume ℂ :=
  stress_field seed time _ (cube_closed radius) output input

theorem stress_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : stress seed (step.2.clockAdvance+time) F = stress step.1 time F := by
  funext output input
  unfold stress
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift inside
  rw [add_sub_assoc,NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) (by linarith)]

end
end SaturationMonoid.NavierStokes.NativeWindowFiniteGramFourier

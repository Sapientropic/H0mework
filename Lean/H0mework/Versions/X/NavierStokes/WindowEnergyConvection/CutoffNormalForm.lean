import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffWindow
import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffNormalForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeWindowConvectionCutoffAction
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def relative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowPressureStrainHistory.relative seed F radius time output input+primitiveField seed F 0 time output input

def correction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowPressureStrainHistory.correction seed F radius time output input-primitiveField seed F 0 time output input

def correctionJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowJointNormalForm.correctionJet seed F radius order time output input-primitiveField seed F order time output input

def heatRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowJointNormalForm.heatRate seed F radius time output input-viscous seed F time output input

def retainedRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  physical (NativeWindowRetainedAction.lowWindow seed time F (F∩wholeRestartModes radius) output input)+
    physical (strainWindow seed F time output input)-NativeWindowRetainedPressure.remainderField seed F radius time output input

def sourceRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  heatRate seed F radius time output input+retainedRate seed F radius time output input+
    physical (NativeWindowStressPreparationAction.correction seed time F output input)-correctionJet seed F radius 1 time output input

def rawRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowJointNormalForm.rawRate seed F radius time output input+primitiveField seed F 1 time output input

theorem relative_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : relative seed F radius time output input=
      NativeWindowStressHeatBalance.sigma seed F output input time-correction seed F radius time output input := by
  unfold relative correction NativeWindowPressureStrainHistory.relative
  abel

theorem relative_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : HasDerivAt (fun t => relative seed F radius t output input)
      (rawRate seed F radius time output input) time :=
  (NativeWindowJointNormalForm.relative_derivative seed F radius time output input).add (primitiveField_hasDerivAt seed F 0 time output input)

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0 ≤ time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    HasDerivAt (fun t => relative seed F radius t output input) (sourceRate seed F radius time output input) time := by
  have source := (NativeWindowJointNormalForm.source_hasDerivAt seed F radius time nonnegative closed output input).add
    (primitiveField_hasDerivAt seed F 0 time output input)
  convert! source using 1
  simp only [sourceRate,heatRate,retainedRate,correctionJet,viscous_original seed F closed time nonnegative,
    NativeWindowJointNormalForm.sourceRate,NativeWindowJointNormalForm.retainedRate]
  abel

theorem rawRate_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (output input : Coordinate) : Continuous (fun time => rawRate seed F radius time output input) :=
  (NativeWindowJointNormalForm.rawRate_continuous seed F radius output input).add
    (continuous_iff_continuousAt.mpr fun time => (primitiveField_hasDerivAt seed F 1 time output input).continuousAt)

theorem sourceRate_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0 ≤ time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    sourceRate seed F radius time output input=rawRate seed F radius time output input :=
  (source_hasDerivAt seed F radius time nonnegative closed output input).unique (relative_derivative seed F radius time output input)

theorem whole_source_write (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (closed : ∀ k,k∈F →waveNeg k∈F) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    relative seed F radius b-relative seed F radius a=∫ time in a..b,sourceRate seed F radius time := by
  have derivative (time : ℝ) : HasDerivAt (relative seed F radius) (rawRate seed F radius time) time :=
    hasDerivAt_pi.mpr fun output => hasDerivAt_pi.mpr fun input => relative_derivative seed F radius time output input
  have continuous : Continuous (rawRate seed F radius) :=
    continuous_pi fun output => continuous_pi fun input => rawRate_continuous seed F radius output input
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time) (continuous.intervalIntegrable a b)
  refine actual.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro time inside
  funext output input
  exact (sourceRate_original seed F radius time ((le_min a0 b0).trans inside.1) closed output input).symm

def coefficients (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (k : IntegerWavevector) (output input : Coordinate) : ℂ :=
  NativeWindowJointHeat.coefficients seed F radius time k output input-NativeWindowConvectionCutoffWindow.primitive seed F 0 time output input k

theorem combined_sequence (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)=
      finiteSequence (frequencies F) (fun k => NativeWindowJointHeat.coefficients seed F radius time k output input)-
        NativeWindowConvectionCutoffWindow.primitive seed F 0 time output input := by
  apply lp.ext
  funext k
  simp only [finiteSequence_apply,lp.coeFn_sub,Pi.sub_apply,coefficients]
  split_ifs with inside
  · rfl
  · rw [primitive_supported seed F 0 time output input k inside,sub_self]

theorem combined_field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    field (finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input))=
      physical (NativeWindowFiniteGramFourier.stress seed time F output input)+correction seed F radius time output input := by
  rw [combined_sequence]
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (_-_) = _
  rw [map_sub]
  change field _-primitiveField seed F 0 time output input=_
  rw [NativeWindowJointHeat.combined_field seed F radius time closed output input,correction]
  abel

theorem relative_field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) : relative seed F radius time output input=
      -field (finiteSequence (frequencies F) (fun k => coefficients seed F radius time k output input)) := by
  rw [combined_field seed F radius time closed output input,relative_original,NativeWindowStressHeatBalance.sigma]
  abel

theorem heat_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) : heatRate seed F radius time output input=
      -nu.coeff • (∑ j : Coordinate,field (finiteJet (frequencies F) (fun k => coefficients seed F radius time k output input) j 2))+
        (2*nu.coeff) • physical (NativeWindowStressHeatSource.diffusion seed time F output input) := by
  rw [heatRate,NativeWindowJointHeat.heat_original seed F radius time closed output input]
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  have scaling (scalar : ℝ) (value : ScalarField) : (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (scalar • value)=
      scalar • (UnitAddTorus.mFourierBasis (d := Coordinate)).repr value :=
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.restrictScalars ℝ).map_smul scalar value
  simp only [map_sub,map_add,scaling,lp.coeFn_sub,lp.coeFn_add,lp.coeFn_smul,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
    NativeWindowHighTransportHeat.laplacian_fourier]
  have visc := viscous_fourier seed F time output input k
  rw [← UnitAddTorus.mFourierBasis_repr] at visc
  rw [visc,combined_sequence]
  simp only [lp.coeFn_sub,Pi.sub_apply,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul]
  ring

theorem correctionJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : correctionJet seed F radius 0 time output input=correction seed F radius time output input := by
  rw [correctionJet,NativeWindowJointNormalForm.correctionJet_zero]
  rfl

theorem correctionJet_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ cutoff ≥ low,∀ time,time∈Icc 0 horizon →∀ output input,
      ‖correctionJet seed (integerWaveFrequencyCube cutoff) radius order time output input‖<epsilon := by
  obtain ⟨old,oldBound⟩ := NativeWindowJointNormalForm.correctionJet_small seed order horizon nonnegative (epsilon/2) (by positivity)
  obtain ⟨cut,cutBound⟩ := NativeWindowConvectionCutoffWindow.primitive_small seed order horizon nonnegative (epsilon/2) (by positivity)
  refine ⟨max old cut,fun radius above cutoff covered time inside output input => ?_⟩
  have first := oldBound radius ((le_max_left _ _).trans above) (integerWaveFrequencyCube cutoff) time inside output input
  have last := cutBound cutoff ((le_max_right _ _).trans covered) time inside output input
  rw [← primitiveField_norm] at last
  apply (norm_sub_le _ _).trans_lt
  linarith only [first,last]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem whole_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    relative seed F radius (step.2.clockAdvance+time)=relative step.1 F radius time := by
  funext output input
  simp only [relative,NativeWindowPressureStrainHistory.relative_next seed step generated radius time nonnegative F,
    primitiveField,NativeWindowConvectionCutoffWindow.primitive_next seed F 0 step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffNormalForm

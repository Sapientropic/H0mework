import H0mework.Versions.X.NavierStokes.WindowEnergyJoint.Heat

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowJointEnergyGate
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeWindowPressureStrainHistory (correction relative jointWork)
open NativeWindowFiniteGramFourier (fourierRead)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def lowRow (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) : ℂ :=
  ∫ shift,NativeForwardWindowSource.kernel shift • fourierRead k
    (NativeWindowRetainedPressure.sourceLow seed radius F (time-shift) output input)

theorem strain_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    Integrable (fun shift => NativeForwardWindowSource.kernel shift • NativeWindowHighPressureCurrent.strainRow
      (NativeWindowHighPressureCurrent.value seed radius (time-shift)) F k output input) := by
  have source := (fourierRead k).integrable_comp
    (NativeWindowPressureStrainHistory.strain_integrable seed radius time F output input)
  have actual : Integrable (fun shift => NativeWindowHighPressureCurrent.strainRow
      (NativeWindowHighPressureCurrent.value seed radius (time-shift)) F k output input)
      NativeForwardWindowPairingReadout.averageMeasure := by
    apply source.congr
    filter_upwards with shift
    exact NativeWindowPressureStrainPhysical.source_strain_fourier seed radius (time-shift) F closed output input k
  exact (integrable_withDensity_iff_integrable_smul NativeForwardWindowPairingReadout.density_measurable).mp actual

theorem low_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    Integrable (fun shift => NativeForwardWindowSource.kernel shift • fourierRead k
      (NativeWindowRetainedPressure.sourceLow seed radius F (time-shift) output input)) := by
  have paid := (NativeWindowRetainedPressure.remainder_integrable seed F closed radius time output input k).sub
    (strain_integrable seed F closed radius time output input k)
  apply paid.congr
  filter_upwards with shift
  simp only [NativeWindowRetainedPressure.remainderRow,smul_add,Pi.sub_apply,add_sub_cancel_right]

theorem remainderWindow_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    NativeWindowRetainedPressure.remainderWindow seed F radius time output input k=
      lowRow seed F radius time output input k+fourierRead k
        (NativeWindowPressureStrainHistory.window seed radius time F output input) := by
  rw [NativeWindowPressureStrainHistory.window_fourier seed radius time F closed,
    NativeForwardWindowPairingReadout.density_integral]
  simp only [NativeWindowRetainedPressure.remainderWindow,NativeWindowRetainedPressure.remainderRow,smul_add]
  exact integral_add (low_integrable seed F closed radius time output input k)
    (strain_integrable seed F closed radius time output input k)

theorem low_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate)
    (k : IntegerWavevector) (outside : k∉F+F) : lowRow seed F radius time output input k=0 := by
  simp only [lowRow,NativeWindowRetainedPressure.low_supported seed F closed radius _ output input k outside,
    smul_zero,integral_zero]

def lowPressureField (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  field (finiteSequence (F+F) (lowRow seed F radius time output input))

theorem lowPressureField_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (lowPressureField seed F radius time output input) k=lowRow seed F radius time output input k := by
  rw [lowPressureField,field_fourier,finiteSequence_apply]
  split_ifs with inside
  · rfl
  · exact (low_supported seed F closed radius time output input k inside).symm

theorem remainderField_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) :
    NativeWindowRetainedPressure.remainderField seed F radius time output input=
      lowPressureField seed F radius time output input+
        NativeWindowStressHeatSource.physical (NativeWindowPressureStrainHistory.window seed radius time F output input) := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  simp only [map_add,lp.coeFn_add,Pi.add_apply,UnitAddTorus.mFourierBasis_repr]
  rw [NativeWindowRetainedPressure.remainderField_fourier seed F closed radius,lowPressureField_fourier seed F closed radius,
    remainderWindow_split seed F closed radius]
  congr 1
  change fourierRead k _=UnitAddTorus.mFourierCoeff
    (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) _).toLp 2 volume ℂ) k
  rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
  rfl

def lowAdvWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical
      (NativeWindowRetainedAction.lowWindow seed time F (F∩wholeRestartModes radius) output input))

def convectionWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  -(∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowRetainedAction.convectionWindow seed time F output input)))

def lowPressureWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  -(∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (lowPressureField seed F radius time output input))

theorem retainedWork_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) :
    NativeWindowJointNormalForm.retainedWork seed F radius time=
      lowAdvWork seed F radius time+convectionWork seed F radius time+lowPressureWork seed F radius time-
        ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
          (NativeWindowStressHeatSource.physical (NativeWindowPressureStrainHistory.window seed radius time F output input)) := by
  simp only [NativeWindowJointNormalForm.retainedWork,NativeWindowJointNormalForm.retainedRate,
    remainderField_split seed F closed radius,inner_sub_right,inner_add_right,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,lowAdvWork,convectionWork,lowPressureWork]
  ring

theorem joint_generator (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) :
    NativeWindowJointNormalForm.heatWork seed F radius time+NativeWindowJointNormalForm.retainedWork seed F radius time=
      -nu.coeff*NativeWindowJointHeat.dirichlet seed F radius time-
        2*nu.coeff*(∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)+
          lowAdvWork seed F radius time+convectionWork seed F radius time+lowPressureWork seed F radius time+
            jointWork seed F radius time := by
  rw [NativeWindowJointHeat.heatWork_identity seed F radius time closed,retainedWork_split seed F closed radius]
  simp only [jointWork,NativeWindowJointHeat.crossWork]
  ring

theorem energy_balance (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (nonnegative : 0≤time) :
    deriv (NativeWindowJointNormalForm.energy seed F radius) time+
      nu.coeff*NativeWindowJointHeat.dirichlet seed F radius time+
        2*nu.coeff*(∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)=
          lowAdvWork seed F radius time+convectionWork seed F radius time+lowPressureWork seed F radius time+
            jointWork seed F radius time+NativeWindowJointNormalForm.preparationWork seed F radius time-
              NativeWindowJointNormalForm.timeWork seed F radius time := by
  rw [(NativeWindowJointNormalForm.energy_generator seed F radius time nonnegative closed).deriv,
    joint_generator seed F closed radius time]
  ring

theorem source_energy_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      (∀ k,k∈F →waveNeg k∈F) →deriv (NativeWindowJointNormalForm.energy seed F radius) time+
        nu.coeff*NativeWindowJointHeat.dirichlet seed F radius time+
          2*nu.coeff*(∫ point : Torus,NativeWindowStressHeatSource.interaction seed time F point)≤
            lowAdvWork seed F radius time+convectionWork seed F radius time+lowPressureWork seed F radius time+
              jointWork seed F radius time+NativeWindowJointNormalForm.preparationWork seed F radius time+
                NativeWindowJointNormalForm.energy seed F radius time+epsilon := by
  obtain ⟨low,paid⟩ := NativeWindowJointNormalForm.energy_uniform_feed seed horizon nonnegative epsilon positive
  refine ⟨low,fun radius above F time inside closed => ?_⟩
  have source := paid radius above F time inside closed
  rw [joint_generator seed F closed radius time] at source
  linarith only [source]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem lowPressureField_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    lowPressureField seed F radius (step.2.clockAdvance+time)=lowPressureField step.1 F radius time := by
  have actual := congrArg Prod.snd (NativeWindowRetainedPressure.whole_next seed step generated time nonnegative F closed radius)
  change NativeWindowRetainedPressure.remainderField seed F radius (step.2.clockAdvance+time)=
    NativeWindowRetainedPressure.remainderField step.1 F radius time at actual
  funext output input
  have before := remainderField_split seed F closed radius (step.2.clockAdvance+time) output input
  rw [actual,NativeWindowPressureStrainHistory.window_next seed step generated radius time nonnegative F] at before
  exact add_right_cancel (before.symm.trans (remainderField_split step.1 F closed radius time output input))

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    (lowAdvWork seed F radius (step.2.clockAdvance+time),convectionWork seed F radius (step.2.clockAdvance+time),
      lowPressureWork seed F radius (step.2.clockAdvance+time))=
        (lowAdvWork step.1 F radius time,convectionWork step.1 F radius time,lowPressureWork step.1 F radius time) := by
  have source := NativeWindowRetainedAction.whole_next seed step generated time nonnegative F (F∩wholeRestartModes radius)
  have low := congrArg Prod.fst source
  have convective := congrArg (fun data => data.2.1) source
  change NativeWindowRetainedAction.lowWindow seed (step.2.clockAdvance+time) F (F∩wholeRestartModes radius)=
    NativeWindowRetainedAction.lowWindow step.1 time F (F∩wholeRestartModes radius) at low
  change NativeWindowRetainedAction.convectionWindow seed (step.2.clockAdvance+time) F=
    NativeWindowRetainedAction.convectionWindow step.1 time F at convective
  simp only [lowAdvWork,convectionWork,lowPressureWork,
    NativeWindowPressureStrainHistory.relative_next seed step generated radius time nonnegative F,low,convective,
    lowPressureField_next seed F closed radius step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowJointEnergyGate

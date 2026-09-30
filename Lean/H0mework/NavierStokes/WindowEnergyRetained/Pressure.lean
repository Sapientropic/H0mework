import H0mework.NavierStokes.WindowEnergyRetained.Action
import H0mework.NavierStokes.WindowEnergyHighPressure.Physical
import H0mework.NavierStokes.WindowEnergyHighPressure.Resolvent

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowRetainedPressure
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeEndpointVelocityCarrier NativeWindowPressureSectors
open NativeWindowHighPressurePhysical (realSynthesis realSynthesis_sub)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def trilinear (left right last : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  realSynthesis F (fun k => force left right k output)*realSynthesis F (fun k => last k input)+
    realSynthesis F (fun k => force left right k input)*realSynthesis F (fun k => last k output)

theorem diagonal (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (output input : Coordinate) :
    trilinear value value value F output input=NativeWindowHighPressurePhysical.pressurePair value F output input := rfl

theorem sectors (value low : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (output input : Coordinate) :
    trilinear value value value F output input=
      (2 : ℝ) • trilinear low value value F output input-trilinear low low value F output input+
        trilinear (value-low) (value-low) low F output input+
          trilinear (value-low) (value-low) (value-low) F output input := by
  simp only [trilinear,force_sub_left,force_sub_right,force_swap value low,lp.coeFn_sub,Pi.sub_apply,realSynthesis_sub]
  ext point
  simp only [ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

def lowPair (value low : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  (2 : ℝ) • trilinear low value value F output input-trilinear low low value F output input+
    trilinear (value-low) (value-low) low F output input

theorem pressure_split (value low : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (output input : Coordinate) :
    NativeWindowHighPressurePhysical.pressurePair value F output input=
      lowPair value low F output input+NativeWindowHighPressurePhysical.pressurePair (value-low) F output input :=
  sectors value low F output input

theorem original_pressure_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ,∀ output input,NativeWindowRetainedAction.pressurePair seed F output input time=
      NativeWindowHighPressurePhysical.pressurePair (NativeWindowHighPressureCurrent.velocity seed time) F output input := by
  filter_upwards [NativeWindowRetainedAction.source_pressure_ae seed F] with time actual output input
  simp only [NativeWindowRetainedAction.pressurePair,NativeWindowRetainedAction.pair,actual,
    NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original,
    NativeWindowHighPressurePhysical.pressurePair,NativeWindowHighPressurePhysical.source_read]
  have same : wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst=
      NativeWindowHighPressureCurrent.velocity seed time := rfl
  simp only [same,NativeWindowHighPressurePhysical.realSynthesis]
  ring


def sourceLow (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) : C(Torus,ℝ) :=
  lowPair (NativeWindowHighPressureCurrent.velocity seed time)
    (complexSharpSupportProjection (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius)
      (NativeWindowHighPressureCurrent.velocity seed time)) F output input

theorem original_sectors_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) :
    ∀ᵐ time : ℝ,∀ output input,NativeWindowRetainedAction.pressurePair seed F output input time=
      sourceLow seed radius F time output input+
        NativeWindowHighPressurePhysical.pressurePair (NativeWindowHighPressureCurrent.value seed radius time) F output input := by
  filter_upwards [original_pressure_ae seed F] with time original output input
  rw [original output input,pressure_split _ (complexSharpSupportProjection
    (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius)
      (NativeWindowHighPressureCurrent.velocity seed time))]
  rfl

theorem original_tensor_fourier_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) : ∀ᵐ time : ℝ,∀ output input k,
    NativeWindowFiniteGramFourier.fourierRead k (NativeWindowRetainedAction.pressurePair seed F output input time)=
      NativeWindowFiniteGramFourier.fourierRead k (sourceLow seed radius F time output input)+
        NativeWindowHighPressureCurrent.tensorRow (NativeWindowHighPressureCurrent.value seed radius time) F k output input := by
  filter_upwards [original_sectors_ae seed F radius] with time original output input k
  rw [original output input,map_add,NativeWindowHighPressurePhysical.source_pressurePair_fourier seed radius time F closed]

def divergenceRead (nu : Viscosity) (k : IntegerWavevector) (output input : Coordinate) :
    NativeWindowHighTransportSource.Current →L[ℝ] ℂ :=
  (nu.coeff*integerWaveViscousMultiplier k) •
    (lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 k).comp
      ((NativeWindowHighTransportResolvent.resolve nu output input).restrictScalars ℝ)

theorem divergenceRead_apply (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    divergenceRead nu k output input (NativeWindowHighPressureCurrent.current seed F radius time)=
      NativeWindowHighPressureCurrent.tensorRow (NativeWindowHighPressureCurrent.value seed radius time) F k output input-
        NativeWindowHighPressureCurrent.strainRow (NativeWindowHighPressureCurrent.value seed radius time) F k output input := by
  change (nu.coeff*integerWaveViscousMultiplier k : ℝ) •
    NativeWindowHighTransportResolvent.resolve nu output input (NativeWindowHighPressureCurrent.current seed F radius time) k=_
  rw [NativeWindowHighTransportResolvent.viscous_row]
  exact eq_sub_of_add_eq (NativeWindowHighPressureCurrent.pressure_decomposition
    (NativeWindowHighPressureCurrent.value seed radius time) F k output input).symm

/-- Original low pressure sectors and the full high pressure strain remain literal source terms. -/
def remainderRow (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) : ℂ :=
  NativeWindowFiniteGramFourier.fourierRead k (sourceLow seed radius F time output input)+
    NativeWindowHighPressureCurrent.strainRow (NativeWindowHighPressureCurrent.value seed radius time) F k output input

theorem original_remainder_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) : ∀ᵐ time : ℝ,∀ output input k,
    NativeWindowFiniteGramFourier.fourierRead k (NativeWindowRetainedAction.pressurePair seed F output input time)=
      divergenceRead nu k output input (NativeWindowHighPressureCurrent.current seed F radius time)+
        remainderRow seed radius F time output input k := by
  filter_upwards [original_tensor_fourier_ae seed F closed radius] with time original output input k
  rw [original output input k,divergenceRead_apply,remainderRow]
  abel

theorem divergence_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) : Integrable (fun shift =>
      NativeForwardWindowSource.kernel shift • divergenceRead nu k output input
        (NativeWindowHighPressureCurrent.current seed F radius (time-shift))) := by
  have source := (divergenceRead nu k output input).integrable_comp
    (NativeWindowHighPressureResolvent.window_integrable seed F radius 0 time)
  simpa only [map_smul,NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using source

theorem pressure_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) : Integrable (fun shift =>
      NativeForwardWindowSource.kernel shift • NativeWindowFiniteGramFourier.fourierRead k
        (NativeWindowRetainedAction.pressurePair seed F output input (time-shift))) := by
  have source := (NativeWindowFiniteGramFourier.fourierRead k).integrable_comp
    (NativeWindowRetainedAction.pressurePair_integrable seed time F output input)
  exact (integrable_withDensity_iff_integrable_smul NativeForwardWindowPairingReadout.density_measurable).mp source

theorem remainder_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    Integrable (fun shift => NativeForwardWindowSource.kernel shift • remainderRow seed radius F (time-shift) output input k) := by
  have source := (pressure_integrable seed F time output input k).sub (divergence_integrable seed F radius time output input k)
  apply source.congr
  filter_upwards [(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    (original_remainder_ae seed F closed radius)] with shift original
  simp only [Pi.sub_apply,original output input k,smul_add,add_sub_cancel_left]

def remainderWindow (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) : ℂ :=
  ∫ shift,NativeForwardWindowSource.kernel shift • remainderRow seed radius F (time-shift) output input k

theorem pressureWindow_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    NativeWindowFiniteGramFourier.fourierRead k (NativeWindowRetainedAction.pressureWindow seed time F output input)=
      (nu.coeff*integerWaveViscousMultiplier k : ℝ) •
        NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input k+
          remainderWindow seed F radius time output input k := by
  rw [NativeWindowRetainedAction.pressureWindow,← (NativeWindowFiniteGramFourier.fourierRead k).integral_comp_comm
    (NativeWindowRetainedAction.pressurePair_integrable seed time F output input),NativeForwardWindowPairingReadout.density_integral]
  have same : (fun shift => NativeForwardWindowSource.kernel shift • NativeWindowFiniteGramFourier.fourierRead k
      (NativeWindowRetainedAction.pressurePair seed F output input (time-shift))) =ᵐ[volume]
      fun shift => NativeForwardWindowSource.kernel shift • divergenceRead nu k output input
        (NativeWindowHighPressureCurrent.current seed F radius (time-shift))+
          NativeForwardWindowSource.kernel shift • remainderRow seed radius F (time-shift) output input k := by
    filter_upwards [(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
      (original_remainder_ae seed F closed radius)] with shift original
    rw [original output input k,smul_add]
  rw [integral_congr_ae same,integral_add (divergence_integrable seed F radius time output input k)
    (remainder_integrable seed F closed radius time output input k)]
  congr 1
  simp only [divergenceRead_apply]
  simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using
    (NativeWindowHighPressureResolvent.primitive_equation seed F radius 0 time output input k).symm

private theorem absent_pair (F : Finset IntegerWavevector) (k : IntegerWavevector) (outside : k∉F+F)
    (q : IntegerWavevector) (member : q∈F) : k-q∉F := by
  intro inside
  exact outside (Finset.mem_add.mpr ⟨k-q,inside,q,member,sub_add_cancel k q⟩)

theorem tensor_supported (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) (k : IntegerWavevector) (outside : k∉F+F) :
    NativeWindowHighPressureCurrent.tensorRow value F k output input=0 := by
  apply Finset.sum_eq_zero
  intro q member
  exact if_neg (absent_pair F k outside q member)

theorem strain_supported (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) (k : IntegerWavevector) (outside : k∉F+F) :
    NativeWindowHighPressureCurrent.strainRow value F k output input=0 := by
  apply Finset.sum_eq_zero
  intro q member
  rw [NativeWindowHighPressureCurrent.scalarRow,if_neg (absent_pair F k outside q member),zero_mul]

theorem low_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate)
    (k : IntegerWavevector) (outside : k∉F+F) :
    NativeWindowFiniteGramFourier.fourierRead k (sourceLow seed radius F time output input)=0 := by
  have reality : FiniteStateFourierReality (NativeWindowHighPressureCurrent.velocity seed time) :=
    wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality
  have actual := congrArg (NativeWindowFiniteGramFourier.fourierRead k) (pressure_split
    (NativeWindowHighPressureCurrent.velocity seed time)
    (complexSharpSupportProjection (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius)
      (NativeWindowHighPressureCurrent.velocity seed time)) F output input)
  rw [map_add,NativeWindowHighPressurePhysical.pressurePair_fourier _ reality F closed] at actual
  change NativeWindowHighPressureCurrent.tensorRow _ F k output input=
    NativeWindowFiniteGramFourier.fourierRead k (sourceLow seed radius F time output input)+
      NativeWindowFiniteGramFourier.fourierRead k
        (NativeWindowHighPressurePhysical.pressurePair (NativeWindowHighPressureCurrent.value seed radius time) F output input) at actual
  rw [NativeWindowHighPressurePhysical.source_pressurePair_fourier seed radius time F closed,
    tensor_supported _ F output input k outside,tensor_supported _ F output input k outside,add_zero] at actual
  exact actual.symm

theorem remainder_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate)
    (k : IntegerWavevector) (outside : k∉F+F) : remainderWindow seed F radius time output input k=0 := by
  simp only [remainderWindow,remainderRow,low_supported seed F closed radius _ output input k outside,
    strain_supported _ F output input k outside,add_zero,smul_zero,integral_zero]

theorem viscous_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) (outside : k∉F+F) :
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) •
      NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input k=0 := by
  rw [NativeWindowHighPressureResolvent.primitive_equation]
  simp only [tensor_supported _ F output input k outside,strain_supported _ F output input k outside,
    sub_self,smul_zero,integral_zero]

def remainderField (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteSequence (F+F)
    (remainderWindow seed F radius time output input))

def viscousPrimitive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatEnergy.field (NativeWindowStressHeatEnergy.finiteSequence (F+F)
    (fun k => (nu.coeff*integerWaveViscousMultiplier k : ℝ) •
      NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input k))

theorem remainderField_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (remainderField seed F radius time output input) k=remainderWindow seed F radius time output input k := by
  rw [remainderField,NativeWindowStressHeatEnergy.field_fourier,NativeWindowStressHeatEnergy.finiteSequence_apply]
  split_ifs with inside
  · rfl
  · exact (remainder_supported seed F closed radius time output input k inside).symm

theorem viscousPrimitive_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (viscousPrimitive seed F radius time output input) k=
      (nu.coeff*integerWaveViscousMultiplier k : ℝ) •
        NativeWindowHighPressureResolvent.primitive seed F radius 0 time output input k := by
  rw [viscousPrimitive,NativeWindowStressHeatEnergy.field_fourier,NativeWindowStressHeatEnergy.finiteSequence_apply]
  split_ifs with inside
  · rfl
  · exact (viscous_supported seed F radius time output input k inside).symm

theorem pressureWindow_physical (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) :
    NativeWindowStressHeatSource.physical (NativeWindowRetainedAction.pressureWindow seed time F output input)=
      viscousPrimitive seed F radius time output input+remainderField seed F radius time output input := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  simp only [map_add,lp.coeFn_add,Pi.add_apply,UnitAddTorus.mFourierBasis_repr]
  rw [remainderField_fourier seed F closed radius,viscousPrimitive_fourier]
  have original (f : C(Torus,ℝ)) : UnitAddTorus.mFourierCoeff (NativeWindowStressHeatSource.physical f) k=
      NativeWindowFiniteGramFourier.fourierRead k f := by
    change UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) f).toLp 2 volume ℂ) k=_
    rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
    rfl
  rw [original,pressureWindow_fourier seed F closed radius]

theorem sigma_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (F A : Finset IntegerWavevector) (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) (output input : Coordinate) :
    HasDerivAt (NativeWindowStressHeatBalance.sigma seed F output input)
      (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)+
        NativeWindowStressHeatSource.physical (NativeWindowHighTransportForcing.highWindow seed time F A output input)+
        NativeWindowStressHeatSource.physical (NativeWindowRetainedAction.lowWindow seed time F A output input)-
        NativeWindowStressHeatSource.physical (NativeWindowRetainedAction.convectionWindow seed time F output input)-
        viscousPrimitive seed F radius time output input-remainderField seed F radius time output input+
        NativeWindowStressHeatSource.physical (NativeWindowStressPreparationAction.correction seed time F output input)) time := by
  have source := NativeWindowRetainedAction.sigma_hasDerivAt seed time nonnegative F A closed output input
  rw [pressureWindow_physical seed F closed radius] at source
  convert! source using 1
  abel

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem viscousPrimitive_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    viscousPrimitive seed F radius (step.2.clockAdvance+time)=viscousPrimitive step.1 F radius time := by
  funext output input
  simp only [viscousPrimitive,NativeWindowHighPressureResolvent.primitive_next seed F radius 0 step generated time nonnegative]

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (F : Finset IntegerWavevector) (closed : ∀ k,k∈F → waveNeg k∈F) (radius : ℕ) :
    (viscousPrimitive seed F radius (step.2.clockAdvance+time),remainderField seed F radius (step.2.clockAdvance+time))=
      (viscousPrimitive step.1 F radius time,remainderField step.1 F radius time) := by
  refine Prod.ext (viscousPrimitive_next seed step generated time nonnegative F radius) ?_
  have original := congrArg (fun p => p.2.2) (NativeWindowRetainedAction.whole_next seed step generated time nonnegative F ∅)
  change NativeWindowRetainedAction.pressureWindow seed (step.2.clockAdvance+time) F=
    NativeWindowRetainedAction.pressureWindow step.1 time F at original
  funext output input
  have before := pressureWindow_physical seed F closed radius (step.2.clockAdvance+time) output input
  have after := pressureWindow_physical step.1 F closed radius time output input
  rw [original,viscousPrimitive_next seed step generated time nonnegative F radius] at before
  exact add_left_cancel (before.symm.trans after)

end
end SaturationMonoid.NavierStokes.NativeWindowRetainedPressure

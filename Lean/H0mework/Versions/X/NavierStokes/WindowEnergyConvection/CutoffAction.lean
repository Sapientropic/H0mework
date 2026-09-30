import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffWindow
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Evolution

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeForwardWindowPairingReadout NativeCompleteStressAction
open NativeWindowConvectionCutoffPhysical
open NativeWindowCrossHistoryAction (velocity gradient)
open NativeWindowConvectionCutoffWindow (primitive)
open NativeWindowStressHeatEnergy (finiteSequence finiteSequence_apply field_fourier)
open NativeWindowHighTransportRelative (fieldCLM)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

abbrev frequencies := NativeWindowJointHeat.frequencies

def filteredCLM (F : Finset IntegerWavevector) (output input : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  ∑ k∈F,(NativeWindowStressHeatBalance.basis k).comp (stressRead k output input)

theorem filteredCLM_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) : filteredCLM F output input (NativeUnifiedCompleteSource.source seed time)=
      filtered seed F time output input := by
  simp only [filteredCLM,filtered,NativeWindowHighPressurePhysical.realSynthesis,sum_apply,ContinuousLinearMap.comp_apply]

theorem field_raw (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (output input : Coordinate) :
    NativeWindowConvectionCutoffPhysical.field seed F time output input=
      filteredCLM F output input (NativeUnifiedCompleteSource.source seed time)+
        NativeWindowFiniteGramFourier.read F output (NativeUnifiedCompleteSource.source seed time)*
          NativeWindowFiniteGramFourier.read F input (NativeUnifiedCompleteSource.source seed time) := by
  simp only [filteredCLM_original,NativeWindowConvectionCutoffPhysical.field,velocity,NativeWindowStressHeatTime.field_original]

theorem field_memLp (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (output input : Coordinate) :
    MemLp (fun shift => NativeWindowConvectionCutoffPhysical.field seed F (time-shift) output input) ∞ averageMeasure := by
  simp_rw [field_raw]
  have quadratic := (NativeWindowLowAdvectorHistory.read_memLp seed time (NativeWindowFiniteGramFourier.read F input)).mul' (r := ∞)
    (NativeWindowLowAdvectorHistory.read_memLp seed time (NativeWindowFiniteGramFourier.read F output))
  convert! MemLp.add (ε := C(Torus,ℝ)) (NativeWindowLowAdvectorHistory.read_memLp seed time (filteredCLM F output input)) quadratic using 1

theorem strain_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (output input : Coordinate) :
    Integrable (fun shift => strain seed F (time-shift) output input) averageMeasure := by
  have row (j o i : Coordinate) : Integrable (fun shift => gradient seed F (time-shift) j o*
      NativeWindowConvectionCutoffPhysical.field seed F (time-shift) i j) averageMeasure := by
    have paid := ((field_memLp seed F time i j).mul (r := ∞)
      (NativeWindowLowAdvectorHistory.read_memLp seed time (NativeWindowStressHeatSource.jetRead F j 1 o))).integrable (by norm_num : (1 : ℝ≥0∞)≤∞)
    simpa only [NativeWindowCrossHistoryAction.gradient,Pi.mul_apply] using! paid
  apply integrable_finsetSum (ε' := C(Torus,ℝ)) Finset.univ
  intro j _
  convert! Integrable.add (ε' := C(Torus,ℝ)) (row j output input) (row j input output) using 1

def strainWindow (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) : C(Torus,ℝ) :=
  ∫ shift,strain seed F (time-shift) output input ∂averageMeasure

theorem current_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (j output input : Coordinate) (k : IntegerWavevector) (outside : k∉frequencies F) :
    NativeWindowConvectionCutoffCurrent.current seed F time j output input k=0 := by
  classical
  have absent : k∉F+(F∪(F+F)) := by simpa only [Finset.add_union,frequencies,NativeWindowHighTransportHeat.frequencies] using outside
  have row (o i : Coordinate) : NativeWindowConvectionCutoffCurrent.productCLM
      (NativeWindowHighTransportSource.vectorRead o (NativeUnheatedWindowStress.projection seed F time))
      (NativeWindowHighTransportSource.tensorRead (i,j) (NativeWindowConvectionCutoffStress.value seed F time)) k=0 := by
    apply NativeWindowHighTransportProduct.product_supported _ _ F (F∪(F+F)) ?_ ?_ k absent
    · intro p absent
      change NativeUnheatedWindowStress.projection seed F time p o=0
      simp [NativeUnheatedWindowStress.projection,complexSharpSupportProjection_apply,absent]
    · intro p absent
      change NativeWindowConvectionCutoffStress.value seed F time p (i,j)=0
      rw [NativeWindowConvectionCutoffStress.value_supported seed F time p absent]
      rfl
  change _+_=(0 : ℂ)
  rw [row output input,row input output,add_zero]

theorem window_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ) (time : ℝ)
    (j output input : Coordinate) (k : IntegerWavevector) (outside : k∉frequencies F) :
    NativeWindowConvectionCutoffWindow.window seed F order time j output input k=0 := by
  change NativeWindowHighTransportSource.read j output input k (∫ shift,NativeForwardWindowJets.kernelJet order shift •
    NativeWindowConvectionCutoffCurrent.current seed F (time-shift))=0
  rw [← (NativeWindowHighTransportSource.read j output input k).integral_comp_comm
    (NativeWindowConvectionCutoffWindow.window_integrable seed F order time)]
  simp only [map_smul]
  change (∫ shift,NativeForwardWindowJets.kernelJet order shift •
    NativeWindowConvectionCutoffCurrent.current seed F (time-shift) j output input k)=0
  simp only [current_supported seed F _ j output input k outside,smul_zero,integral_zero]

theorem primitive_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) (outside : k∉frequencies F) :
    primitive seed F order time output input k=0 := by
  change (∑ j : Coordinate,NativeWindowHighTransportResolvent.factor nu j k*
    NativeWindowConvectionCutoffWindow.window seed F order time j output input k)=0
  exact Finset.sum_eq_zero fun j _ => by rw [window_supported seed F order time j output input k outside,mul_zero]

def primitiveField (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField := fieldCLM (primitive seed F order time output input)

theorem primitiveField_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (time : ℝ) (output input : Coordinate) : HasDerivAt (fun t => primitiveField seed F order t output input)
      (primitiveField seed F (order+1) time output input) time :=
  fieldCLM.hasFDerivAt.comp_hasDerivAt time (NativeWindowConvectionCutoffWindow.primitive_hasDerivAt seed F order time output input)

theorem primitiveField_norm (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (time : ℝ) (output input : Coordinate) : ‖primitiveField seed F order time output input‖=‖primitive seed F order time output input‖ :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.norm_map _

def viscous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  fieldCLM (finiteSequence (frequencies F) (fun k => (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F 0 time output input k))

theorem viscous_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) : UnitAddTorus.mFourierCoeff (viscous seed F time output input) k=
      (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F 0 time output input k := by
  change UnitAddTorus.mFourierCoeff (NativeWindowStressHeatEnergy.field _) k=_
  rw [field_fourier,finiteSequence_apply]
  split_ifs with inside
  · rfl
  · rw [primitive_supported seed F 0 time output input k inside,smul_zero]

theorem viscous_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (time : ℝ) (nonnegative : 0 ≤ time) (output input : Coordinate) :
    viscous seed F time output input=physical (NativeWindowRetainedAction.convectionWindow seed time F output input)+
      physical (strainWindow seed F time output input) := by
  have physical_fourier (f : C(Torus,ℝ)) (k : IntegerWavevector) : UnitAddTorus.mFourierCoeff (physical f) k=
      NativeWindowFiniteGramFourier.fourierRead k f := by
    change UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) f).toLp 2 volume ℂ) k=_
    rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
    rfl
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  rw [map_add,lp.coeFn_add,Pi.add_apply,UnitAddTorus.mFourierBasis_repr,UnitAddTorus.mFourierBasis_repr,
    UnitAddTorus.mFourierBasis_repr,viscous_fourier,physical_fourier,physical_fourier]
  rw [NativeWindowRetainedAction.convectionWindow,strainWindow,
    ← (NativeWindowFiniteGramFourier.fourierRead k).integral_comp_comm (NativeWindowRetainedAction.convectionPair_integrable seed time F output input),
    ← (NativeWindowFiniteGramFourier.fourierRead k).integral_comp_comm (strain_integrable seed F time output input),
    ← integral_add ((NativeWindowFiniteGramFourier.fourierRead k).integrable_comp (NativeWindowRetainedAction.convectionPair_integrable seed time F output input))
      ((NativeWindowFiniteGramFourier.fourierRead k).integrable_comp (strain_integrable seed F time output input))]
  simp only [← map_add]
  rw [density_integral]
  change (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F 0 time output input k=
    ∫ shift,NativeForwardWindowJets.kernelJet 0 shift • NativeWindowFiniteGramFourier.fourierRead k
      (NativeWindowRetainedAction.convectionPair seed F output input (time-shift)+strain seed F (time-shift) output input)
  have average := NativeWindowFiniteStressUniform.average_original 0 time time ⟨nonnegative,le_rfl⟩
    (fun sample => NativeWindowFiniteGramFourier.fourierRead k
      (NativeWindowRetainedAction.convectionPair seed F output input sample+strain seed F sample output input))
  exact (NativeWindowConvectionCutoffWindow.primitive_source seed F closed 0 time time ⟨nonnegative,le_rfl⟩ output input k).trans average

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffAction

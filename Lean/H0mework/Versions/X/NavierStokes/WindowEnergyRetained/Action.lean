import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Forcing
import H0mework.Versions.X.NavierStokes.WindowEnergyPressureSectors.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowRetainedAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativePhysicalFourier NativeStressCurlAlgebra
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowPairingReadout
open NativeWindowCrossHistoryAction NativeWindowHighTransportGreen
open NativeWindowStressHeatBalance (basis)
open NativeWindowHighTransportForcing (remainingAction remainingPair)
open NativeWindowPressureSectors (force)
noncomputable section
variable {nu : Viscosity}

def tensorRead (wave : IntegerWavevector) : FullSpace →L[ℝ] NativeFluidStressCoefficient :=
  ContinuousLinearMap.pi fun output => ContinuousLinearMap.pi fun input => stressRead wave output input

def convectionRead (F : Finset IntegerWavevector) (i : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  ∑ wave∈F,(basis wave).comp (((ContinuousLinearMap.proj i).comp
    ((NativeStressCurlAlgebra.stressDivergenceCLM wave).restrictScalars ℝ)).comp (tensorRead wave))

def pressureRead (F : Finset IntegerWavevector) (i : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  ∑ wave∈F,(basis wave).comp ((-NativePhysicalGradient.multiplier wave i) •
    (((NativeCofinalStress.stressPressureCLM wave).restrictScalars ℝ).comp (tensorRead wave)))

theorem tensorRead_apply (value : FullSpace) (wave : IntegerWavevector) :
    tensorRead wave value=NativeCompleteStressCarrier.read value.snd wave := rfl

theorem source_tensor_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,∀ wave,
    tensorRead wave (NativeUnifiedCompleteSource.source seed time)=
      NativeHigherTimeJets.mixedFlux (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave := by
  filter_upwards [NativeUnifiedGlobalStressSource.stress_ae seed] with time original wave
  rw [tensorRead_apply,NativeUnifiedCompleteSource.stress_read,original,NativeUnifiedCompleteSource.velocity_read]
  rfl

theorem convectionRead_apply (F : Finset IntegerWavevector) (i : Coordinate) (value : FullSpace) :
    convectionRead F i value=∑ wave∈F,basis wave
      (nativeFluidStressDivergenceCoefficient (fun wave => tensorRead wave value) wave i) := by
  simp only [convectionRead,sum_apply,ContinuousLinearMap.comp_apply]
  rfl

theorem pressureRead_apply (F : Finset IntegerWavevector) (i : Coordinate) (value : FullSpace) :
    pressureRead F i value=∑ wave∈F,basis wave
      (-NativePhysicalGradient.multiplier wave i*NativeStressCurlAlgebra.stressPressureCoefficient wave (tensorRead wave value)) := by
  simp only [pressureRead,sum_apply,ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul]
  rfl

theorem source_pressure_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ,∀ i,pressureRead F i (NativeUnifiedCompleteSource.source seed time)=
      ∑ wave∈F,basis wave (force (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave i) := by
  filter_upwards [source_tensor_ae seed] with time source i
  rw [pressureRead_apply]
  apply Finset.sum_congr rfl
  intro wave _
  rw [source wave]
  congr 1
  simp only [force,NativePhysicalGradient.multiplier]
  ring

theorem source_action_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ,0<time →∀ i,
      NativeWindowStressPreparationAction.actionRead F i (NativeUnifiedCompleteSource.source seed time)=
        convectionRead F i (NativeUnifiedCompleteSource.source seed time)+pressureRead F i (NativeUnifiedCompleteSource.source seed time) := by
  have same := ae_all_iff.mpr fun i => NativeWindowStressPreparationAction.action_original_ae seed F i
  filter_upwards [same,NativeWindowStressHeatBalance.action_original_ae seed F,
    source_tensor_ae seed,source_pressure_ae seed F] with time prep actual tensor pressure positive i
  rw [prep i positive,actual positive.le i,convectionRead_apply,pressure i,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro wave _
  simp only [tensor,NativeWindowPressureSectors.force_original,map_add]

def lowAdvection (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (time : ℝ) : Vector := advection (velocity seed A time) (gradient seed F time)

/-- The literal unprojected-divergence residual retains all raw convection and cutoff effects. -/
def convectionResidual (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) : Vector := fun i =>
  convectionRead F i (NativeUnifiedCompleteSource.source seed time)+advection (velocity seed F time) (gradient seed F time) i

theorem remainingAction_ae (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ,0<time →∀ i,remainingAction seed F A time i=
      convectionResidual seed F time i+pressureRead F i (NativeUnifiedCompleteSource.source seed time)-lowAdvection seed F A time i := by
  filter_upwards [source_action_ae seed F] with time actual positive i
  rw [remainingAction,actual positive i]
  simp only [convectionResidual,lowAdvection,NativeWindowHighTransportForcing.highAdvection,advection,drift,
    Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]
  abel

def pair (first last : Vector) (output input : Coordinate) : C(Torus,ℝ) :=
  first output*last input+last output*first input

def lowPair (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  pair (lowAdvection seed F A time) (velocity seed F time) output input

def convectionPair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  pair (convectionResidual seed F time) (velocity seed F time) output input

def pressurePair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  pair (fun i => pressureRead F i (NativeUnifiedCompleteSource.source seed time)) (velocity seed F time) output input

theorem remainingPair_ae (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ,0<time →∀ output input,remainingPair seed F A output input time=
      lowPair seed F A output input time-convectionPair seed F output input time-pressurePair seed F output input time := by
  filter_upwards [remainingAction_ae seed F A] with time actual positive output input
  ext point
  simp only [remainingPair,actual positive,lowPair,convectionPair,pressurePair,pair,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.neg_apply,ContinuousMap.mul_apply]
  ring

private theorem empty_velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : velocity seed ∅ time=0 := by
  funext i
  simp [velocity,NativeWindowStressHeatTime.field_original,NativeWindowFiniteGramFourier.read,
    NativeWindowFiniteGramFourier.complexRead]

theorem lowPair_split (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : lowPair seed F A output input time=
      NativeWindowHighTransportForcing.highPair seed F ∅ output input time-
        NativeWindowHighTransportForcing.highPair seed F A output input time := by
  simp only [lowPair,pair,lowAdvection,NativeWindowHighTransportForcing.highPair,
    NativeWindowHighTransportForcing.highAdvection,drift,empty_velocity,advection,Pi.sub_apply,Pi.zero_apply,sub_zero,
    sub_mul,Finset.sum_sub_distrib]
  ring

theorem lowPair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector)
    (output input : Coordinate) : Integrable (fun shift => lowPair seed F A output input (time-shift)) averageMeasure := by
  simp only [lowPair_split]
  convert! Integrable.sub (β := C(Torus,ℝ))
    (NativeWindowHighTransportForcing.highPair_integrable seed time F ∅ output input)
    (NativeWindowHighTransportForcing.highPair_integrable seed time F A output input) using 1

theorem pressurePair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : Integrable (fun shift => pressurePair seed F output input (time-shift)) averageMeasure := by
  unfold pressurePair pair
  convert! Integrable.add (ε' := C(Torus,ℝ)) ?_ ?_ using 1
  · simpa only [velocity,NativeWindowStressHeatTime.field_original] using!
      NativeWindowStressHeatSource.product_integrable seed time (pressureRead F output) (NativeWindowFiniteGramFourier.read F input)
  · simpa only [velocity,NativeWindowStressHeatTime.field_original] using!
      NativeWindowStressHeatSource.product_integrable seed time (NativeWindowFiniteGramFourier.read F output) (pressureRead F input)

theorem convectionPair_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : convectionPair seed F output input time=
      pair (fun i => convectionRead F i (NativeUnifiedCompleteSource.source seed time)) (velocity seed F time) output input+
        NativeWindowHighTransportForcing.highPair seed F ∅ output input time := by
  simp only [convectionPair,convectionResidual,pair,NativeWindowHighTransportForcing.highPair,
    NativeWindowHighTransportForcing.highAdvection,drift,empty_velocity,sub_zero]
  ring

theorem convectionPair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : Integrable (fun shift => convectionPair seed F output input (time-shift)) averageMeasure := by
  have raw : Integrable (fun shift => pair (fun i => convectionRead F i (NativeUnifiedCompleteSource.source seed (time-shift)))
      (velocity seed F (time-shift)) output input) averageMeasure := by
    unfold pair
    convert! Integrable.add (ε' := C(Torus,ℝ)) ?_ ?_ using 1
    · simpa only [velocity,NativeWindowStressHeatTime.field_original] using!
        NativeWindowStressHeatSource.product_integrable seed time (convectionRead F output) (NativeWindowFiniteGramFourier.read F input)
    · simpa only [velocity,NativeWindowStressHeatTime.field_original] using!
        NativeWindowStressHeatSource.product_integrable seed time (NativeWindowFiniteGramFourier.read F output) (convectionRead F input)
  simp only [convectionPair_split]
  convert! Integrable.add (ε' := C(Torus,ℝ)) raw
    (NativeWindowHighTransportForcing.highPair_integrable seed time F ∅ output input) using 1

def lowWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) := ∫ shift,lowPair seed F A output input (time-shift) ∂averageMeasure

def convectionWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) := ∫ shift,convectionPair seed F output input (time-shift) ∂averageMeasure

def pressureWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) := ∫ shift,pressurePair seed F output input (time-shift) ∂averageMeasure

theorem remainingWindow_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (F A : Finset IntegerWavevector) (output input : Coordinate) :
    NativeWindowHighTransportForcing.remainingWindow seed time F A output input=
      lowWindow seed time F A output input-convectionWindow seed time F output input-pressureWindow seed time F output input := by
  have shifted := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    (remainingPair_ae seed F A)
  have measured := (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le shifted
  have actual : (fun shift => remainingPair seed F A output input (time-shift)) =ᵐ[averageMeasure]
      fun shift => lowPair seed F A output input (time-shift)-convectionPair seed F output input (time-shift)-
        pressurePair seed F output input (time-shift) := by
    filter_upwards [measured,NativeWindowHistoryGNS.average_support] with shift source support
    exact source (by linarith) output input
  rw [NativeWindowHighTransportForcing.remainingWindow,integral_congr_ae actual]
  have first : Integrable (fun shift => lowPair seed F A output input (time-shift)-
      convectionPair seed F output input (time-shift)) averageMeasure := by
    convert! Integrable.sub (β := C(Torus,ℝ)) (lowPair_integrable seed time F A output input)
      (convectionPair_integrable seed time F output input) using 1
  rw [integral_sub first (pressurePair_integrable seed time F output input),
    integral_sub (lowPair_integrable seed time F A output input) (convectionPair_integrable seed time F output input)]
  rfl

theorem sigma_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time)
    (F A : Finset IntegerWavevector) (closed : ∀ k,k∈F → waveNeg k∈F) (output input : Coordinate) :
    HasDerivAt (NativeWindowStressHeatBalance.sigma seed F output input)
      (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)+
        NativeWindowStressHeatSource.physical (NativeWindowHighTransportForcing.highWindow seed time F A output input)+
        NativeWindowStressHeatSource.physical (lowWindow seed time F A output input)-
        NativeWindowStressHeatSource.physical (convectionWindow seed time F output input)-
        NativeWindowStressHeatSource.physical (pressureWindow seed time F output input)+
        NativeWindowStressHeatSource.physical (NativeWindowStressPreparationAction.correction seed time F output input)) time := by
  have original := NativeWindowHighTransportForcing.sigma_hasDerivAt seed time F A closed output input
  rw [remainingWindow_split seed time nonnegative,map_sub,map_sub] at original
  convert! original using 1
  abel

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (F A : Finset IntegerWavevector) :
    (lowWindow seed (step.2.clockAdvance+time) F A,convectionWindow seed (step.2.clockAdvance+time) F,
      pressureWindow seed (step.2.clockAdvance+time) F)=
    (lowWindow step.1 time F A,convectionWindow step.1 time F,pressureWindow step.1 time F) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals
    funext output input
    dsimp only [lowWindow,convectionWindow,pressureWindow]
    apply integral_congr_ae
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    have nonnegative' : 0≤time-shift := by linarith
    have source := NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) nonnegative'
    dsimp only [lowPair,convectionPair,pressurePair,pair,convectionResidual,lowAdvection,advection,
      velocity,NativeWindowCrossHistoryAction.gradient]
    simp only [NativeWindowStressHeatTime.field_original,show step.2.clockAdvance+time-shift=
      step.2.clockAdvance+(time-shift) by ring,source]

end
end SaturationMonoid.NavierStokes.NativeWindowRetainedAction

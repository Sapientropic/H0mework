import H0mework.NavierStokes.WindowEnergyHighTransport.Relative
import H0mework.NavierStokes.WindowEnergyHighTransport.Spatial

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportNormalForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativePhysicalFourier NativeWindowHighTransportRelative
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem physical_fourier (f : C(Torus,ℝ)) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (NativeWindowStressHeatSource.physical f) k=NativeWindowFiniteGramFourier.fourierRead k f := by
  change UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) f).toLp 2 volume ℂ) k=_
  rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
  rfl

theorem highWindow_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    NativeWindowStressHeatSource.physical (NativeWindowHighTransportForcing.highWindow seed time F
      (F∩wholeRestartModes radius) output input)=primitiveViscous seed F radius time output input := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext k
  rw [UnitAddTorus.mFourierBasis_repr,UnitAddTorus.mFourierBasis_repr,physical_fourier,
    NativeWindowHighTransportSpatial.highWindow_fourier seed time nonnegative,primitiveViscous_fourier]
  have actual := primitive_viscous_original seed F radius time nonnegative closed output input k
  change (nu.coeff*integerWaveViscousMultiplier k : ℝ) • UnitAddTorus.mFourierCoeff
    (NativeWindowStressHeatEnergy.field (NativeWindowHighTransportResolvent.primitive seed F radius 0 time output input)) k=_ at actual
  rw [NativeWindowStressHeatEnergy.field_fourier] at actual
  exact actual.symm

/-- Original heat and retained two-leg action, with the source-owned viscous primitive removed. -/
def sourceRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)+
    primitiveViscous seed F radius time output input+
    NativeWindowStressHeatSource.physical (NativeWindowHighTransportForcing.remainingWindow seed time F (F∩wholeRestartModes radius) output input)+
    NativeWindowStressHeatSource.physical (NativeWindowStressPreparationAction.correction seed time F output input)-
    primitiveField seed F radius 1 time output input

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    HasDerivAt (fun t => relative seed F radius t output input) (sourceRate seed F radius time output input) time := by
  have source := (NativeWindowHighTransportForcing.sigma_hasDerivAt seed time F (F∩wholeRestartModes radius) closed output input).sub
    (primitiveField_hasDerivAt seed F radius 0 time output input)
  rw [highWindow_original seed F radius time nonnegative closed output input] at source
  exact source

theorem sourceRate_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    sourceRate seed F radius time output input=rawRate seed F radius time output input :=
  (source_hasDerivAt seed F radius time nonnegative closed output input).unique (relative_derivative seed F radius time output input)

theorem whole_source_write (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (closed : ∀ k,k∈F →waveNeg k∈F) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) :
    relative seed F radius b-relative seed F radius a=∫ time in a..b,sourceRate seed F radius time := by
  have derivative (time : ℝ) : HasDerivAt (relative seed F radius) (rawRate seed F radius time) time :=
    hasDerivAt_pi.mpr fun output => hasDerivAt_pi.mpr fun input => relative_derivative seed F radius time output input
  have continuous : Continuous (rawRate seed F radius) :=
    continuous_pi fun output => continuous_pi fun input => rawRate_continuous seed F radius output input
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time) (continuous.intervalIntegrable a b)
  refine generated.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro time inside
  funext output input
  exact (sourceRate_original seed F radius time ((le_min a0 b0).trans inside.1) closed output input).symm

def retainedWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowHighTransportForcing.remainingWindow seed time F (F∩wholeRestartModes radius) output input))

def heatWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)+primitiveViscous seed F radius time output input)

def preparationWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressPreparationAction.correction seed time F output input))

theorem energy_generator (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    HasDerivAt (energy seed F radius)
      (heatWork seed F radius time+retainedWork seed F radius time+preparationWork seed F radius time-timeWork seed F radius time) time := by
  have row (output input : Coordinate) := ((source_hasDerivAt seed F radius time nonnegative closed output input).norm_sq).const_mul (1/2 : ℝ)
  have actual := HasDerivAt.sum (u := Finset.univ) fun output _ => HasDerivAt.sum (u := Finset.univ) fun input _ => row output input
  convert! actual using 1
  simp only [sourceRate,heatWork,retainedWork,preparationWork,timeWork,inner_add_right,inner_sub_right]
  simp_rw [show ∀ x : ℝ,(1/2 : ℝ)*(2*x)=x from fun x => by ring]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]

theorem energy_uniform_feed (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
    (∀ k,k∈F →waveNeg k∈F) →deriv (energy seed F radius) time ≤
      heatWork seed F radius time+retainedWork seed F radius time+preparationWork seed F radius time+energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := timeWork_uniform seed horizon nonnegative epsilon positive
  refine ⟨low,fun radius above F time inside closed => ?_⟩
  rw [(energy_generator seed F radius time inside.1 closed).deriv]
  have paid := small radius above F time inside
  have signed := neg_le_abs (timeWork seed F radius time)
  linarith only [paid,signed]

theorem whole_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    relative seed F radius (step.2.clockAdvance+time)=relative step.1 F radius time := by
  funext output input
  simp only [relative,NativeWindowStressHeatBalance.sigma,NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative,
    primitiveField,NativeWindowHighTransportResolvent.primitive_next seed F radius 0 step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportNormalForm

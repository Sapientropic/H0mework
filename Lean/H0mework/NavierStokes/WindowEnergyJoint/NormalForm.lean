import H0mework.NavierStokes.WindowEnergyHighPressure.StrainHistory
import H0mework.NavierStokes.WindowEnergyRetained.Pressure

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowJointNormalForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier
open NativeWindowPressureStrainHistory (correction relative)
open NativeWindowHighTransportRelative (fieldCLM)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def correctionJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  fieldCLM (NativeWindowHighTransportResolvent.primitive seed F radius order time output input-
    NativeWindowHighPressureResolvent.primitive seed F radius order time output input)

theorem correctionJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : correctionJet seed F radius 0 time output input=correction seed F radius time output input := by
  rw [correctionJet,map_sub]
  rfl

theorem correctionJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : HasDerivAt (fun t => correctionJet seed F radius order t output input)
      (correctionJet seed F radius (order+1) time output input) time :=
  fieldCLM.hasFDerivAt.comp_hasDerivAt time
    ((NativeWindowHighTransportResolvent.primitive_hasDerivAt seed F radius order time output input).sub
      (NativeWindowHighPressureResolvent.primitive_hasDerivAt seed F radius order time output input))

theorem correctionJet_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : ‖correctionJet seed F radius order time output input‖ ≤
      ‖NativeWindowHighTransportResolvent.primitive seed F radius order time output input‖+
        ‖NativeWindowHighPressureResolvent.primitive seed F radius order time output input‖ := by
  change ‖(UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (_-_)‖≤_
  rw [LinearIsometryEquiv.norm_map]
  exact norm_sub_le _ _

theorem correctionJet_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →∀ output input,
      ‖correctionJet seed F radius order time output input‖<epsilon := by
  obtain ⟨left,first⟩ := NativeWindowHighTransportResolvent.primitive_small seed order horizon nonnegative (epsilon/2) (by positivity)
  obtain ⟨right,last⟩ := NativeWindowHighPressureResolvent.primitive_small seed order horizon nonnegative (epsilon/2) (by positivity)
  refine ⟨max left right,fun radius above F time inside output input => ?_⟩
  apply (correctionJet_bound seed F radius order time output input).trans_lt
  have a := first radius ((le_max_left _ _).trans above) F time inside output input
  have b := last radius ((le_max_right _ _).trans above) F time inside output input
  linarith only [a,b]

def rawRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  -NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet seed F output input 1 time)-
    correctionJet seed F radius 1 time output input

theorem relative_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : HasDerivAt (fun t => relative seed F radius t output input)
      (rawRate seed F radius time output input) time := by
  have derivative := correctionJet_hasDerivAt seed F radius 0 time output input
  simp only [correctionJet_zero] at derivative
  have source := ((NativeWindowStressHeatSource.physical.hasFDerivAt.comp_hasDerivAt time
    (NativeWindowStressHeatTime.jet_hasDerivAt seed F output input 0 time)).neg).sub derivative
  simpa only [relative,rawRate,NativeWindowStressHeatBalance.sigma,NativeWindowStressHeatTime.jet_zero,
    Function.comp_def,Pi.sub_apply,Pi.neg_apply] using! source

theorem rawRate_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (output input : Coordinate) : Continuous (fun t => rawRate seed F radius t output input) := by
  have first := (NativeWindowStressHeatSource.physical.continuous.comp (continuous_iff_continuousAt.mpr
    (fun time => (NativeWindowStressHeatTime.jet_hasDerivAt seed F output input 1 time).continuousAt))).neg
  exact first.sub (continuous_iff_continuousAt.mpr fun time =>
    (correctionJet_hasDerivAt seed F radius 1 time output input).continuousAt)

def heatRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)+
    NativeWindowHighTransportRelative.primitiveViscous seed F radius time output input-
      NativeWindowRetainedPressure.viscousPrimitive seed F radius time output input

def retainedRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatSource.physical (NativeWindowRetainedAction.lowWindow seed time F (F∩wholeRestartModes radius) output input)-
    NativeWindowStressHeatSource.physical (NativeWindowRetainedAction.convectionWindow seed time F output input)-
      NativeWindowRetainedPressure.remainderField seed F radius time output input

def sourceRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  heatRate seed F radius time output input+retainedRate seed F radius time output input+
    NativeWindowStressHeatSource.physical (NativeWindowStressPreparationAction.correction seed time F output input)-
      correctionJet seed F radius 1 time output input

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    HasDerivAt (fun t => relative seed F radius t output input) (sourceRate seed F radius time output input) time := by
  have derivative := correctionJet_hasDerivAt seed F radius 0 time output input
  simp only [correctionJet_zero] at derivative
  have source := (NativeWindowRetainedPressure.sigma_hasDerivAt seed time nonnegative F
    (F∩wholeRestartModes radius) closed radius output input).sub derivative
  rw [NativeWindowHighTransportNormalForm.highWindow_original seed F radius time nonnegative closed output input] at source
  convert! source using 1
  dsimp only [sourceRate,heatRate,retainedRate]
  abel

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
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time) (continuous.intervalIntegrable a b)
  refine actual.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro time inside
  funext output input
  exact (sourceRate_original seed F radius time ((le_min a0 b0).trans inside.1) closed output input).symm

def energy (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,(1/2 : ℝ)*‖relative seed F radius time output input‖^2

def timeWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (correctionJet seed F radius 1 time output input)

def heatWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input) (heatRate seed F radius time output input)

def retainedWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input) (retainedRate seed F radius time output input)

def preparationWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressPreparationAction.correction seed time F output input))

theorem timeWork_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    |timeWork seed F radius time|≤energy seed F radius time+
      ∑ output : Coordinate,∑ input : Coordinate,(1/2 : ℝ)*‖correctionJet seed F radius 1 time output input‖^2 := by
  have row (output input : Coordinate) : |inner ℝ (relative seed F radius time output input)
      (correctionJet seed F radius 1 time output input)|≤(1/2 : ℝ)*‖relative seed F radius time output input‖^2+
        (1/2 : ℝ)*‖correctionJet seed F radius 1 time output input‖^2 := by
    apply (abs_real_inner_le_norm _ _).trans
    nlinarith only [sq_nonneg (‖relative seed F radius time output input‖-‖correctionJet seed F radius 1 time output input‖)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ => row output input)
  simpa only [Finset.sum_add_distrib,energy,timeWork] using paid

theorem timeWork_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      |timeWork seed F radius time|≤energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := correctionJet_small seed 1 horizon nonnegative (Real.sqrt (2*epsilon/9)) (by positivity)
  refine ⟨low,fun radius above F time inside => (timeWork_bound seed F radius time).trans ?_⟩
  apply add_le_add_right
  have row (output input : Coordinate) : (1/2 : ℝ)*‖correctionJet seed F radius 1 time output input‖^2≤epsilon/9 := by
    have paid := pow_le_pow_left₀ (norm_nonneg _) (small radius above F time inside output input).le 2
    rw [Real.sq_sqrt (by positivity : 0≤2*epsilon/9)] at paid
    linarith
  exact (Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)

theorem energy_generator (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    HasDerivAt (energy seed F radius)
      (heatWork seed F radius time+retainedWork seed F radius time+preparationWork seed F radius time-timeWork seed F radius time) time := by
  have row (output input : Coordinate) := ((source_hasDerivAt seed F radius time nonnegative closed output input).norm_sq).const_mul (1/2 : ℝ)
  have source := HasDerivAt.sum (u := Finset.univ) fun output _ => HasDerivAt.sum (u := Finset.univ) fun input _ => row output input
  convert! source using 1
  simp only [sourceRate,heatWork,retainedWork,preparationWork,timeWork,inner_add_right,inner_sub_right]
  simp_rw [show ∀ x : ℝ,(1/2 : ℝ)*(2*x)=x from fun x => by ring]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]

theorem energy_uniform_feed (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
    (∀ k,k∈F →waveNeg k∈F) →deriv (energy seed F radius) time≤
      heatWork seed F radius time+retainedWork seed F radius time+preparationWork seed F radius time+energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := timeWork_uniform seed horizon nonnegative epsilon positive
  refine ⟨low,fun radius above F time inside closed => ?_⟩
  rw [(energy_generator seed F radius time inside.1 closed).deriv]
  have paid := small radius above F time inside
  have signed := neg_le_abs (timeWork seed F radius time)
  linarith only [paid,signed]

theorem original_energy_le (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    NativeWindowStressHeatBalance.energy seed F time≤2*energy seed F radius time+
      ∑ output : Coordinate,∑ input : Coordinate,‖correction seed F radius time output input‖^2 := by
  simp only [NativeWindowStressHeatBalance.energy,energy,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output _
  apply Finset.sum_le_sum
  intro input _
  have same : NativeWindowStressHeatBalance.sigma seed F output input time=
      relative seed F radius time output input+correction seed F radius time output input := by unfold relative; abel
  have bound := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (relative seed F radius time output input)
    (correction seed F radius time output input)) 2
  rw [same]
  nlinarith only [bound,sq_nonneg (‖relative seed F radius time output input‖-‖correction seed F radius time output input‖)]

theorem original_energy_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      NativeWindowStressHeatBalance.energy seed F time≤2*energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := correctionJet_small seed 0 horizon nonnegative (Real.sqrt (epsilon/9)) (by positivity)
  refine ⟨low,fun radius above F time inside => (original_energy_le seed F radius time).trans ?_⟩
  apply add_le_add_right
  have row (output input : Coordinate) : ‖correction seed F radius time output input‖^2≤epsilon/9 := by
    have paid := pow_le_pow_left₀ (norm_nonneg _) (small radius above F time inside output input).le 2
    simpa only [correctionJet_zero,Real.sq_sqrt (by positivity : 0≤epsilon/9)] using paid
  exact (Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)

theorem correctionJet_zero_mode (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : UnitAddTorus.mFourierCoeff (correctionJet seed F radius order time output input) 0=0 := by
  have pressure : NativeWindowHighPressureResolvent.primitive seed F radius order time output input 0=0 := by
    change (∑ j : Coordinate,NativeWindowHighTransportResolvent.factor nu j 0*
      NativeWindowHighPressureResolvent.window seed F radius order time j output input 0)=0
    simp [NativeWindowHighTransportResolvent.factor,NativePhysicalGradient.multiplier,complexWavevector]
  change UnitAddTorus.mFourierCoeff (NativeWindowStressHeatEnergy.field (_-_)) 0=0
  rw [NativeWindowStressHeatEnergy.field_fourier]
  simp only [lp.coeFn_sub,Pi.sub_apply,NativeWindowHighTransportResolvent.primitive_zero,pressure,sub_self]

theorem relative_mean (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : UnitAddTorus.mFourierCoeff (relative seed F radius time output input) 0=
      UnitAddTorus.mFourierCoeff (NativeWindowStressHeatBalance.sigma seed F output input time) 0 := by
  simp only [← UnitAddTorus.mFourierBasis_repr,relative,map_sub,lp.coeFn_sub,Pi.sub_apply]
  rw [UnitAddTorus.mFourierBasis_repr,UnitAddTorus.mFourierBasis_repr,← correctionJet_zero,
    correctionJet_zero_mode,sub_zero]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem correctionJet_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    correctionJet seed F radius order (step.2.clockAdvance+time)=correctionJet step.1 F radius order time := by
  funext output input
  simp only [correctionJet,NativeWindowHighTransportResolvent.primitive_next seed F radius order step generated time nonnegative,
    NativeWindowHighPressureResolvent.primitive_next seed F radius order step generated time nonnegative]

theorem sourceRate_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    sourceRate seed F radius (step.2.clockAdvance+time)=sourceRate step.1 F radius time := by
  funext output input
  rw [sourceRate_original seed F radius _ (add_nonneg step.2.clockAdvance_pos.le nonnegative) closed,
    sourceRate_original step.1 F radius time nonnegative closed]
  simp only [rawRate,NativeWindowStressHeatTime.jet_next seed F output input 1 step generated time nonnegative,
    correctionJet_next seed F radius 1 step generated time nonnegative]

theorem whole_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    (relative seed F radius (step.2.clockAdvance+time),sourceRate seed F radius (step.2.clockAdvance+time),energy seed F radius (step.2.clockAdvance+time))=
      (relative step.1 F radius time,sourceRate step.1 F radius time,energy step.1 F radius time) := by
  simp only [energy,NativeWindowPressureStrainHistory.relative_next seed step generated radius time nonnegative F,
    sourceRate_next seed F closed radius step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowJointNormalForm

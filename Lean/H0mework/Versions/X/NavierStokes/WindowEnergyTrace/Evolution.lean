import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Energy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowTraceEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeWindowStressHeatSource (physical)
open NativeWindowTraceGradient (traceStress traceDiffusion traceInteraction)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def timeWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,NativeWindowJointNormalForm.correctionJet seed F radius 1 time i i)

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    HasDerivAt (relative seed F radius) (∑ i : Coordinate,NativeWindowJointNormalForm.sourceRate seed F radius time i i) time :=
  HasDerivAt.sum (u := Finset.univ) fun i _ => NativeWindowJointNormalForm.source_hasDerivAt seed F radius time nonnegative closed i i

theorem pressure_trace_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) :
    inner ℝ (relative seed F radius time) (∑ i : Coordinate,physical (NativeWindowPressureStrainHistory.window seed radius time F i i))=0 := by
  rw [inner_sum]
  exact NativeWindowPressureStrainHistory.isotropic_pressure_zero seed radius time nonnegative F _

theorem energy_generator (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    HasDerivAt (energy seed F radius) (heatWork seed F radius time+lowAdvWork seed F radius time+
      convectionWork seed F radius time+lowPressureWork seed F radius time-timeWork seed F radius time) time := by
  have source := ((source_hasDerivAt seed F radius time nonnegative closed).norm_sq).const_mul (1/2 : ℝ)
  have preparation (i : Coordinate) : physical (NativeWindowStressPreparationAction.correction seed time F i i)=0 := by
    rw [NativeWindowStressPreparationAction.correction,NativeWindowPreparationWrite.fraction_after time (by linarith),
      zero_smul,map_zero]
  convert! source using 1
  simp only [NativeWindowJointNormalForm.sourceRate,NativeWindowJointNormalForm.retainedRate,
    NativeWindowJointEnergyGate.remainderField_split seed F closed radius,preparation,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,add_zero,
    inner_sub_right,inner_add_right,pressure_trace_zero seed F radius time nonnegative,
    heatWork,lowAdvWork,convectionWork,lowPressureWork,timeWork]
  ring

theorem energy_balance (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    deriv (energy seed F radius) time+nu.coeff*dirichlet seed F radius time+
      2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)=
        lowAdvWork seed F radius time+convectionWork seed F radius time+lowPressureWork seed F radius time-
          timeWork seed F radius time-2*nu.coeff*crossWork seed F radius time := by
  rw [(energy_generator seed F radius time nonnegative closed).deriv,heatWork_identity seed F radius time closed]
  ring

theorem timeWork_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      |timeWork seed F radius time|≤energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := NativeWindowJointNormalForm.correctionJet_small seed 1 horizon nonnegative
    (Real.sqrt (2*epsilon)/3) (by positivity)
  refine ⟨low,fun radius above F time inside => ?_⟩
  have normBound : ‖∑ i : Coordinate,NativeWindowJointNormalForm.correctionJet seed F radius 1 time i i‖≤Real.sqrt (2*epsilon) := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum fun i _ => (small radius above F time inside i i).le).trans_eq
    simp
    ring
  have square := pow_le_pow_left₀ (norm_nonneg _) normBound 2
  rw [Real.sq_sqrt (by positivity : 0≤2*epsilon)] at square
  apply (abs_real_inner_le_norm _ _).trans
  unfold energy
  nlinarith only [square,sq_nonneg (‖relative seed F radius time‖-
    ‖∑ i : Coordinate,NativeWindowJointNormalForm.correctionJet seed F radius 1 time i i‖)]

theorem source_energy_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      (∀ k,k∈F →waveNeg k∈F) →deriv (energy seed F radius) time+nu.coeff*dirichlet seed F radius time+
        2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)≤
          lowAdvWork seed F radius time+convectionWork seed F radius time+lowPressureWork seed F radius time+
            energy seed F radius time+epsilon-2*nu.coeff*crossWork seed F radius time := by
  obtain ⟨low,small⟩ := timeWork_uniform seed horizon nonnegative epsilon positive
  refine ⟨low,fun radius above F time inside closed => ?_⟩
  rw [energy_balance seed F radius time inside.1 closed]
  have paid := small radius above F time inside
  have signed := neg_le_abs (timeWork seed F radius time)
  linarith only [paid,signed]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem whole_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    (relative seed F radius (step.2.clockAdvance+time),correction seed F radius (step.2.clockAdvance+time),
      energy seed F radius (step.2.clockAdvance+time))=(relative step.1 F radius time,correction step.1 F radius time,energy step.1 F radius time) := by
  simp only [relative,correction,energy,NativeWindowPressureStrainHistory.relative_next seed step generated radius time nonnegative F,
    NativeWindowPressureStrainHistory.correction_next seed step generated radius time nonnegative F]

theorem dirichlet_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    dirichlet seed F radius (step.2.clockAdvance+time)=dirichlet step.1 F radius time := by
  have same := congrArg Prod.fst (whole_next seed F radius step generated time nonnegative)
  change relative seed F radius (step.2.clockAdvance+time)=relative step.1 F radius time at same
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro j _
  have before := gradient_original seed F radius (step.2.clockAdvance+time) closed j
  rw [same] at before
  exact congrArg (fun value : ScalarField => ‖value‖^2)
    (neg_injective (before.unique (gradient_original step.1 F radius time closed j)))

end
end SaturationMonoid.NavierStokes.NativeWindowTraceEnergy

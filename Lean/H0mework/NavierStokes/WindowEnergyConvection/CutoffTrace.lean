import H0mework.NavierStokes.WindowEnergyConvection.CutoffNormalForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffTrace
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier NativeWindowStressHeatEnergy
open NativeWindowStressHeatSource (physical)
open NativeWindowTraceGradient (traceStress traceDiffusion traceInteraction)
open NativeWindowConvectionCutoffAction (frequencies primitiveField)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def relative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ScalarField :=
  ∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.relative seed F radius time i i

def correction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ScalarField :=
  ∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.correction seed F radius time i i

def coefficients (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (k : IntegerWavevector) : ℂ := ∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.coefficients seed F radius time k i i

def energy (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  (1/2 : ℝ)*‖relative seed F radius time‖^2

def dirichlet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ j : Coordinate,‖field (finiteJet (frequencies F) (coefficients seed F radius time) j 1)‖^2

def lowAdvWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,physical (NativeWindowRetainedAction.lowWindow seed time F (F∩wholeRestartModes radius) i i))

def strainWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,physical (NativeWindowConvectionCutoffAction.strainWindow seed F time i i))

def lowPressureWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  -(inner ℝ (relative seed F radius time) (∑ i : Coordinate,NativeWindowJointEnergyGate.lowPressureField seed F radius time i i))

def heatWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.heatRate seed F radius time i i)

def crossWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (correction seed F radius time) (physical (traceDiffusion seed time F))

def timeWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.correctionJet seed F radius 1 time i i)

theorem old_trace_difference (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    relative seed F radius time=NativeWindowTraceEnergy.relative seed F radius time+∑ i : Coordinate,primitiveField seed F 0 time i i := by
  simp only [relative,NativeWindowConvectionCutoffNormalForm.relative,Finset.sum_add_distrib,NativeWindowTraceEnergy.relative]

theorem crossWork_difference (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    crossWork seed F radius time=NativeWindowTraceEnergy.crossWork seed F radius time-
      inner ℝ (∑ i : Coordinate,primitiveField seed F 0 time i i) (physical (traceDiffusion seed time F)) := by
  simp only [crossWork,correction,NativeWindowConvectionCutoffNormalForm.correction,Finset.sum_sub_distrib,inner_sub_left,
    NativeWindowTraceEnergy.crossWork,NativeWindowTraceEnergy.correction]

theorem strainWork_difference (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    strainWork seed F radius time=
      inner ℝ (NativeWindowTraceEnergy.relative seed F radius time)
        (∑ i : Coordinate,physical (NativeWindowConvectionCutoffAction.strainWindow seed F time i i))+
      inner ℝ (∑ i : Coordinate,primitiveField seed F 0 time i i)
        (∑ i : Coordinate,physical (NativeWindowConvectionCutoffAction.strainWindow seed F time i i)) := by
  rw [strainWork,old_trace_difference,inner_add_left]

theorem sequence_trace (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    finiteSequence (frequencies F) (coefficients seed F radius time)=∑ i : Coordinate,
      finiteSequence (frequencies F) (fun k => NativeWindowConvectionCutoffNormalForm.coefficients seed F radius time k i i) := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum,Finset.sum_apply,finiteSequence_apply,coefficients]
  split_ifs <;> simp

theorem jet_trace (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (j : Coordinate) (order : ℕ) : finiteJet (frequencies F) (coefficients seed F radius time) j order=
      ∑ i : Coordinate,finiteJet (frequencies F) (fun k => NativeWindowConvectionCutoffNormalForm.coefficients seed F radius time k i i) j order := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum,Finset.sum_apply,finiteJet,finiteSequence_apply,coefficients,Finset.mul_sum]
  split_ifs <;> simp

theorem field_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) : field (finiteSequence (frequencies F) (coefficients seed F radius time))=
      physical (traceStress seed time F)+correction seed F radius time := by
  rw [sequence_trace]
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (∑ i : Coordinate,_) = _
  rw [map_sum]
  change (∑ i : Coordinate,field (finiteSequence (frequencies F)
    (fun k => NativeWindowConvectionCutoffNormalForm.coefficients seed F radius time k i i)))=_
  simp only [NativeWindowConvectionCutoffNormalForm.combined_field seed F radius time closed,Finset.sum_add_distrib,
    traceStress,correction,map_sum]

theorem relative_field (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) : relative seed F radius time=
      -field (finiteSequence (frequencies F) (coefficients seed F radius time)) := by
  rw [sequence_trace]
  change _= -(UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (∑ i : Coordinate,_)
  rw [map_sum,← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => NativeWindowConvectionCutoffNormalForm.relative_field seed F radius time closed i i)

theorem heat_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    (∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.heatRate seed F radius time i i)=
      -nu.coeff • (∑ j : Coordinate,field (finiteJet (frequencies F) (coefficients seed F radius time) j 2))+
        (2*nu.coeff) • physical (traceDiffusion seed time F) := by
  have jet_read (j : Coordinate) : field (finiteJet (frequencies F) (coefficients seed F radius time) j 2)=
      ∑ i : Coordinate,field (finiteJet (frequencies F) (fun k => NativeWindowConvectionCutoffNormalForm.coefficients seed F radius time k i i) j 2) := by
    rw [jet_trace]
    exact map_sum (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm _ _
  simp only [NativeWindowConvectionCutoffNormalForm.heat_original seed F radius time closed,Finset.sum_add_distrib,← Finset.smul_sum,
    traceDiffusion,map_sum,jet_read]
  rw [Finset.sum_comm (f := fun i j => field (finiteJet (frequencies F)
    (fun k => NativeWindowConvectionCutoffNormalForm.coefficients seed F radius time k i i) j 2))]

theorem heatWork_identity (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) : heatWork seed F radius time=
      -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)-
        2*nu.coeff*crossWork seed F radius time := by
  have green (j : Coordinate) : inner ℝ (field (finiteSequence (frequencies F) (coefficients seed F radius time)))
      (field (finiteJet (frequencies F) (coefficients seed F radius time) j 2))=
        -‖field (finiteJet (frequencies F) (coefficients seed F radius time) j 1)‖^2 := by
    simpa only [finiteJet,pow_zero,one_mul] using finite_green (frequencies F) (coefficients seed F radius time) j
  rw [heatWork,heat_original seed F radius time closed,relative_field seed F radius time closed]
  simp only [inner_add_right,real_inner_smul_right,inner_neg_left,inner_sum,green,Finset.sum_neg_distrib]
  rw [field_original seed F radius time closed,inner_add_left,NativeWindowStressHeatSource.physical_inner]
  change _= -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,traceStress seed time F point*traceDiffusion seed time F point)-2*nu.coeff*crossWork seed F radius time
  dsimp only [dirichlet,crossWork]
  ring

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0 ≤ time) (closed : ∀ k,k∈F →waveNeg k∈F) : HasDerivAt (relative seed F radius)
      (∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.sourceRate seed F radius time i i) time :=
  HasDerivAt.sum (u := Finset.univ) fun i _ => NativeWindowConvectionCutoffNormalForm.source_hasDerivAt seed F radius time nonnegative closed i i

theorem energy_generator (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0 ≤ time) (closed : ∀ k,k∈F →waveNeg k∈F) : HasDerivAt (energy seed F radius)
      (heatWork seed F radius time+lowAdvWork seed F radius time+strainWork seed F radius time+
        lowPressureWork seed F radius time-timeWork seed F radius time) time := by
  have source := ((source_hasDerivAt seed F radius time nonnegative closed).norm_sq).const_mul (1/2 : ℝ)
  have preparation (i : Coordinate) : physical (NativeWindowStressPreparationAction.correction seed time F i i)=0 := by
    rw [NativeWindowStressPreparationAction.correction,NativeWindowPreparationWrite.fraction_after time (by linarith),zero_smul,map_zero]
  have pressure : inner ℝ (relative seed F radius time)
      (∑ i : Coordinate,physical (NativeWindowPressureStrainHistory.window seed radius time F i i))=0 := by
    rw [inner_sum]
    exact NativeWindowPressureStrainHistory.isotropic_pressure_zero seed radius time nonnegative F _
  convert! source using 1
  simp only [NativeWindowConvectionCutoffNormalForm.sourceRate,NativeWindowConvectionCutoffNormalForm.retainedRate,
    NativeWindowJointEnergyGate.remainderField_split seed F closed radius,preparation,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    add_zero,inner_sub_right,inner_add_right,pressure,heatWork,lowAdvWork,strainWork,lowPressureWork,timeWork]
  ring

theorem energy_balance (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0 ≤ time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    deriv (energy seed F radius) time+nu.coeff*dirichlet seed F radius time+
      2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)=
        lowAdvWork seed F radius time+strainWork seed F radius time+lowPressureWork seed F radius time-
          timeWork seed F radius time-2*nu.coeff*crossWork seed F radius time := by
  rw [(energy_generator seed F radius time nonnegative closed).deriv,heatWork_identity seed F radius time closed]
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem whole_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (relative seed F radius (step.2.clockAdvance+time),energy seed F radius (step.2.clockAdvance+time))=
      (relative step.1 F radius time,energy step.1 F radius time) := by
  have same := congrArg (fun value : Coordinate → Coordinate → ScalarField => ∑ i : Coordinate,value i i)
    (NativeWindowConvectionCutoffNormalForm.whole_next seed F radius step generated time nonnegative)
  change relative seed F radius (step.2.clockAdvance+time)=relative step.1 F radius time at same
  simp only [energy,same]

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffTrace

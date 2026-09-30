import H0mework.NavierStokes.WindowEnergyTrace.Gradient

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

def relative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ScalarField :=
  ∑ i : Coordinate,NativeWindowPressureStrainHistory.relative seed F radius time i i

def correction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ScalarField :=
  ∑ i : Coordinate,NativeWindowPressureStrainHistory.correction seed F radius time i i

def coefficients (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (k : IntegerWavevector) : ℂ := ∑ i : Coordinate,NativeWindowJointHeat.coefficients seed F radius time k i i

def energy (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  (1/2 : ℝ)*‖relative seed F radius time‖^2

def dirichlet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ j : Coordinate,‖field (finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 1)‖^2

def lowAdvWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,
    physical (NativeWindowRetainedAction.lowWindow seed time F (F∩wholeRestartModes radius) i i))

def convectionWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  -(inner ℝ (relative seed F radius time) (∑ i : Coordinate,physical (NativeWindowRetainedAction.convectionWindow seed time F i i)))

def lowPressureWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  -(inner ℝ (relative seed F radius time) (∑ i : Coordinate,NativeWindowJointEnergyGate.lowPressureField seed F radius time i i))

def heatWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (relative seed F radius time) (∑ i : Coordinate,NativeWindowJointNormalForm.heatRate seed F radius time i i)

def crossWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (correction seed F radius time) (physical (traceDiffusion seed time F))

theorem sequence_trace (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) : finiteSequence (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time)=
      ∑ i : Coordinate,finiteSequence (NativeWindowJointHeat.frequencies F) (fun k => NativeWindowJointHeat.coefficients seed F radius time k i i) := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum,Finset.sum_apply,finiteSequence_apply,coefficients]
  split_ifs <;> simp

theorem jet_trace (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (j : Coordinate) (order : ℕ) :
    finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j order=
      ∑ i : Coordinate,finiteJet (NativeWindowJointHeat.frequencies F) (fun k => NativeWindowJointHeat.coefficients seed F radius time k i i) j order := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum,Finset.sum_apply,finiteJet,finiteSequence_apply,coefficients,Finset.mul_sum]
  split_ifs <;> simp

theorem field_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    field (finiteSequence (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time))=
      physical (traceStress seed time F)+correction seed F radius time := by
  rw [sequence_trace]
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (∑ i : Coordinate,_) = _
  rw [map_sum]
  change (∑ i : Coordinate,field (finiteSequence (NativeWindowJointHeat.frequencies F)
    (fun k => NativeWindowJointHeat.coefficients seed F radius time k i i)))=_
  simp only [NativeWindowJointHeat.combined_field seed F radius time closed,Finset.sum_add_distrib,
    traceStress,correction,map_sum]

theorem relative_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    relative seed F radius time= -field (finiteSequence (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time)) := by
  rw [field_original seed F radius time closed]
  simp only [relative,NativeWindowPressureStrainHistory.relative,NativeWindowStressHeatBalance.sigma,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,traceStress,map_sum,correction]
  abel

theorem heat_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    (∑ i : Coordinate,NativeWindowJointNormalForm.heatRate seed F radius time i i)=
      -nu.coeff • (∑ j : Coordinate,field (finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 2))+
        (2*nu.coeff) • physical (traceDiffusion seed time F) := by
  have jet_read (j : Coordinate) : field (finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 2)=
      ∑ i : Coordinate,field (finiteJet (NativeWindowJointHeat.frequencies F)
        (fun k => NativeWindowJointHeat.coefficients seed F radius time k i i) j 2) := by
    rw [jet_trace]
    exact map_sum (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm _ _
  simp only [NativeWindowJointHeat.heat_original seed F radius time closed,Finset.sum_add_distrib,← Finset.smul_sum,
    traceDiffusion,map_sum,jet_read]
  rw [Finset.sum_comm (f := fun i j => field (finiteJet (NativeWindowJointHeat.frequencies F)
    (fun k => NativeWindowJointHeat.coefficients seed F radius time k i i) j 2))]

theorem heatWork_identity (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) :
    heatWork seed F radius time= -nu.coeff*dirichlet seed F radius time-
      2*nu.coeff*(∫ point : Torus,traceInteraction seed time F point)-2*nu.coeff*crossWork seed F radius time := by
  have green (j : Coordinate) : inner ℝ
      (field (finiteSequence (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time)))
      (field (finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 2))=
        -‖field (finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 1)‖^2 := by
    simpa only [finiteJet,pow_zero,one_mul] using finite_green (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j
  rw [heatWork,heat_original seed F radius time closed,relative_original seed F radius time closed]
  simp only [inner_add_right,real_inner_smul_right,inner_neg_left,inner_sum,green,Finset.sum_neg_distrib]
  rw [field_original seed F radius time closed,inner_add_left,NativeWindowStressHeatSource.physical_inner]
  change _= -nu.coeff*dirichlet seed F radius time-2*nu.coeff*(∫ point : Torus,traceStress seed time F point*traceDiffusion seed time F point)-2*nu.coeff*crossWork seed F radius time
  dsimp only [dirichlet,crossWork]
  ring

theorem gradient_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (closed : ∀ k,k∈F →waveNeg k∈F) (j : Coordinate) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j displacement)
      (relative seed F radius time))
      (-field (finiteJet (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 1)) 0 := by
  have source := (finiteJet_hasDerivAt (NativeWindowJointHeat.frequencies F) (coefficients seed F radius time) j 0).neg
  simp only [finiteJet,pow_zero,one_mul] at source
  rw [relative_original seed F radius time closed]
  simpa only [NativePhysicalTranslation.translate,map_neg,Pi.neg_apply] using! source

end
end SaturationMonoid.NavierStokes.NativeWindowTraceEnergy

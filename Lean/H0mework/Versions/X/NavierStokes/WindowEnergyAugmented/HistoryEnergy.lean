import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchyEnergy
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryPairWindow

set_option autoImplicit false
open scoped BigOperators Topology Convolution ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHierarchyHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeFiniteActionResolvent NativeWindowAugmentedFixedOperator NativeWindowAugmentedTimeForm
open NativeResolventCompactness NativeUnheatedGlobalNegativeOne NativeWholeH1Mixed NativeWindowStressOseenTest
open NativePhysicalFourier NativeWindowHierarchyPairWindow NativeWindowStageNineSource NativeWindowStageNineWords
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

def wordRead (M : ℕ) (directions : List Coordinate) : State →L[ℝ] physicalSpace (modes M) :=
  (LinearMap.toContinuousLinearMap (word (modes M) (modes_zero M) (modes_closed M) directions)).comp (lift (modes M))

def fieldRead (M : ℕ) (F : Finset IntegerWavevector) (directions : List Coordinate) (i : Coordinate) :
    State →L[ℝ] C(Torus,ℝ) :=
  (LinearMap.toContinuousLinearMap (evaluate (modes M) F i)).comp (wordRead M directions)

def spectralPair (nu : Viscosity) (M : ℕ) (directions : List Coordinate) : State →L[ℝ] State →L[ℝ] ℝ :=
  ∑ k ∈ modes M,∑ i : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier k) •
    (innerSL ℝ).bilinearComp
      ((LinearMap.toContinuousLinearMap (rowRead (modes M) k i)).comp (wordRead M directions))
      ((LinearMap.toContinuousLinearMap (rowRead (modes M) k i)).comp (wordRead M directions))

def productPair (M : ℕ) (F : Finset IntegerWavevector) (directions : List Coordinate) (output input : Coordinate) :
    State →L[ℝ] State →L[ℝ] ScalarField :=
  ((ContinuousLinearMap.compL ℝ State C(Torus,ℝ) ScalarField) NativeWindowStressHeatSource.physical).comp
    ((ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp (fieldRead M F directions output) (fieldRead M F directions input))

def sampleEnergy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : ℝ :=
  NativeWindowStageNineWords.energy seed order observation (modes M) F radius
    (NativeWindowStageNineEnergy.values seed M order sample)

def history (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) : ℝ :=
  ∑ index : FixedMatterSpatialWordIndex order,
    (window seed (spectralPair nu M index.toList) kernelOrder observation+
      ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (matrixJet seed F radius 0 observation output input)
        (window seed (productPair M F index.toList output input) kernelOrder observation))

def coefficientRate (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) : ℝ :=
  ∑ index : FixedMatterSpatialWordIndex order,∑ output : Coordinate,∑ input : Coordinate,
    inner ℝ (matrixJet seed F radius 1 observation output input)
      (window seed (productPair M F index.toList output input) kernelOrder observation)

theorem history_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) :
    HasDerivAt (history seed M order F radius kernelOrder)
      (history seed M order F radius (kernelOrder+1) observation+
        coefficientRate seed M order F radius kernelOrder observation) observation := by
  have row (index : FixedMatterSpatialWordIndex order) (output input : Coordinate) :=
    (matrixJet_hasDerivAt seed F radius 0 observation output input).inner ℝ
      (window_hasDerivAt seed (productPair M F index.toList output input) kernelOrder observation)
  have fields (index : FixedMatterSpatialWordIndex order) := HasDerivAt.sum (u := Finset.univ) fun output _ =>
    HasDerivAt.sum (u := Finset.univ) fun input _ => row index output input
  have all := HasDerivAt.sum (u := Finset.univ) fun index _ =>
    (window_hasDerivAt seed (spectralPair nu M index.toList) kernelOrder observation).add (fields index)
  convert! all using 1
  · funext time
    simp only [history,Finset.sum_fn,Pi.add_apply]
  · simp only [history,coefficientRate,Finset.sum_add_distrib]
    ring

theorem sampleEnergy_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : sampleEnergy seed observation M order F radius sample=
      ∑ index : FixedMatterSpatialWordIndex order,(pair seed (spectralPair nu M index.toList) sample+
        ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (matrixJet seed F radius 0 observation output input)
          (pair seed (productPair M F index.toList output input) sample)) := by
  simp only [sampleEnergy,NativeWindowStageNineWords.energy,NativeWindowStageNineEnergy.values,
    test_pairing,physicalForm,LinearMap.add_apply,spectral,matrixPhysicalForm,LinearMap.mk₂_apply,
    NativeWindowAugmentedSourceForm.matrixRead,matrixJet_zero,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    spectralPair,productPair,pair,sum_apply,smul_apply,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.compL_apply,smul_eq_mul]
  rfl

theorem inner_window (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] ScalarField)
    (field : ScalarField) (kernelOrder : ℕ) (observation : ℝ) :
    inner ℝ field (window seed B kernelOrder observation)=
      ∫sample in observation+1..observation+2,NativeUnheatedStressPairEvolution.kernelWeight kernelOrder observation 0 sample •
        inner ℝ field (pair seed B sample) := by
  rw [window_original]
  have paid := ((pair_continuous seed B).intervalIntegrable (μ := volume) (a := observation+1) (b := observation+2)).continuousOn_smul
    (NativeUnheatedStressPairEvolution.kernelWeight_continuous kernelOrder observation 0).continuousOn
  simpa only [map_smul,innerSL_apply_apply] using! ((innerSL ℝ field).intervalIntegral_comp_comm paid).symm

theorem history_original (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) : history seed M order F radius kernelOrder observation=
      ∫sample in observation+1..observation+2,NativeUnheatedStressPairEvolution.kernelWeight kernelOrder observation 0 sample •
        sampleEnergy seed observation M order F radius sample := by
  let g:=NativeUnheatedStressPairEvolution.kernelWeight kernelOrder observation 0
  have scalar (index : FixedMatterSpatialWordIndex order) : IntervalIntegrable
      (fun sample => g sample • pair seed (spectralPair nu M index.toList) sample) volume (observation+1) (observation+2) :=
    ((pair_continuous seed _).intervalIntegrable (μ := volume) (a := observation+1) (b := observation+2)).continuousOn_smul
      (NativeUnheatedStressPairEvolution.kernelWeight_continuous kernelOrder observation 0).continuousOn
  have row (index : FixedMatterSpatialWordIndex order) (output input : Coordinate) : IntervalIntegrable
      (fun sample => g sample • inner ℝ (matrixJet seed F radius 0 observation output input)
        (pair seed (productPair M F index.toList output input) sample)) volume (observation+1) (observation+2) :=
    by
      simpa only [Function.comp_def,innerSL_apply_apply] using!
        (((innerSL ℝ (matrixJet seed F radius 0 observation output input)).continuous.comp
          (pair_continuous seed (productPair M F index.toList output input))).intervalIntegrable
            (μ := volume) (a := observation+1) (b := observation+2)).continuousOn_smul
          (NativeUnheatedStressPairEvolution.kernelWeight_continuous kernelOrder observation 0).continuousOn
  simp only [sampleEnergy_original,history,Finset.smul_sum,smul_add]
  have innerPaid (index : FixedMatterSpatialWordIndex order) (output : Coordinate) : IntervalIntegrable
      (fun sample => ∑ input : Coordinate,g sample • inner ℝ (matrixJet seed F radius 0 observation output input)
        (pair seed (productPair M F index.toList output input) sample)) volume (observation+1) (observation+2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun input _ => row index output input)
  have matrixPaid (index : FixedMatterSpatialWordIndex order) : IntervalIntegrable
      (fun sample => ∑ output : Coordinate,∑ input : Coordinate,g sample • inner ℝ (matrixJet seed F radius 0 observation output input)
        (pair seed (productPair M F index.toList output input) sample)) volume (observation+1) (observation+2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun output _ => innerPaid index output)
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun index _ => (scalar index).add (matrixPaid index))]
  apply Finset.sum_congr rfl
  intro index _
  rw [intervalIntegral.integral_add (scalar index)
    (matrixPaid index),window_original]
  congr 1
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun output _ => innerPaid index output)]
  apply Finset.sum_congr rfl
  intro output _
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun input _ => row index output input)]
  exact Finset.sum_congr rfl (fun input _ => inner_window seed _ _ _ _)

theorem history_initial (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    history seed M order F radius 0 (-2)=sampleEnergy seed (-2) M order F radius 0 := by
  simp only [history,window_initial seed _ (-2) le_rfl,sampleEnergy_original]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem history_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) (nonnegative : 0 ≤ observation) :
    history seed M order F radius kernelOrder (step.2.clockAdvance+observation)=history step.1 M order F radius kernelOrder observation := by
  simp only [history,window_next seed _ _ step generated observation nonnegative,matrixJet_zero,
    NativeWindowAugmentedSourceForm.matrixField,
    NativeWindowFiniteGramFourier.stress_next seed step generated observation nonnegative F,
    NativeWindowPressureStrainHistory.correction_next seed step generated radius observation nonnegative F]

end
end SaturationMonoid.NavierStokes.NativeWindowHierarchyHistory

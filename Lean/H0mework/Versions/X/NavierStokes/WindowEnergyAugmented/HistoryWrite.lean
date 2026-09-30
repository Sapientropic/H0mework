import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHierarchyWrite
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWindowAugmentedFixedOperator NativeWindowAugmentedTimeForm
open NativeResolventCompactness NativeUnheatedGlobalNegativeOne NativeWholeH1Mixed NativeWindowStressOseenSource
open NativePhysicalFourier NativeWindowHierarchyPairWindow NativeWindowHierarchyHistory
open NativeWindowStageNineSource NativeWindowStageNineWords NativeWindowOperatorGreen
open NativeUnheatedStressPairEvolution
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

def sampleRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : ℝ :=
  ∑ index : FixedMatterSpatialWordIndex order,
    (pairing (modes M) (NativeWindowStageNineSource.coefficientRate seed M index.toList sample)
      (test seed observation (modes M) (modes M) F radius (coefficient seed M index.toList sample))+
    pairing (modes M) (coefficient seed M index.toList sample)
      (test seed observation (modes M) (modes M) F radius (NativeWindowStageNineSource.coefficientRate seed M index.toList sample)))

theorem sampleRate_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : sampleRate seed observation M order F radius sample=
      ∑ index : FixedMatterSpatialWordIndex order,(action seed (spectralPair nu M index.toList) sample+
        ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (matrixJet seed F radius 0 observation output input)
          (action seed (productPair M F index.toList output input) sample)) := by
  simp only [sampleRate,test_pairing,physicalForm,LinearMap.add_apply,spectral,matrixPhysicalForm,LinearMap.mk₂_apply,
    NativeWindowAugmentedSourceForm.matrixRead,matrixJet_zero,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    spectralPair,productPair,action,sum_apply,smul_apply,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.compL_apply,smul_eq_mul,Finset.sum_add_distrib,inner_add_right,fieldRead,wordRead,coefficient,
    NativeWindowStageNineSource.coefficientRate,LinearMap.coe_toContinuousLinearMap',ContinuousLinearMap.mul_apply']
  ring

def spatialRow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (directions : List Coordinate) (sample : ℝ) : ℝ :=
  let B:=test seed observation (modes M) (modes M) F radius
  let D:=word (modes M) (modes_zero M) (modes_closed M) directions
  let U:=load M seed sample
  let V:=D U
  let commuted:=bracket D (NativeWindowStageNineSource.sourceOperator seed M sample) U+D (forcing seed M sample)
  pairing (modes M) V (lyapunov (modes M) (modes_zero M) (modes_closed M) nu
    (advector M seed sample) (advector_reality M seed sample) B V)+
    pairing (modes M) commuted (B V)+pairing (modes M) V (B commuted)

theorem sampleRate_spatial (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ∀ᵐ sample : ℝ,
    sampleRate seed observation M order F radius sample=
      if 0 ≤ sample then ∑ index : FixedMatterSpatialWordIndex order,spatialRow seed observation M F radius index.toList sample else 0 := by
  filter_upwards [source_action_ae seed M] with sample original
  by_cases nonnegative : 0 ≤ sample
  · rw [if_pos nonnegative,sampleRate]
    apply Finset.sum_congr rfl
    intro index _
    rw [NativeWindowStageNineSource.coefficientRate,coefficient,lift_load seed sample nonnegative,original nonnegative,map_add]
    simp only [map_add,LinearMap.add_apply,spatialRow]
    have green := word_green seed observation (modes M) F (modes_zero M) (modes_closed M) radius
      (advector M seed sample) (advector_reality M seed sample) index.toList (load M seed sample)
    dsimp only at green
    simp only [NativeWindowStageNineSource.sourceOperator]
    linarith only [green]
  · simp only [if_neg nonnegative,sampleRate,NativeWindowStageNineSource.coefficientRate,
      rate_before seed sample (lt_of_not_ge nonnegative),map_zero,LinearMap.zero_apply,zero_add,Finset.sum_const_zero]

theorem inner_action_window (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] ScalarField)
    (field : ScalarField) (kernelOrder : ℕ) (observation : ℝ) :
    inner ℝ field (window seed B (kernelOrder+1) observation)=
      ∫sample in observation+1..observation+2,kernelWeight kernelOrder observation 0 sample • inner ℝ field (action seed B sample) := by
  rw [window_write]
  have paid := (action_integrable seed B (observation+1) (observation+2)).continuousOn_smul
    (kernelWeight_continuous kernelOrder observation 0).continuousOn
  simpa only [map_smul,innerSL_apply_apply] using! ((innerSL ℝ field).intervalIntegral_comp_comm paid).symm

theorem history_movement (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) : history seed M order F radius (kernelOrder+1) observation=
      ∫sample in observation+1..observation+2,kernelWeight kernelOrder observation 0 sample •
        sampleRate seed observation M order F radius sample := by
  let g:=kernelWeight kernelOrder observation 0
  have scalar (index : FixedMatterSpatialWordIndex order) : IntervalIntegrable
      (fun sample => g sample • action seed (spectralPair nu M index.toList) sample) volume (observation+1) (observation+2) :=
    (action_integrable seed _ _ _).continuousOn_smul (kernelWeight_continuous kernelOrder observation 0).continuousOn
  have row (index : FixedMatterSpatialWordIndex order) (output input : Coordinate) : IntervalIntegrable
      (fun sample => g sample • inner ℝ (matrixJet seed F radius 0 observation output input)
        (action seed (productPair M F index.toList output input) sample)) volume (observation+1) (observation+2) := by
    let read:=innerSL ℝ (matrixJet seed F radius 0 observation output input)
    have paid:=action_integrable seed (productPair M F index.toList output input) (observation+1) (observation+2)
    have tested : IntervalIntegrable (fun sample => read (action seed (productPair M F index.toList output input) sample))
        volume (observation+1) (observation+2) := ⟨read.integrable_comp paid.1,read.integrable_comp paid.2⟩
    exact tested.continuousOn_smul (kernelWeight_continuous kernelOrder observation 0).continuousOn
  have innerPaid (index : FixedMatterSpatialWordIndex order) (output : Coordinate) : IntervalIntegrable
      (fun sample => ∑ input : Coordinate,g sample • inner ℝ (matrixJet seed F radius 0 observation output input)
        (action seed (productPair M F index.toList output input) sample)) volume (observation+1) (observation+2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun input _ => row index output input)
  have matrixPaid (index : FixedMatterSpatialWordIndex order) : IntervalIntegrable
      (fun sample => ∑ output : Coordinate,∑ input : Coordinate,g sample • inner ℝ (matrixJet seed F radius 0 observation output input)
        (action seed (productPair M F index.toList output input) sample)) volume (observation+1) (observation+2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun output _ => innerPaid index output)
  simp only [sampleRate_original,history,Finset.smul_sum,smul_add]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun index _ => (scalar index).add (matrixPaid index))]
  apply Finset.sum_congr rfl
  intro index _
  rw [intervalIntegral.integral_add (scalar index) (matrixPaid index),window_write]
  congr 1
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun output _ => innerPaid index output)]
  apply Finset.sum_congr rfl
  intro output _
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun input _ => row index output input)]
  exact Finset.sum_congr rfl (fun input _ => inner_action_window seed _ _ _ _)

def spatialRate (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) : ℝ :=
  ∫sample in observation+1..observation+2,kernelWeight kernelOrder observation 0 sample •
    sampleRate seed observation M order F radius sample

theorem whole_history_write (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius kernelOrder : ℕ) (observation : ℝ) :
    HasDerivAt (history seed M order F radius kernelOrder)
      (spatialRate seed M order F radius kernelOrder observation+
        NativeWindowHierarchyHistory.coefficientRate seed M order F radius kernelOrder observation) observation := by
  simpa only [history_movement,spatialRate] using history_hasDerivAt seed M order F radius kernelOrder observation

end
end SaturationMonoid.NavierStokes.NativeWindowHierarchyWrite

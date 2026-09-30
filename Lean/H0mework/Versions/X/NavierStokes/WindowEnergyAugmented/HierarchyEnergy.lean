import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchyWords
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchySource

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowStageNineEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowOperatorGreen NativeWindowAugmentedFixedOperator
open NativeWindowAugmentedTimeForm NativeWindowStageNineWords NativeWindowStageNineSource
open NativeUnheatedGlobalNegativeOne NativeWholeH1Mixed NativeWindowStressOseenSource NativeWindowStressOseenTest
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

theorem moving_energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) (f : ℝ →physicalSpace M) (f' : physicalSpace M) (actual : HasDerivAt f f' time) :
    HasDerivAt (fun t => pairing M (f t) (test seed t M M F radius (f t)))
      (quadraticJet seed M F radius 1 time (f time)+
        pairing M f' (test seed time M M F radius (f time))+
        pairing M (f time) (test seed time M M F radius f')) time := by
  have readDerivative (k : IntegerWavevector) (i : Coordinate) : HasDerivAt
      (fun t => rowRead M k i (f t)) (rowRead M k i f') time :=
    (LinearMap.toContinuousLinearMap (rowRead M k i)).hasFDerivAt.comp_hasDerivAt time actual
  have spectralRow (k : IntegerWavevector) (i : Coordinate) :=
    ((readDerivative k i).inner ℝ (readDerivative k i)).const_mul (1+nu.coeff*integerWaveViscousMultiplier k)
  have spectralRate := HasDerivAt.sum (u := M) fun k _ => HasDerivAt.sum (u := Finset.univ) fun i _ => spectralRow k i
  have evaluated (i : Coordinate) : HasDerivAt (fun t => evaluate M F i (f t)) (evaluate M F i f') time :=
    (LinearMap.toContinuousLinearMap (evaluate M F i)).hasFDerivAt.comp_hasDerivAt time actual
  have product (output input : Coordinate) : HasDerivAt
      (fun t => NativeWindowStressHeatSource.physical (evaluate M F output (f t)*evaluate M F input (f t)))
      (NativeWindowStressHeatSource.physical
        (evaluate M F output f'*evaluate M F input (f time)+evaluate M F output (f time)*evaluate M F input f')) time :=
    NativeWindowStressHeatSource.physical.hasFDerivAt.comp_hasDerivAt time ((evaluated output).mul (evaluated input))
  have row (output input : Coordinate) :=
    (matrixJet_hasDerivAt seed F radius 0 time output input).inner ℝ (product output input)
  have rows := HasDerivAt.sum (u := Finset.univ) fun output _ => HasDerivAt.sum (u := Finset.univ) fun input _ => row output input
  have all := spectralRate.add rows
  convert! all using 1
  · funext t
    rw [actual_pairing]
    simp only [spectral,LinearMap.mk₂_apply,quadraticJet,Finset.sum_fn,Pi.add_apply]
  · simp only [test_pairing,physicalForm,spectral,quadraticJet,matrixJet_zero,matrixPhysicalForm,
      LinearMap.add_apply,LinearMap.mk₂_apply,NativeWindowAugmentedSourceForm.matrixRead,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,map_add,inner_add_right,
      Finset.sum_add_distrib,mul_add]
    ring

def values (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    FixedMatterSpatialWordIndex order →physicalSpace (modes M) :=
  fun index => coefficient seed M index.toList time

def sourceEnergy (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) : ℝ := energy seed order time (modes M) F radius (values seed M order time)

def sourceTimeRate (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) : ℝ := timeRate seed order time (modes M) F radius (values seed M order time)

def spatialRow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (directions : List Coordinate) (time : ℝ) : ℝ :=
  let B:=test seed time (modes M) (modes M) F radius
  let D:=word (modes M) (modes_zero M) (modes_closed M) directions
  let U:=load M seed time
  let V:=D U
  let commuted:=bracket D (sourceOperator seed M time) U+D (forcing seed M time)
  pairing (modes M) V (lyapunov (modes M) (modes_zero M) (modes_closed M) nu
    (advector M seed time) (advector_reality M seed time) B V)+
    pairing (modes M) commuted (B V)+pairing (modes M) V (B commuted)

def sourceSpatialRate (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) : ℝ := ∑ index : FixedMatterSpatialWordIndex order,spatialRow seed M F radius index.toList time

theorem spatialRow_original_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) : ∀ᵐ time : ℝ,0 ≤ time →∀ directions : List Coordinate,
      pairing (modes M) (coefficientRate seed M directions time)
          (test seed time (modes M) (modes M) F radius (coefficient seed M directions time))+
        pairing (modes M) (coefficient seed M directions time)
          (test seed time (modes M) (modes M) F radius (coefficientRate seed M directions time))=
      spatialRow seed M F radius directions time := by
  filter_upwards [source_action_ae seed M] with time original nonnegative directions
  rw [coefficientRate,coefficient,lift_load seed time nonnegative,original nonnegative,map_add]
  simp only [map_add,LinearMap.add_apply,spatialRow]
  have green := word_green seed time (modes M) F (modes_zero M) (modes_closed M) radius
    (advector M seed time) (advector_reality M seed time) directions (load M seed time)
  dsimp only at green
  simp only [NativeWindowStageNineSource.sourceOperator]
  linarith only [green]

theorem sourceEnergy_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ∀ᵐ time : ℝ,0<time →
      HasDerivAt (sourceEnergy seed M order F radius)
        (sourceTimeRate seed M order F radius time+sourceSpatialRate seed M order F radius time) time := by
  have derivatives := ae_all_iff.2 (fun index : FixedMatterSpatialWordIndex order =>
    coefficient_hasDerivAt_ae seed M index.toList)
  filter_upwards [derivatives,spatialRow_original_ae seed M F radius] with time actual original positive
  have paid := HasDerivAt.sum (u := Finset.univ) fun index _ =>
    moving_energy_hasDerivAt seed (modes M) F radius time _ _ (actual index positive)
  simp only [Finset.sum_fn] at paid
  convert! paid using 1
  simp only [sourceTimeRate,sourceSpatialRate,timeRate,values,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  rw [← original positive.le index.toList]
  ring

theorem source_energy_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius M order,
      ∀ᵐ time : ℝ,time∈Ioc 0 horizon →
        deriv (sourceEnergy seed M order (integerWaveFrequencyCube outerRadius) radius) time≤
          C*sourceEnergy seed M order (integerWaveFrequencyCube outerRadius) radius time+
            sourceSpatialRate seed M order (integerWaveFrequencyCube outerRadius) radius time := by
  obtain ⟨low,C,C0,paid⟩ := source_hierarchy_control seed horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius M order => ?_⟩
  filter_upwards [sourceEnergy_hasDerivAt_ae seed M order (integerWaveFrequencyCube outerRadius) radius] with time actual inside
  rw [(actual inside.1).deriv]
  have estimate := (paid radius above outerRadius order (modes M) (modes_zero M) (modes_closed M)
    time ⟨inside.1.le,inside.2⟩ (values seed M order time)).2
  exact add_le_add ((le_abs_self _).trans estimate) le_rfl

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem test_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (M F : Finset IntegerWavevector) (radius : ℕ) :
    test seed (step.2.clockAdvance+time) M M F radius=test step.1 time M M F radius := by
  have matrix : NativeWindowAugmentedSourceForm.matrixField seed (step.2.clockAdvance+time) F radius=
      NativeWindowAugmentedSourceForm.matrixField step.1 time F radius := by
    funext output input
    simp only [NativeWindowAugmentedSourceForm.matrixField,
      NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative F,
      NativeWindowPressureStrainHistory.correction_next seed step generated radius time nonnegative F]
  simp only [test,physicalForm,matrixPhysicalForm,NativeWindowAugmentedSourceForm.matrixRead,matrix]

theorem sourceEnergy_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    sourceEnergy seed M order F radius (step.2.clockAdvance+time)=sourceEnergy step.1 M order F radius time := by
  simp only [sourceEnergy,energy,values,coefficient_next seed step generated _ _ time nonnegative,
    test_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowStageNineEnergy

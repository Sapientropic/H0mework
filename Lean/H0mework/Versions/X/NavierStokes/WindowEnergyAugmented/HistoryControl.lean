import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryWrite
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.PreparationControl
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchyInitialEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHierarchyControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWindowAugmentedFixedOperator NativeWindowAugmentedTimeForm
open NativeWindowHierarchyPairWindow NativeWindowHierarchyHistory NativeWindowHierarchyWrite
open NativeWindowStageNineSource NativeWholeH1Mixed NativePhysicalFourier NativeUnheatedStressPairEvolution
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
attribute [local fun_prop] NativeWindowHierarchyPairWindow.pair_continuous

def sampleCoefficient (seed : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
    RationalVorticityEvaluator.butterflyGainViscosity) (observation : ℝ) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : ℝ :=
  ∑ index : FixedMatterSpatialWordIndex order,∑ output : Coordinate,∑ input : Coordinate,
    inner ℝ (matrixJet seed F radius 1 observation output input)
      (pair seed (productPair M F index.toList output input) sample)

theorem sampleCoefficient_original (observation : ℝ) (M order : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) : sampleCoefficient stackedShortCurrent observation M order F radius sample=
      ∑ index : FixedMatterSpatialWordIndex order,quadraticJet stackedShortCurrent (modes M) F radius 1 observation
        (coefficient stackedShortCurrent M index.toList sample) := by
  simp only [sampleCoefficient,quadraticJet,productPair,NativeWindowHierarchyPairWindow.pair,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.bilinearComp_apply]
  rfl

theorem sampleCoefficient_continuous (observation : ℝ) (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    Continuous (sampleCoefficient stackedShortCurrent observation M order F radius) := by
  unfold sampleCoefficient
  fun_prop

theorem sampleEnergy_continuous (observation : ℝ) (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    Continuous (sampleEnergy stackedShortCurrent observation M order F radius) := by
  simp only [funext (sampleEnergy_original stackedShortCurrent observation M order F radius)]
  fun_prop

theorem coefficient_integral (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (observation : ℝ) :
    NativeWindowHierarchyHistory.coefficientRate stackedShortCurrent M order F radius 0 observation=
      ∫sample in observation+1..observation+2,kernelWeight 0 observation 0 sample •
        sampleCoefficient stackedShortCurrent observation M order F radius sample := by
  let term (key : FixedMatterSpatialWordIndex order×(Coordinate×Coordinate)) (sample : ℝ) :=
    kernelWeight 0 observation 0 sample • inner ℝ (matrixJet stackedShortCurrent F radius 1 observation key.2.1 key.2.2)
      (pair stackedShortCurrent (productPair M F key.1.toList key.2.1 key.2.2) sample)
  have paid (key : FixedMatterSpatialWordIndex order×(Coordinate×Coordinate)) :
      IntervalIntegrable (term key) volume (observation+1) (observation+2) := by
    have continuous : Continuous (fun sample => inner ℝ (matrixJet stackedShortCurrent F radius 1 observation key.2.1 key.2.2)
        (pair stackedShortCurrent (productPair M F key.1.toList key.2.1 key.2.2) sample)) :=
      continuous_const.inner (pair_continuous _ _)
    exact (continuous.intervalIntegrable (μ := volume) (observation+1) (observation+2)).continuousOn_smul
      (kernelWeight_continuous 0 observation 0).continuousOn
  have sum := intervalIntegral.integral_finsetSum (s := Finset.univ) (fun key _ => paid key)
  simp only [NativeWindowHierarchyHistory.coefficientRate,inner_window,sampleCoefficient,Finset.smul_sum]
  simpa only [term,Fintype.sum_prod_type] using sum.symm

theorem kernel_nonnegative (observation sample : ℝ) : 0 ≤ kernelWeight 0 observation 0 sample :=
  NativeForwardWindowSource.kernel_nonnegative _

theorem source_coefficient_bound (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius M order,∀ observation∈Icc (-2 : ℝ) horizon,
      |NativeWindowHierarchyHistory.coefficientRate stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 observation|≤
        C*history stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 observation := by
  obtain ⟨low,C,C0,paid⟩ := NativeWindowPreparedAugmentedControl.source_time_bound horizon nonnegative 1
  refine ⟨low,C,C0,fun radius above outerRadius M order observation inside => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  have point (sample : ℝ) : |sampleCoefficient stackedShortCurrent observation M order F radius sample|≤
      C*sampleEnergy stackedShortCurrent observation M order F radius sample := by
    rw [sampleCoefficient_original]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have tested:=Finset.sum_le_sum (s := (Finset.univ : Finset (FixedMatterSpatialWordIndex order))) fun index _ =>
      paid radius above outerRadius (modes M) (modes_zero M) (modes_closed M) observation inside
        (coefficient stackedShortCurrent M index.toList sample)
    exact tested.trans_eq (by simp only [sampleEnergy,NativeWindowStageNineWords.energy,NativeWindowStageNineEnergy.values,Finset.mul_sum,F])
  have timeOrder : observation+1 ≤ observation+2 := by linarith
  have coefficientPaid := ((sampleCoefficient_continuous observation M order F radius).intervalIntegrable (μ := volume) (observation+1) (observation+2)).continuousOn_smul
    (kernelWeight_continuous 0 observation 0).continuousOn
  have energyPaid := ((sampleEnergy_continuous observation M order F radius).intervalIntegrable (μ := volume) (observation+1) (observation+2)).continuousOn_smul
    (kernelWeight_continuous 0 observation 0).continuousOn
  rw [coefficient_integral,← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm timeOrder).trans
  have integrated := intervalIntegral.integral_mono_on timeOrder coefficientPaid.norm (energyPaid.const_mul C)
    (fun sample _ => by
      rw [norm_smul,Real.norm_of_nonneg (kernel_nonnegative observation sample),Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (point sample) (kernel_nonnegative observation sample)).trans_eq (by simp only [smul_eq_mul]; ring))
  exact integrated.trans_eq (by rw [intervalIntegral.integral_const_mul,← history_original])

theorem source_history_gate (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius M order,∀ observation∈Icc (-2 : ℝ) horizon,
      deriv (history stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0) observation≤
        spatialRate stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 observation+
          C*history stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 observation := by
  obtain ⟨low,C,C0,paid⟩ := source_coefficient_bound horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius M order observation inside => ?_⟩
  rw [(whole_history_write stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 observation).deriv]
  exact add_le_add le_rfl ((le_abs_self _).trans (paid radius above outerRadius M order observation inside))

theorem source_history_initial : ∃ low : ℕ,∀ order : ℕ,0≤NativeWindowStageNineInitialEnergy.budget order ∧
    ∀ radius≥low,∀ outerRadius M,
      history stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 (-2)≤
        NativeWindowStageNineInitialEnergy.budget order := by
  obtain ⟨low,paid⟩ := NativeWindowStageNineInitialEnergy.source_initial_energy
  refine ⟨low,fun order => ⟨(paid order).1,fun radius above outerRadius M => ?_⟩⟩
  rw [history_initial]
  exact (paid order).2 radius above outerRadius M

theorem source_history_nonnegative (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ outerRadius M order,∀ observation∈Icc (-2 : ℝ) horizon,
      0≤history stackedShortCurrent M order (integerWaveFrequencyCube outerRadius) radius 0 observation := by
  obtain ⟨low,paid⟩ := NativeWindowPreparedAugmentedControl.source_coercivity horizon nonnegative
  refine ⟨low,fun radius above outerRadius M order observation inside => ?_⟩
  have point (sample : ℝ) : 0 ≤ sampleEnergy stackedShortCurrent observation M order (integerWaveFrequencyCube outerRadius) radius sample := by
    apply Finset.sum_nonneg
    intro index _
    let v:=coefficient stackedShortCurrent M index.toList sample
    have mass : 0≤pairing (modes M) v v := by
      change (0 : ℝ) ≤ inner ℝ (coefficients (modes M) v) (coefficients (modes M) v)
      exact real_inner_self_nonneg
    have gradient : 0≤NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1 := by
      unfold NativeCommonAdvectorAction.curlPair
      apply Finset.sum_nonneg
      intro wave _
      rw [ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval.complexCoordinateRealInner_self]
      exact ThreeDimensionalVorticityCoefficientStretchingPairTable.complexCoordinateVectorNormSq_nonneg _
    exact (add_nonneg mass (mul_nonneg (by positivity [RationalVorticityEvaluator.butterflyGainViscosity.coeff_pos]) gradient)).trans
      (paid radius above (modes M) (integerWaveFrequencyCube outerRadius) (modes_zero M) (modes_closed M)
        (NativeWindowFiniteGramFourier.cube_closed outerRadius) observation inside v)
  rw [history_original,intervalIntegral.integral_of_le (by linarith : observation+1 ≤ observation+2)]
  exact integral_nonneg (fun sample => mul_nonneg (kernel_nonnegative observation sample) (point sample))

end
end SaturationMonoid.NavierStokes.NativeWindowHierarchyControl

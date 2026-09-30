import H0mework.NavierStokes.WindowEnergyTraceDual.Energy
import H0mework.NavierStokes.WindowEnergyAugmented.GlobalGreen
import H0mework.NavierStokes.WindowEnergyAugmented.HistoryPairWindow

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowTraceDualWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowStressOseenTest NativeWindowStressOseenSource
open NativeWindowAugmentedFixedOperator (spectral rowRead load_reads read_equal)
open NativeWindowTraceOperator (test test_pairing)
open NativeWindowStressHeatSource (physical)
open NativeUnheatedGlobalNegativeOne NativeResolventCompactness
open NativeUnheatedStressPairEvolution (kernelWeight)
open NativeWindowFiniteStressUniform (kernelBound)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) : physicalSpace (modes M) :=
  NativeWindowStageNineSource.lift (modes M) (state seed sample)

theorem value_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (value seed M) :=
  (NativeWindowStageNineSource.lift (modes M)).continuous.comp (NativeWindowHierarchyPairWindow.state_continuous seed)

theorem value_load (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample) :
    value seed M sample=load M seed sample := NativeWindowStageNineSource.lift_load seed sample nonnegative M

def sampleEnergy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (sample : ℝ) : ℝ :=
  pairing (modes M) (value seed M sample) (test seed observation (modes M) (modes M) F radius (value seed M sample))

theorem spectral_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample) :
    spectral nu (modes M) (modes M) (value seed M sample) (value seed M sample)=
      NativeWindowAugmentedGlobalGreen.spectralValue seed (modes M) sample := by
  rw [value_load seed M sample nonnegative,NativeWindowAugmentedGlobalGreen.spectralValue_original]
  simp only [spectral,LinearMap.mk₂_apply,real_inner_self_eq_norm_sq]
  apply Finset.sum_congr rfl
  intro wave member
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← load_reads seed sample nonnegative M (modes M) (fun _ inside _ => inside) wave member i]
  rfl

theorem value_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample)
    (F : Finset IntegerWavevector) (cover : ∀ k∈F,k≠0 →k∈modes M) (i : Coordinate) :
    evaluate (modes M) F i (value seed M sample)=NativeWindowStressHeatTime.field seed F i sample := by
  rw [value_load seed M sample nonnegative]
  exact (read_equal (modes M) F _ (state seed sample) (load_reads seed sample nonnegative M F cover) i).symm

theorem sample_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes M)
    (sample : ℝ) (nonnegative : 0 ≤ sample) : sampleEnergy seed observation M F radius sample=
      NativeWindowAugmentedGlobalGreen.spectralValue seed (modes M) sample+
        ∑ i : Coordinate,inner ℝ (NativeWindowTraceOperator.field seed observation F radius)
          (physical (NativeWindowStressHeatTime.product seed F i i sample)) := by
  rw [sampleEnergy,test_pairing,NativeWindowTraceOperator.form,LinearMap.add_apply,LinearMap.add_apply,
    spectral_original seed M sample nonnegative]
  simp only [NativeWindowTraceOperator.matrixForm,LinearMap.mk₂_apply,NativeWindowTraceOperator.read,
    ContinuousLinearMap.comp_apply,innerSL_apply_apply,value_read seed M sample nonnegative F cover,
    NativeWindowStressHeatTime.product]

def energyWindow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∫sample in observation+1..observation+2,kernelWeight 0 observation 0 sample • sampleEnergy seed observation M F radius sample

private theorem product_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (i : Coordinate) :
    Continuous (NativeWindowStressHeatTime.product seed F i i) :=
  ((NativeWindowStressHeatTime.read F i).continuous.comp (NativeWindowHierarchyPairWindow.state_continuous seed)).mul
    ((NativeWindowStressHeatTime.read F i).continuous.comp (NativeWindowHierarchyPairWindow.state_continuous seed))

private theorem weighted_product (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (observation : ℝ) (i : Coordinate) : IntervalIntegrable
      (fun sample => kernelWeight 0 observation 0 sample • NativeWindowStressHeatTime.product seed F i i sample)
      volume (observation+1) (observation+2) :=
  ((product_continuous seed F i).intervalIntegrable (μ := volume) _ _).continuousOn_smul
    (NativeUnheatedStressPairEvolution.kernelWeight_continuous 0 observation 0).continuousOn

private theorem product_window (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (F : Finset IntegerWavevector) (radius : ℕ) (i : Coordinate) :
    (∫sample in observation+1..observation+2,kernelWeight 0 observation 0 sample •
      NativeWindowTraceOperator.read seed observation F radius (NativeWindowStressHeatTime.product seed F i i sample))=
        NativeWindowTraceOperator.read seed observation F radius (NativeWindowFiniteGramFourier.stress seed observation F i i) := by
  have original : (∫sample in observation+1..observation+2,kernelWeight 0 observation 0 sample •
      NativeWindowStressHeatTime.product seed F i i sample)=NativeWindowFiniteGramFourier.stress seed observation F i i := by
    rw [← NativeWindowStressHeatTime.kernel_integral]
    exact NativeWindowStressHeatTime.jet_zero seed F i i observation
  have applied := (NativeWindowTraceOperator.read seed observation F radius).intervalIntegral_comp_comm
    (weighted_product seed F observation i)
  rw [original] at applied
  simpa only [map_smul] using applied

theorem energyWindow_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0≤observation)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes M) :
    energyWindow seed observation M F radius=NativeWindowAugmentedGlobalGreen.spectralWindow seed (modes M) 0 observation+
      inner ℝ (NativeWindowTraceOperator.field seed observation F radius) (physical (NativeWindowTraceGradient.traceStress seed observation F)) := by
  have spectralPaid : IntervalIntegrable (fun sample => kernelWeight 0 observation 0 sample •
      NativeWindowAugmentedGlobalGreen.spectralValue seed (modes M) sample) volume (observation+1) (observation+2) :=
    ((NativeWindowHierarchyPairWindow.pair_continuous seed (NativeWindowAugmentedSourceForm.spectralForm nu (modes M))).intervalIntegrable
      (μ := volume) _ _).continuousOn_smul (NativeUnheatedStressPairEvolution.kernelWeight_continuous 0 observation 0).continuousOn
  have rowPaid (i : Coordinate) : IntervalIntegrable (fun sample => kernelWeight 0 observation 0 sample •
      NativeWindowTraceOperator.read seed observation F radius (NativeWindowStressHeatTime.product seed F i i sample))
      volume (observation+1) (observation+2) :=
    (((NativeWindowTraceOperator.read seed observation F radius).continuous.comp (product_continuous seed F i)).intervalIntegrable
      (μ := volume) _ _).continuousOn_smul (NativeUnheatedStressPairEvolution.kernelWeight_continuous 0 observation 0).continuousOn
  have same : energyWindow seed observation M F radius=
      ∫sample in observation+1..observation+2,kernelWeight 0 observation 0 sample •
        (NativeWindowAugmentedGlobalGreen.spectralValue seed (modes M) sample+
          ∑ i : Coordinate,NativeWindowTraceOperator.read seed observation F radius (NativeWindowStressHeatTime.product seed F i i sample)) := by
    apply intervalIntegral.integral_congr
    intro sample inside
    rw [uIcc_of_le (by linarith : observation+1≤observation+2)] at inside
    dsimp only
    rw [sample_original seed observation M F radius cover sample (by linarith [inside.1])]
    rfl
  rw [same]
  simp only [smul_add,Finset.smul_sum]
  rw [intervalIntegral.integral_add spectralPaid (by simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun i _ => rowPaid i)),
    intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => rowPaid i)]
  have spectrum : (∫sample in observation+1..observation+2,kernelWeight 0 observation 0 sample •
      NativeWindowAugmentedGlobalGreen.spectralValue seed (modes M) sample)=
        NativeWindowAugmentedGlobalGreen.spectralWindow seed (modes M) 0 observation := by
    rw [NativeWindowAugmentedGlobalGreen.spectralWindow,
      NativeWindowFiniteStressUniform.average_original 0 observation observation ⟨nonnegative,le_rfl⟩,
      NativeWindowStressHeatTime.kernel_integral]
  rw [spectrum]
  congr 1
  simp only [NativeWindowTraceGradient.traceStress,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact product_window seed observation F radius i

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  (1+nu.coeff*(2*Real.pi)^2)*kernelBound 0*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)+
      9*(NativeWindowAugmentedPayment.stressBudget seed 0 horizon+1)*NativeWindowAugmentedPayment.stressBudget seed 0 horizon

theorem source_energy_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ outerRadius M,∀ time∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube outerRadius,k≠0 →k∈modes M) →
        energyWindow seed time M (integerWaveFrequencyCube outerRadius) radius≤budget seed horizon := by
  obtain ⟨low,paid⟩ := NativeWindowJointNormalForm.correctionJet_small seed 0 horizon nonnegative 1 (by norm_num)
  refine ⟨low,fun radius above outerRadius M time inside cover => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  let B:=NativeWindowAugmentedPayment.stressBudget seed 0 horizon
  have stress (i : Coordinate) : ‖physical (NativeWindowFiniteGramFourier.stress seed time F i i)‖≤B := by
    rw [← NativeWindowAugmentedPayment.stressJet_zero seed outerRadius time inside.1]
    exact NativeWindowAugmentedPayment.stressJet_bound seed outerRadius 0 time horizon inside i i
  have B0 : 0≤B := (norm_nonneg _).trans (stress 0)
  have entry (i : Coordinate) : ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius i i‖≤B+1 := by
    have small := (paid radius above F time inside i i).le
    rw [NativeWindowJointNormalForm.correctionJet_zero] at small
    exact (norm_add_le _ _).trans (add_le_add (stress i) small)
  have first : ‖NativeWindowTraceOperator.field seed time F radius‖≤3*(B+1) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => entry i).trans_eq (by simp; ring))
  have last : ‖physical (NativeWindowTraceGradient.traceStress seed time F)‖≤3*B := by
    rw [NativeWindowTraceGradient.traceStress,map_sum]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => stress i).trans_eq (by simp))
  have matrix : inner ℝ (NativeWindowTraceOperator.field seed time F radius)
      (physical (NativeWindowTraceGradient.traceStress seed time F))≤9*(B+1)*B :=
    (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
      ((mul_le_mul first last (norm_nonneg _) (by positivity)).trans_eq (by ring)))
  rw [energyWindow_original seed time inside.1 M F radius cover]
  have spectralBound := (le_abs_self _).trans (NativeWindowAugmentedGlobalGreen.spectralWindow_bound seed (modes M) 0 time horizon inside)
  exact add_le_add spectralBound matrix

theorem pairing_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (P Q : Module.End ℝ (physicalSpace (modes M))) :
    Continuous (fun sample => pairing (modes M) (P (value seed M sample)) (Q (value seed M sample))) := by
  have first := (LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp
    ((LinearMap.toContinuousLinearMap P).continuous.comp (value_continuous seed M))
  have last := (LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp
    ((LinearMap.toContinuousLinearMap Q).continuous.comp (value_continuous seed M))
  exact first.inner (𝕜 := ℝ) last

end
end SaturationMonoid.NavierStokes.NativeWindowTraceDualWindow

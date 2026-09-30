import H0mework.NavierStokes.WindowEnergyTraceCut.CutActionSource
import H0mework.NavierStokes.WindowEnergyConvection.CutoffOperatorTime
import H0mework.NavierStokes.WindowEnergyTraceTerminal.GraphHeat

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutActionPhysical
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeWindowOperatorGreen NativeResolventAdjoint
open NativePhysicalFourier
open NativeWindowStressHeatSource (physical)
open NativeWindowTraceAdjoint (value)
open NativeWindowTraceCutAction (diagonal window)
open NativeWindowConvectionCutoffTrace (relative timeWork)
open NativeWindowAugmentedPayment (graphSample graphJet graphBudget stressJet stressBudget)
open NativeUnheatedStressPairEvolution (kernelWeight)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem graph_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) (sample0 : 0 ≤ sample) :
    pairing (modes M) (value seed M sample) (laplacian (modes M) (modes_zero M) (modes_closed M) nu (value seed M sample))=
      graphSample seed (modes M) sample := by
  rw [laplacian_pairing,NativeWindowAugmentedTestProduct.curl_original (modes M) _ (modes_zero M),
    NativeWindowAugmentedPayment.graphSample_original]
  apply congrArg (fun U : ComplexVorticityHilbertState => (2*Real.pi)^2*NativeUnheatedStressProduct.gradientMass U)
  apply lp.ext
  funext k
  rw [NativeUnheatedWindowStress.projection,complexSharpSupportProjection_apply,complexSharpSupportProjection_apply,
    ← NativeUnifiedCompleteSource.velocity_read seed sample]
  change (if k∈modes M then (value seed M sample).1 k else 0)=
    (if k∈modes M then NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed sample).fst k else 0)
  split_ifs with inside
  · funext i
    have read:=NativeWindowAugmentedFixedOperator.load_reads seed sample sample0 M (modes M) (fun _ member _ => member) k inside i
    change NativeUnheatedTriadRows.velocity seed sample k i=_ at read
    rw [NativeUnheatedTriadRows.velocity_original] at read
    change _=(NativeWindowStressOseenSource.load M seed sample).1 k i at read
    change (NativeWindowTraceDualWindow.value seed M sample).1 k i=_
    rw [NativeWindowTraceDualWindow.value_load seed M sample sample0]
    exact read.symm
  · rfl

theorem diagonal_physical (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (sample : ℝ) (sample0 : 0 ≤ sample) (cover : ∀ k∈F,k≠0 →k∈modes M) :
    diagonal seed frame M F radius sample=
      (∑ i : Coordinate,inner ℝ (relative seed F radius frame) (physical (NativeWindowStressHeatTime.product seed F i i sample)))-
        nu.coeff*graphSample seed (modes M) sample := by
  rw [NativeWindowTraceCutAction.diagonal,NativeWindowTraceEndpointWindow.terminal,
    NativeWindowTraceCutOperator.jointTest_physical seed frame (modes M) F radius (modes_zero M) (modes_closed M),graph_original seed M sample sample0]
  have read (i : Coordinate):=NativeWindowTraceDualWindow.value_read seed M sample sample0 F cover i
  simp only [show value seed M sample=NativeWindowTraceDualWindow.value seed M sample from rfl,read,NativeWindowStressHeatTime.product]

def matrix (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (F : Finset IntegerWavevector) (radius order : ℕ) : ℝ :=
  ∑ i : Coordinate,inner ℝ (relative seed F radius frame) (physical (NativeWindowStressHeatTime.jet seed F i i order sampling))

theorem pair_window_physical (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (sampling0 : 0 ≤ sampling)
    (M : ℕ) (F : Finset IntegerWavevector) (radius order : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes M) :
    NativeWindowHierarchyPairWindow.window seed (NativeWindowTraceCutAction.form seed frame M F radius) order sampling=matrix seed frame sampling F radius order-
      nu.coeff*graphJet seed (modes M) order sampling := by
  let read:=(innerSL ℝ (relative seed F radius frame)).comp physical
  have products (i : Coordinate):IntervalIntegrable
      (fun sample => kernelWeight order sampling 0 sample • NativeWindowStressHeatTime.product seed F i i sample)
      volume (sampling+1) (sampling+2) := by
    have continuous:Continuous (NativeWindowStressHeatTime.product seed F i i) :=
      ((NativeWindowStressHeatTime.read F i).continuous.comp (NativeWindowHierarchyPairWindow.state_continuous seed)).mul
        ((NativeWindowStressHeatTime.read F i).continuous.comp (NativeWindowHierarchyPairWindow.state_continuous seed))
    exact (continuous.intervalIntegrable _ _).continuousOn_smul (NativeUnheatedStressPairEvolution.kernelWeight_continuous _ _ _).continuousOn
  have rows (i : Coordinate):IntervalIntegrable
      (fun sample => kernelWeight order sampling 0 sample • read (NativeWindowStressHeatTime.product seed F i i sample))
      volume (sampling+1) (sampling+2) := by
    have paid:IntervalIntegrable (fun sample => read (kernelWeight order sampling 0 sample •
        NativeWindowStressHeatTime.product seed F i i sample)) volume (sampling+1) (sampling+2) :=
      ⟨read.integrable_comp (products i).1,read.integrable_comp (products i).2⟩
    simpa only [map_smul] using paid
  have graphPaid:IntervalIntegrable (fun sample => kernelWeight order sampling 0 sample •
      graphSample seed (modes M) sample) volume (sampling+1) (sampling+2) :=
    ((NativeWindowAugmentedPayment.graphSample_continuous seed (modes M)).intervalIntegrable _ _).continuousOn_smul
      (NativeUnheatedStressPairEvolution.kernelWeight_continuous _ _ _).continuousOn
  rw [NativeWindowHierarchyPairWindow.window_original,← NativeWindowTraceCutAction.diagonal_original]
  have same : (fun sample => kernelWeight order sampling 0 sample • diagonal seed frame M F radius sample)=ᵐ[
      volume.restrict (uIoc (sampling+1) (sampling+2))] fun sample =>
      (∑ i : Coordinate,kernelWeight order sampling 0 sample • read (NativeWindowStressHeatTime.product seed F i i sample))-
      nu.coeff*(kernelWeight order sampling 0 sample • graphSample seed (modes M) sample) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with sample inside
    rw [uIoc_of_le (by linarith : sampling+1 ≤ sampling+2)] at inside
    rw [diagonal_physical seed frame M F radius sample (by linarith [inside.1]) cover]
    simp only [smul_eq_mul,mul_sub,Finset.mul_sum,read,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
    ring
  have sumPaid:IntervalIntegrable (fun sample => ∑ i : Coordinate,kernelWeight order sampling 0 sample •
      read (NativeWindowStressHeatTime.product seed F i i sample)) volume (sampling+1) (sampling+2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun i _ => rows i)
  rw [intervalIntegral.integral_congr_ae_restrict same,
    intervalIntegral.integral_sub sumPaid (graphPaid.const_mul nu.coeff),
    intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => rows i),intervalIntegral.integral_const_mul]
  have row (i : Coordinate) : (∫sample in sampling+1..sampling+2,kernelWeight order sampling 0 sample •
      read (NativeWindowStressHeatTime.product seed F i i sample))=read (NativeWindowStressHeatTime.jet seed F i i order sampling) := by
    have original : (∫sample in sampling+1..sampling+2,kernelWeight order sampling 0 sample •
        NativeWindowStressHeatTime.product seed F i i sample)=NativeWindowStressHeatTime.jet seed F i i order sampling :=
      (NativeWindowStressHeatTime.kernel_integral _ _ _).symm
    have applied:=read.intervalIntegral_comp_comm (products i)
    rw [original] at applied
    simpa only [map_smul] using applied
  simp only [row]
  rw [← NativeWindowStressHeatTime.kernel_integral]
  rfl

theorem window_physical (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (sampling0 : 0 ≤ sampling)
    (M : ℕ) (F : Finset IntegerWavevector) (radius order : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes M) :
    window seed frame sampling M F radius order=matrix seed frame sampling F radius (order+1)-
      nu.coeff*graphJet seed (modes M) (order+1) sampling := by
  rw [NativeWindowTraceCutAction.weighted_write seed frame sampling sampling0]
  exact pair_window_physical seed frame sampling sampling0 M F radius (order+1) cover

theorem pair_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ order : ℕ,∃ C : ℝ,0≤C ∧∀ radius≥low,∀ cutoff≥low,∀ M : ℕ,
      ∀ frame∈Icc 0 horizon,∀ sampling∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
        ‖NativeWindowHierarchyPairWindow.window seed (NativeWindowTraceCutAction.form seed frame M (integerWaveFrequencyCube cutoff) radius) order sampling‖≤C := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowTraceCutTime.source_field_bound seed horizon nonnegative 0
  refine ⟨low,fun order => ⟨max 0 (3*B*stressBudget seed order horizon+nu.coeff*graphBudget seed order horizon),
    le_max_left _ _,fun radius above cutoff covered M frame frameInside sampling sampleInside cover => ?_⟩⟩
  let F:=integerWaveFrequencyCube cutoff
  have relativeBound:‖relative seed F radius frame‖≤B := by
    rw [← norm_neg,← NativeWindowTraceCutTime.fieldJet_zero]
    exact source radius above cutoff covered frame frameInside
  have row (i : Coordinate) : ‖inner ℝ (relative seed F radius frame)
      (physical (NativeWindowStressHeatTime.jet seed F i i order sampling))‖≤B*stressBudget seed order horizon := by
    have last:=NativeWindowAugmentedPayment.stressJet_bound seed cutoff order sampling horizon sampleInside i i
    rw [NativeWindowAugmentedPayment.stressJet_original seed cutoff order sampling sampleInside.1] at last
    exact (norm_inner_le_norm _ _).trans (mul_le_mul relativeBound last (norm_nonneg _) B0)
  have matrixBound:‖matrix seed frame sampling F radius order‖≤3*B*stressBudget seed order horizon :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))
  rw [pair_window_physical seed frame sampling sampleInside.1 M F radius order cover]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Real.norm_of_nonneg nu.coeff_pos.le]
  exact (add_le_add matrixBound (mul_le_mul_of_nonneg_left
    (NativeWindowAugmentedPayment.graphJet_bound seed (modes M) order sampling horizon sampleInside) nu.coeff_pos.le)).trans (le_max_right _ _)

theorem source_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ order : ℕ,∃ C : ℝ,0≤C ∧∀ radius≥low,∀ cutoff≥low,∀ M : ℕ,
      ∀ frame∈Icc 0 horizon,∀ sampling∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
        ‖window seed frame sampling M (integerWaveFrequencyCube cutoff) radius order‖≤C := by
  obtain ⟨low,paid⟩:=pair_uniform seed horizon nonnegative
  refine ⟨low,fun order => ?_⟩
  obtain ⟨C,C0,bounded⟩:=paid (order+1)
  refine ⟨C,C0,fun radius above cutoff covered M frame fi sampling si cover => ?_⟩
  rw [NativeWindowTraceCutAction.weighted_write seed frame sampling si.1]
  exact bounded radius above cutoff covered M frame fi sampling si cover

theorem energy_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    HasDerivAt (NativeWindowConvectionCutoffTrace.energy seed F radius)
      (-matrix seed time time F radius 1-timeWork seed F radius time) time := by
  have velocity:HasDerivAt (relative seed F radius) (-NativeWindowTraceCutTime.fieldJet seed F radius 1 time) time := by
    convert! (NativeWindowTraceCutTime.fieldJet_hasDerivAt seed F radius 0 time).neg using 1
    funext sample
    simp only [Pi.neg_apply,NativeWindowTraceCutTime.fieldJet_zero,neg_neg]
  have generated:=velocity.norm_sq.const_mul (1/2 : ℝ)
  convert! generated using 1
  simp only [NativeWindowTraceCutTime.fieldJet_split,inner_neg_right,inner_sum,inner_add_right,matrix,
    timeWork,Finset.sum_add_distrib]
  ring

theorem source_time_identity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (time0 : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes M) :
    deriv (NativeWindowConvectionCutoffTrace.energy seed F radius) time+window seed time time M F radius 0+
      nu.coeff*graphJet seed (modes M) 1 time+timeWork seed F radius time=0 := by
  rw [(energy_derivative seed F radius time).deriv,window_physical seed time time time0 M F radius 0 cover]
  ring

theorem source_graph_identity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (time0 : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (closed : ∀ k,k∈F →waveNeg k∈F)
    (cover : ∀ k∈F,k≠0 →k∈modes M) :
    nu.coeff*NativeWindowTraceTerminalGraphHeat.gradientCross seed F radius time+
      NativeWindowTraceTerminalGraph.remainderEnergy seed time M F radius+NativeWindowConvectionCutoffTrace.strainWork seed F radius time=
    NativeWindowTraceEndpointWindow.terminalEnergy seed time M F radius-
      nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M time-window seed time time M F radius 0-
      nu.coeff*graphJet seed (modes M) 1 time-NativeWindowConvectionCutoffTrace.lowAdvWork seed F radius time-
      NativeWindowConvectionCutoffTrace.lowPressureWork seed F radius time := by
  have original:=NativeWindowTraceTerminalGraphHeat.source_generator_identity seed time time0 M F radius closed cover
  have temporal:=source_time_identity seed time time0 M F radius cover
  linarith only [original,temporal]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutActionPhysical

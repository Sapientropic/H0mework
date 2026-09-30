import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowJets
import H0mework.Versions.X.NavierStokes.WindowPhysics.SpacetimeVelocity
import H0mework.Versions.X.NavierStokes.WindowPhysics.SpacetimeStress

/-! The original window consumes the full source tail, with no spatial heat parameter.
The source clock and the kernel are unchanged. -/

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWindowTailMoments

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open NativeFullOrderAction NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativeEndpointVelocityCarrier NativeForwardWindowJets
open NativeCompleteStressAction

noncomputable section
variable {nu : Viscosity}

def tailBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : ℝ :=
  NativeGeneratedGlobalControl.windowBudget (NativeEventualTailControl.sourceWindow seed)
    (NativeEventualTailControl.sourceTail seed) horizon order

theorem original_tail_moments (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed)
      (NativeAbsoluteEventualControl.startTime seed + horizon)) (order : ℕ) :
    Summable (velocityMomentDensity order
      (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)) ∧
      (∑' wave, velocityMomentDensity order
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave) ≤
          tailBudget seed horizon order := by
  rw [NativeUnifiedCompleteSource.velocity_read,
    NativeAbsoluteEventualControl.velocity_reads_tail seed time inside.1]
  exact NativeGeneratedGlobalControl.global_moment_control
    (NativeEventualTailControl.sourceWindow seed)
    (NativeEventualTailControl.sourceWindow_first seed)
    (NativeEventualTailControl.sourceWindow_last seed)
    (NativeEventualTailControl.sourceTail seed) horizon order
    ⟨time - NativeAbsoluteEventualControl.startTime seed, sub_nonneg.mpr inside.1, by linarith [inside.2]⟩

theorem kernelJet_interval (rank : ℕ) (shift : ℝ) (nonzero : kernelJet rank shift ≠ 0) :
    shift ∈ Icc (-2 : ℝ) (-1 : ℝ) := by
  have inside := kernelJet_support rank (subset_closure nonzero)
  change shift ∈ tsupport (NativeForwardWindowSource.bump.normed volume) at inside
  rw [NativeForwardWindowSource.bump.tsupport_normed_eq, Metric.mem_closedBall,
    Real.dist_eq, abs_le] at inside
  change -(1 / 2 : ℝ) ≤ shift - -3 / 2 ∧ shift - -3 / 2 ≤ (1 / 2 : ℝ) at inside
  constructor <;> linarith [inside.1, inside.2]

theorem original_tail_coefficient_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed)
      (NativeAbsoluteEventualControl.startTime seed + horizon)) (order : ℕ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    frequencySize wave ^ order *
      ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave coordinate‖ ≤
        Real.sqrt (tailBudget seed horizon order) := by
  have paid := original_tail_moments seed horizon time inside order
  have component :
      ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave coordinate‖ ^ 2 ≤
      complexCoordinateVectorNormSq (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_left component (sq_nonneg _)).trans
    ((paid.1.le_tsum wave (fun k _ => by
      apply mul_nonneg (sq_nonneg _)
      exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).trans paid.2)

theorem jet_integrable (seed : GeneratedWholeRestartCurrent nu) (rank : ℕ) (time : ℝ) :
    Integrable (fun shift : ℝ => kernelJet rank shift • NativeUnifiedCompleteSource.source seed (time - shift)) :=
  (kernelJet_compact rank).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernelJet_smooth rank).continuous (NativeForwardWindowSource.original_locallyIntegrable seed) time

theorem jet_read_integral (seed : GeneratedWholeRestartCurrent nu) (rank : ℕ) (time : ℝ)
    (read : FullSpace →L[ℝ] ℂ) :
    read (jet seed rank time) =
      ∫ shift : ℝ, kernelJet rank shift • read (NativeUnifiedCompleteSource.source seed (time - shift)) := by
  change read (∫ shift : ℝ, kernelJet rank shift • NativeUnifiedCompleteSource.source seed (time - shift)) = _
  rw [← read.integral_comp_comm (jet_integrable seed rank time)]
  apply integral_congr_ae
  filter_upwards with shift
  exact map_smul read (kernelJet rank shift) _

theorem jet_read_tail_bound (seed : GeneratedWholeRestartCurrent nu)
    (read : FullSpace →L[ℝ] ℂ) (horizon time : ℝ) (rank order : ℕ)
    (wave : IntegerWavevector) (bound : ℝ)
    (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (bounded : ∀ actual ∈ Icc (NativeAbsoluteEventualControl.startTime seed) (horizon + 2),
      frequencySize wave ^ order * ‖read (NativeUnifiedCompleteSource.source seed actual)‖ ≤ bound) :
    frequencySize wave ^ order * ‖read (jet seed rank time)‖ ≤
      (∫ shift : ℝ, ‖kernelJet rank shift‖) * bound := by
  have dominated (shift : ℝ) :
      ‖(frequencySize wave ^ order) • (kernelJet rank shift •
        read (NativeUnifiedCompleteSource.source seed (time - shift)))‖ ≤
        ‖kernelJet rank shift‖ * bound := by
    by_cases zero : kernelJet rank shift = 0
    · simp [zero]
    · have support := kernelJet_interval rank shift zero
      have actual : time - shift ∈ Icc (NativeAbsoluteEventualControl.startTime seed) (horizon + 2) := by
        constructor <;> linarith [inside.1, inside.2, support.1, support.2]
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg (frequencySize_nonneg wave) order)]
      simpa only [mul_left_comm] using
        mul_le_mul_of_nonneg_left (bounded (time - shift) actual) (norm_nonneg (kernelJet rank shift))
  have written := norm_integral_le_of_norm_le
    ((kernelJet_integrable rank).norm.mul_const bound) (Eventually.of_forall dominated)
  rw [integral_smul, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (frequencySize_nonneg wave) order),
    ← jet_read_integral, integral_mul_const] at written
  exact written

def velocityBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (rank order : ℕ) : ℝ :=
  (∫ shift : ℝ, ‖kernelJet rank shift‖) *
    Real.sqrt (tailBudget seed (horizon + 2 - NativeAbsoluteEventualControl.startTime seed) order)

theorem window_velocity_coefficient_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    frequencySize wave ^ order * ‖wholeVelocity (jet seed rank time).fst wave coordinate‖ ≤
      velocityBudget seed horizon rank order := by
  let read := (NativeWindowSpacetimeVelocity.read wave coordinate).comp NativeForwardWindowEvolution.velocityRead
  apply jet_read_tail_bound seed read horizon time rank order wave
    (Real.sqrt (tailBudget seed (horizon + 2 - NativeAbsoluteEventualControl.startTime seed) order)) inside
  intro actual member
  exact original_tail_coefficient_bound seed _ actual
    ⟨member.1, by linarith [member.2]⟩ order wave coordinate

theorem window_velocity_decay (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    frequencySize wave ^ order * ‖wholeVelocity (jet seed rank time).fst wave coordinate‖ ≤
      velocityBudget seed horizon rank (order + 4) * decay wave := by
  have paid := window_velocity_coefficient_bound seed horizon time inside rank (order + 4) wave coordinate
  calc
    _ = (frequencySize wave ^ (order + 4) * ‖wholeVelocity (jet seed rank time).fst wave coordinate‖) * decay wave := by
      unfold decay
      rw [pow_add]
      field_simp [(frequencySize_pos wave).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right paid (sq_nonneg _)

theorem original_tail_stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed ≤ time) :
    NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source seed time).snd =
      NativeStressSource.quadraticFlux (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
  have offset_pos : 0 < NativeEventualTailControl.offset seed := by
    have advancing := elapsedTime_strictMono (NativeEventualTailControl.terminal seed).terminal (by norm_num : 0 < 2)
    simpa only [NativeEventualTailControl.offset, elapsedTime_zero] using advancing
  have later : NativeFiniteMacroPhysical.clock (NativeEventualTailControl.terminal seed).arrival < time := by
    change NativeFiniteMacroPhysical.clock (NativeEventualTailControl.terminal seed).arrival +
      NativeEventualTailControl.offset seed ≤ time at inside
    linarith
  rw [NativeUnifiedCompleteSource.stress_read, NativeUnifiedCompleteSource.velocity_read]
  simp only [NativeUnifiedGlobalStressSource.stress, NativeUnifiedGlobalStressSource.source,
    NativeUnifiedGlobalStressSource.global, endpointSplice_of_lt _ _ _ _ later,
    NativeAbsoluteEventualControl.velocity, NativeFiniteMacroGlobal.globalPath,
    NativeUnifiedGlobalStressSource.ordinary]

def tailAmplitudeBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  (tailBudget seed horizon 2 + ∑' wave, decay wave) / 2

theorem original_tail_amplitude (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed)
      (NativeAbsoluteEventualControl.startTime seed + horizon)) :
    Summable (amplitude (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)) ∧
      (∑' wave, amplitude (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave) ≤
        tailAmplitudeBudget seed horizon := by
  have paid := original_tail_moments seed horizon time inside 2
  have same : (fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave)) =
      velocityMomentDensity 2 (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
    funext wave
    simp only [velocityMomentDensity, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      ← pow_mul]
  have squarePaid : Summable fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave) := by
    rw [same]
    exact paid.1
  have bound := moment_le_square_payment (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) 0 squarePaid
  rw [same] at bound
  simp only [pow_zero, one_mul] at bound
  exact ⟨by simpa only [pow_zero, one_mul] using summable_moment_of_square _ 0 squarePaid,
    bound.trans (div_le_div_of_nonneg_right (add_le_add paid.2 le_rfl) (by norm_num))⟩

def tailStressBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : ℝ :=
  Real.sqrt ((2 * 2 ^ order) ^ 2 * tailAmplitudeBudget seed horizon ^ 2 * tailBudget seed horizon order)

theorem original_tail_stress_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed)
      (NativeAbsoluteEventualControl.startTime seed + horizon)) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    frequencySize wave ^ order *
      ‖NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source seed time).snd wave output input‖ ≤
        tailStressBudget seed horizon order := by
  rw [original_tail_stress seed time inside.1]
  have paid := original_tail_moments seed horizon time inside order
  have majorant := original_tail_amplitude seed horizon time inside
  have flux := flux_moment_control order (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    majorant.1 paid.1 output input
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, ← Complex.normSq_eq_norm_sq]
  have single := flux.1.le_tsum wave (fun k _ =>
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
  apply (single.trans flux.2).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact pow_le_pow_left₀ (tsum_nonneg (fun k => vorticityRowAmplitude_nonneg _ k)) majorant.2 2
  · exact paid.2
  · exact tsum_nonneg fun k => by
      apply mul_nonneg (sq_nonneg _)
      exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

def stressBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (rank order : ℕ) : ℝ :=
  (∫ shift : ℝ, ‖kernelJet rank shift‖) *
    tailStressBudget seed (horizon + 2 - NativeAbsoluteEventualControl.startTime seed) order

theorem window_stress_coefficient_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) :
    frequencySize wave ^ order * ‖NativeCompleteStressCarrier.read (jet seed rank time).snd wave output input‖ ≤
      stressBudget seed horizon rank order := by
  let read := NativeWindowSpacetimeStress.read wave (output, input)
  apply jet_read_tail_bound seed read horizon time rank order wave
    (tailStressBudget seed (horizon + 2 - NativeAbsoluteEventualControl.startTime seed) order) inside
  intro actual member
  exact original_tail_stress_bound seed _ actual
    ⟨member.1, by linarith [member.2]⟩ order wave output input

theorem window_stress_decay (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) :
    frequencySize wave ^ order * ‖NativeCompleteStressCarrier.read (jet seed rank time).snd wave output input‖ ≤
      stressBudget seed horizon rank (order + 4) * decay wave := by
  have paid := window_stress_coefficient_bound seed horizon time inside rank (order + 4) wave output input
  calc
    _ = (frequencySize wave ^ (order + 4) * ‖NativeCompleteStressCarrier.read (jet seed rank time).snd wave output input‖) * decay wave := by
      unfold decay
      rw [pow_add]
      field_simp [(frequencySize_pos wave).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right paid (sq_nonneg _)

theorem window_velocity_absolute_moment (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (coordinate : Coordinate) :
    Summable (fun wave => frequencySize wave ^ order *
      ‖wholeVelocity (jet seed rank time).fst wave coordinate‖) ∧
      (∑' wave, frequencySize wave ^ order * ‖wholeVelocity (jet seed rank time).fst wave coordinate‖) ≤
        velocityBudget seed horizon rank (order + 4) * ∑' wave, decay wave := by
  have bounded := window_velocity_decay seed horizon time inside rank order
  have majorant := decay_summable.mul_left (velocityBudget seed horizon rank (order + 4))
  have paid := majorant.of_nonneg_of_le
    (fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order) (norm_nonneg _))
    (fun wave => bounded wave coordinate)
  refine ⟨paid, ?_⟩
  simpa only [tsum_mul_left] using paid.tsum_le_tsum (fun wave => bounded wave coordinate) majorant

theorem window_stress_absolute_moment (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (output input : Coordinate) :
    Summable (fun wave => frequencySize wave ^ order *
      ‖NativeCompleteStressCarrier.read (jet seed rank time).snd wave output input‖) ∧
      (∑' wave, frequencySize wave ^ order * ‖NativeCompleteStressCarrier.read (jet seed rank time).snd wave output input‖) ≤
        stressBudget seed horizon rank (order + 4) * ∑' wave, decay wave := by
  have bounded := window_stress_decay seed horizon time inside rank order
  have majorant := decay_summable.mul_left (stressBudget seed horizon rank (order + 4))
  have paid := majorant.of_nonneg_of_le
    (fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order) (norm_nonneg _))
    (fun wave => bounded wave output input)
  refine ⟨paid, ?_⟩
  simpa only [tsum_mul_left] using paid.tsum_le_tsum (fun wave => bounded wave output input) majorant

end
end SaturationMonoid.NavierStokes.NativeWindowTailMoments

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow
import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.FinitePointClock

open Complex Filter FourierTransform MeasureTheory Set
open OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
open OriginalRSourceJointContact.OutsideHistory.ClockReconstruction
open scoped Topology ContDiff
open private right_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric

local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation

/-- The source and its actual R response jointly produce the inward time derivative. -/
def generatorWrite (c : BurnolCompletedMellinCoordinate) (old : BurnolL2) : BurnolL2 :=
  (c.value / 2 - 1 / 4) • R c old + old

private theorem orbit_has_derivative (c : BurnolCompletedMellinCoordinate) (old : BurnolL2) (t : ℝ) :
    HasDerivAt (fun h : ℝ => D (-h / 2) (R c old)) (D (-t / 2) (generatorWrite c old)) t := by
  have origin : HasDerivAt (fun h : ℝ => D (-h / 2) (R c old)) (generatorWrite c old) (t-t) := by
    rw [sub_self]
    exact burnolDirectRightResolventOrbit_hasDerivAt (c.value / 2) (right_quarter c) old
  have translate : HasDerivAt (fun h : ℝ => h-t) 1 t := (hasDerivAt_id t).sub_const t
  have shifted := HasDerivAt.scomp (h := fun h : ℝ => h-t) t origin translate
  simp only [one_smul, Function.comp_def] at shifted
  let U := (D (-t / 2)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have acted := U.hasFDerivAt.comp_hasDerivAt t shifted
  have same : (fun h : ℝ => U (D (-(h-t) / 2) (R c old))) =
      (fun h : ℝ => D (-h / 2) (R c old)) := by
    funext h
    change D (-t / 2) (D (-(h-t) / 2) (R c old)) = _
    rw [burnolMultiplicativeDilation_add, show -t/2 + -(h-t)/2 = -h/2 by ring]
  change HasDerivAt (fun h : ℝ => U (D (-(h-t) / 2) (R c old)))
    (U (generatorWrite c old)) t at acted
  rw [same] at acted
  exact acted

theorem actual_time_cost (c : BurnolCompletedMellinCoordinate) (old : BurnolL2) (t h : ℝ) :
    ‖D (-t / 2) (R c old) - D (-h / 2) (R c old)‖ ≤ ‖generatorWrite c old‖ * ‖t-h‖ := by
  let orbit (s : ℝ) := D (-s/2) (R c old)
  let slope (s : ℝ) := D (-s/2) (generatorWrite c old)
  have differentiated (s : ℝ) : HasDerivWithinAt orbit (slope s) univ s :=
    (orbit_has_derivative c old s).hasDerivWithinAt
  have bounded (s : ℝ) : ‖slope s‖ ≤ ‖generatorWrite c old‖ := by
    change ‖D (-s/2) (generatorWrite c old)‖ ≤ _
    rw [(D (-s/2)).norm_map]
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := orbit) (f' := slope) (s := univ) (x := h) (y := t)
    (fun s _ => differentiated s) (fun s _ => bounded s) convex_univ (mem_univ h) (mem_univ t)

/-- The radius is bounded by the positive clock, so the whole window lies in positive time. -/
def clockBump (n : ℕ) (radius : ℝ) (positive : 0 < radius) : ContDiffBump (2 * clock n) :=
  let outer := min (clock n) radius
  have outerPositive : 0 < outer := lt_min (clock_pos n) positive
  ⟨outer / 2, outer, half_pos outerPositive, half_lt_self outerPositive⟩

private def compensated {t₀ : ℝ} (b : ContDiffBump t₀) : ℝ → ℂ :=
  fun t => ((b.normed volume t * Real.exp (t / 8) : ℝ) : ℂ)

private def compensatedSchwartz {t₀ : ℝ} (b : ContDiffBump t₀) : SchwartzMap ℝ ℂ := by
  have compact : HasCompactSupport (fun t : ℝ => b.normed volume t * Real.exp (t / 8)) :=
    (b.hasCompactSupport_normed (μ := volume)).mul_right
  have support : Function.support (compensated b) =
      Function.support (fun t : ℝ => b.normed volume t * Real.exp (t / 8)) := by
    ext t
    simp [compensated]
  have smooth : ContDiff ℝ ∞ (compensated b) := by
    exact Complex.ofRealCLM.contDiff.comp
      (b.contDiff_normed.mul (Real.contDiff_exp.comp (contDiff_id.div_const 8)))
  exact (show HasCompactSupport (compensated b) by
    unfold HasCompactSupport tsupport at compact ⊢
    rwa [support]).toSchwartzMap smooth

/-- Fourier inversion of the positive-time window cancels the original 3/8 damping. -/
def clockTest {t₀ : ℝ} (b : ContDiffBump t₀) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (compensatedSchwartz b)

private theorem compensated_read {t₀ : ℝ} (b : ContDiffBump t₀) (t : ℝ) :
    𝓕 (clockTest b : ℝ → ℂ) t = compensated b t := by
  rw [← SchwartzMap.fourier_coe, clockTest, FourierTransform.fourier_fourierInv_eq]
  rfl

private theorem normed_support {t₀ t : ℝ} (b : ContDiffBump t₀) (live : b.normed volume t ≠ 0) :
    ‖t-t₀‖ < b.rOut := by
  have located : t ∈ Function.support (b.normed volume) := live
  rw [b.support_normed_eq, Metric.mem_ball, dist_eq_norm] at located
  exact located

section Observe
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (Q : BurnolL2 →L[ℂ] E)

omit [CompleteSpace E] in
private theorem exact_clock_average {t₀ : ℝ} (b : ContDiffBump t₀) (inside : b.rOut ≤ t₀) (v : BurnolL2) :
    windowRead Q (clockTest b) v =
      ∫ t : ℝ, b.normed volume t • Q (D (-t/2) v) := by
  rw [windowRead, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases live : b.normed volume t = 0
  · by_cases tPos : t ∈ Ioi (0 : ℝ)
    · simp only [indicator_of_mem tPos, compensated_read, compensated, live, zero_mul,
        Complex.ofReal_zero, zero_smul]
    · simp only [indicator_of_notMem tPos, live, zero_smul]
  · have distance := normed_support b live
    rw [Real.norm_eq_abs, abs_lt] at distance
    have tPos : t ∈ Ioi (0 : ℝ) := by
      change 0 < t
      linarith [distance.1]
    rw [indicator_of_mem tPos, compensated_read, compensated, burnolDirectRightResolventIntegrand,
      map_smul, smul_smul]
    have damping : positiveMellinQuarterRightResolventWeight (3/8) t =
        (Real.exp (-(t / 8)) : ℂ) := by
      unfold positiveMellinQuarterRightResolventWeight
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [damping, ← Complex.ofReal_mul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rfl

/-- The actual R-generated derivative controls the error of the normalized time window. -/
theorem actual_clock_window_time_error (c : BurnolCompletedMellinCoordinate) (old : BurnolL2)
    {t₀ : ℝ} (b : ContDiffBump t₀) (inside : b.rOut ≤ t₀) :
    ‖windowRead Q (clockTest b) (R c old) - Q (D (-t₀/2) (R c old))‖ ≤
      ‖Q‖ * ‖generatorWrite c old‖ * b.rOut := by
  let signal (t : ℝ) := Q (D (-t/2) (R c old))
  have continuousSignal : Continuous signal :=
    Q.continuous.comp ((burnolMultiplicativeDilation_stronglyContinuous (R c old)).comp (by fun_prop))
  have avg : Integrable (fun t : ℝ => b.normed volume t • signal t) := by
    apply ((b.integrable_normed (μ := volume)).mul_const (‖Q‖ * ‖R c old‖)).mono'
      (b.continuous_normed.smul continuousSignal).aestronglyMeasurable
    filter_upwards with t
    change ‖b.normed volume t • signal t‖ ≤ b.normed volume t * (‖Q‖ * ‖R c old‖)
    rw [norm_smul, Real.norm_of_nonneg (b.nonneg_normed t)]
    apply mul_le_mul_of_nonneg_left _ (b.nonneg_normed t)
    change ‖Q (D (-t/2) (R c old))‖ ≤ _
    simpa only [(D (-t/2)).norm_map] using Q.le_opNorm (D (-t/2) (R c old))
  rw [exact_clock_average Q b inside]
  have balance : (∫ t : ℝ, b.normed volume t • (signal t - signal t₀)) =
      (∫ t : ℝ, b.normed volume t • signal t) - signal t₀ := by
    simp_rw [smul_sub]
    rw [integral_sub avg ((b.integrable_normed (μ := volume)).smul_const _),
      b.integral_normed_smul volume]
  change ‖(∫ t : ℝ, b.normed volume t • signal t) - signal t₀‖ ≤ _
  rw [← balance]
  let K := ‖Q‖ * ‖generatorWrite c old‖ * b.rOut
  have unit : (∫ t : ℝ, b.normed volume t * K) = K := by
    rw [integral_mul_const, b.integral_normed, one_mul]
  change ‖∫ t : ℝ, b.normed volume t • (signal t - signal t₀)‖ ≤ K
  rw [← unit]
  apply norm_integral_le_of_norm_le ((b.integrable_normed (μ := volume)).mul_const K)
  filter_upwards with t
  by_cases live : b.normed volume t = 0
  · simp only [live, zero_smul, norm_zero, zero_mul, le_refl]
  · rw [norm_smul, Real.norm_of_nonneg (b.nonneg_normed t)]
    apply mul_le_mul_of_nonneg_left _ (b.nonneg_normed t)
    change ‖Q (D (-t/2) (R c old)) - Q (D (-t₀/2) (R c old))‖ ≤ K
    rw [← map_sub]
    apply (Q.le_opNorm _).trans
    dsimp only [K]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg Q)
    exact (actual_time_cost c old t t₀).trans
      (mul_le_mul_of_nonneg_left (normed_support b live).le (norm_nonneg _))

end Observe
end OriginalRSourceJointContact.OutsideHistory.FinitePointClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.OutsideHistory

open BurnolPhysicalState SourceGeneratedActionObservationHistory Filter Set
open scoped Topology
open OriginalRSourceJointContact.OutsideHistory.ClockReconstruction
open OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
open OriginalRSourceJointContact.OutsideHistory.FinitePointClock
open private step_total from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.Kernel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "A" => sourceStep observation nontrivial half
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "P" => burnolEvenAmbientProjectionEndomorphism
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "R" => burnolDirectRightResolventCLM
local notation "Dilation" => burnolMultiplicativeDilation
local notation "T" => Inv.pairTotal

/-- Use one literal head and a finite window of the positive successor slots. -/
def finiteClockPair (n : ℕ) (radius : ℝ) (positive : 0 < radius) (W N : ℕ)
    (history : completion A outsideRead) : SourcePair :=
  let head := stageRead A outsideRead 0 history 0
  let field := recordedWindow observation nontrivial half (clockTest (clockBump n radius positive)) W N history
  (Dilation (clock n) field - head, head)

variable (depth : ℕ)
local notation "source" => D.input observation nontrivial half depth

/-- The initial predecessor is the original first R result on the same Xi receipt. -/
def clockPredecessor : ℕ → BurnolL2
  | 0 => R c (OriginalKCombPhysicalAction.value observation nontrivial depth half)
  | ordinal+1 => T (source ordinal)

theorem actual_clock_predecessor (ordinal : ℕ) :
    R c (clockPredecessor observation nontrivial half depth ordinal) = T (source ordinal) := by
  cases ordinal with
  | zero =>
    have origin := OriginalKCombFirstFullSourceDynamics.raw_origin observation nontrivial half depth
    simp only [OriginalKCombCofinalRAction.original_R_direct] at origin
    exact origin.symm
  | succ ordinal =>
    change R c (T (source ordinal)) = T (source (ordinal+1))
    rw [← actual_source_step observation nontrivial half depth ordinal, step_total]

/-- The original predecessor pays the time error of each literal current. The head is exact. -/
theorem actual_finite_clock_error (n : ℕ) (radius : ℝ) (positive : 0 < radius) (ε : ℝ)
    (precision : 0 < ε) :
    ∃ W N : ℕ, ∀ ordinal : ℕ,
      let old := clockPredecessor observation nontrivial half depth ordinal
      let next := T (source ordinal)
      ‖finiteClockPair observation nontrivial half n radius positive W N
          (sourceMap A outsideRead (source ordinal)) - source ordinal‖ ≤
        ‖P (Dilation (-clock n) next)‖ + ‖O‖ * ‖generatorWrite c old‖ * radius +
          8 * ‖O‖ * ‖next‖ * ε := by
  let bump := clockBump n radius positive
  obtain ⟨W,N,window⟩ := actual_recorded_window_precise observation nontrivial half depth
    (clockTest bump) ε precision
  refine ⟨W,N,fun ordinal => ?_⟩
  let old := clockPredecessor observation nontrivial half depth ordinal
  let next := T (source ordinal)
  let estimate := recordedWindow observation nontrivial half (clockTest bump) W N
    (sourceMap A outsideRead (source ordinal))
  let average := windowRead O (clockTest bump) next
  let point := O (Dilation (-clock n) next)
  have action : R c old = next := actual_clock_predecessor observation nontrivial half depth ordinal
  have fits : bump.rOut ≤ 2 * clock n :=
    (min_le_left (clock n) radius).trans (by linarith [clock_pos n])
  have time := actual_clock_window_time_error O c old bump fits
  rw [action, show -(2 * clock n)/2 = -clock n by ring] at time
  have timeBound : ‖average - point‖ ≤ ‖O‖ * ‖generatorWrite c old‖ * radius :=
    time.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
  have frequency : ‖estimate - average‖ ≤ 8 * ‖O‖ * ‖next‖ * ε := by
    rw [norm_sub_rev]
    exact window ordinal
  have estimatedPoint : ‖estimate - point‖ ≤
      ‖O‖ * ‖generatorWrite c old‖ * radius + 8 * ‖O‖ * ‖next‖ * ε := by
    calc
      _ = ‖(estimate - average) + (average - point)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖estimate - average‖ + ‖average - point‖ := norm_add_le _ _
      _ ≤ 8 * ‖O‖ * ‖next‖ * ε + ‖O‖ * ‖generatorWrite c old‖ * radius :=
        add_le_add frequency timeBound
      _ = _ := add_comm _ _
  have head :
      stageRead A outsideRead 0 (sourceMap A outsideRead (source ordinal)) 0 =
        (source ordinal).2 := by
    rw [source_reads_stage]
    rfl
  rw [finiteClockPair, head]
  change ‖(Dilation (clock n) estimate - (source ordinal).2 - (source ordinal).1,
    (source ordinal).2 - (source ordinal).2)‖ ≤ _
  rw [sub_self, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have first : Dilation (clock n) estimate - (source ordinal).2 - (source ordinal).1 =
      Dilation (clock n) estimate - next := by
    change _ = Dilation (clock n) estimate - ((source ordinal).1 + (source ordinal).2)
    abel
  rw [first]
  calc
    _ = ‖(Dilation (clock n) point - next) +
          (Dilation (clock n) estimate - Dilation (clock n) point)‖ := by
      rw [add_comm, sub_add_sub_cancel]
    _ ≤ ‖Dilation (clock n) point - next‖ +
          ‖Dilation (clock n) estimate - Dilation (clock n) point‖ := norm_add_le _ _
    _ = ‖P (Dilation (-clock n) next)‖ + ‖estimate - point‖ := by
      change ‖readClock n next - next‖ + _ = _
      rw [actual_clock_error, ← map_sub, (Dilation (clock n)).norm_map]
    _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl estimatedPoint

private theorem quarter_budget {ε scale : ℝ} (positive : 0 < ε) (scaleNonnegative : 0 ≤ scale) :
    scale * (ε / (4 * (1 + scale))) ≤ ε / 4 := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

/-- One finite clock recovers the original current and its literal next at the requested tolerance. -/
theorem actual_finite_clock_current_next (ordinal : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ (n : ℕ) (radius : ℝ) (radiusPositive : 0 < radius) (W N : ℕ),
      (‖finiteClockPair observation nontrivial half n radius radiusPositive W N
          (sourceMap A outsideRead (source ordinal)) - source ordinal‖ ≤ ε) ∧
      (‖finiteClockPair observation nontrivial half n radius radiusPositive W N
          (sourceMap A outsideRead (source (ordinal+1))) - source (ordinal+1)‖ ≤ ε) := by
  let timeScale (i : ℕ) := ‖O‖ * ‖generatorWrite c (clockPredecessor observation nontrivial half depth i)‖
  let freqScale (i : ℕ) := 8 * ‖O‖ * ‖T (source i)‖
  let timeBudget := max (timeScale ordinal) (timeScale (ordinal+1))
  let freqBudget := max (freqScale ordinal) (freqScale (ordinal+1))
  let radius := ε / (4 * (1 + timeBudget))
  let frequency := ε / (4 * (1 + freqBudget))
  have timeNonnegative : 0 ≤ timeBudget :=
    (show 0 ≤ timeScale ordinal by dsimp only [timeScale]; positivity).trans (le_max_left _ _)
  have freqNonnegative : 0 ≤ freqBudget :=
    (show 0 ≤ freqScale ordinal by dsimp only [freqScale]; positivity).trans (le_max_left _ _)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have frequencyPositive : 0 < frequency := by dsimp only [frequency]; positivity
  let spatial (i n : ℕ) := ‖P (Dilation (-clock n) (T (source i)))‖
  have vanishes (i : ℕ) : Tendsto (spatial i) atTop (𝓝 0) := by
    simpa only [actual_clock_error, spatial] using
      (tendsto_iff_norm_sub_tendsto_zero.mp (actual_clock_recovers (T (source i))))
  have small (i : ℕ) : ∀ᶠ n in atTop, spatial i n < ε / 2 :=
    (vanishes i).eventually (Iio_mem_nhds (half_pos positive))
  obtain ⟨n, current, next⟩ := ((small ordinal).and (small (ordinal+1))).exists
  obtain ⟨W,N,paid⟩ := actual_finite_clock_error observation nontrivial half depth n radius
    radiusPositive frequency frequencyPositive
  have error (i : ℕ) (space : spatial i n < ε/2)
      (time : timeScale i ≤ timeBudget) (freq : freqScale i ≤ freqBudget) :
      ‖finiteClockPair observation nontrivial half n radius radiusPositive W N
        (sourceMap A outsideRead (source i)) - source i‖ ≤ ε := by
    refine (paid i).trans ?_
    change spatial i n + timeScale i * radius + freqScale i * frequency ≤ ε
    have timeBound := (mul_le_mul_of_nonneg_right time radiusPositive.le).trans
      (quarter_budget positive timeNonnegative)
    have freqBound := (mul_le_mul_of_nonneg_right freq frequencyPositive.le).trans
      (quarter_budget positive freqNonnegative)
    linarith
  exact ⟨n, radius, radiusPositive, W, N,
    error ordinal current (le_max_left _ _) (le_max_left _ _),
    error (ordinal+1) next (le_max_right _ _) (le_max_right _ _)⟩

end OriginalKCofinalFullBranchFibre.OutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

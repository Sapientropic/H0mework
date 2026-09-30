import H0mework.NavierStokes.Restart.VelocityWeakEndpoint
import H0mework.NavierStokes.GeneratedPaths.StrongSpaceTimeCompactness
import H0mework.NavierStokes.Energy.StrongContinuationDifferenceKineticEnergy
import Mathlib.Topology.Ultrafilter

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeResolventCompactness

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy

noncomputable section

abbrev State := WholeRestartVelocityEndpointState
abbrev Wave := NonzeroIntegerWavevector

def curlDensity (value : State) (wave : Wave) : ℝ := integerWaveViscousMultiplier wave.1 * ‖value wave‖ ^ 2

def CurlBudget (value : State) (cap : ℝ) : Prop :=
  ∀ observed : Finset Wave, (∑ wave ∈ observed, curlDensity value wave) ≤ cap

def observed (radius : ℕ) : Finset Wave := (lowFrequencyCube radius).subtype (fun wave => wave ≠ 0)

def truncate (frequencies : Finset Wave) (value : State) : State :=
  ∑ wave ∈ frequencies, lp.single 2 wave (value wave)

theorem truncate_apply (frequencies : Finset Wave) (value : State) (wave : Wave) :
    truncate frequencies value wave = if wave ∈ frequencies then value wave else 0 := by
  classical
  rw [truncate, lp.coeFn_sum]
  simp [Finset.sum_apply, lp.single_apply]

theorem norm_sq_sum (value : State) : ‖value‖ ^ 2 = ∑' wave, ‖value wave‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) value

theorem budget_summable (value : State) (cap : ℝ) (paid : CurlBudget value cap) :
    Summable (curlDensity value) ∧ (∑' wave, curlDensity value wave) ≤ cap := by
  have positive (wave : Wave) : 0 ≤ curlDensity value wave :=
    mul_nonneg (integerWaveViscousMultiplier_pos wave).le (sq_nonneg _)
  exact ⟨summable_of_sum_le positive paid, Real.tsum_le_of_sum_le positive paid⟩

theorem tail_scaled (value : State) (cap : ℝ) (paid : CurlBudget value cap) (radius : ℕ) :
    (2 * Real.pi) ^ 2 * (radius : ℝ) ^ 2 * ‖value - truncate (observed radius) value‖ ^ 2 ≤ cap := by
  have row (wave : Wave) : (2 * Real.pi) ^ 2 * (radius : ℝ) ^ 2 *
      ‖(value - truncate (observed radius) value) wave‖ ^ 2 ≤ curlDensity value wave := by
    change _ * ‖value wave - truncate (observed radius) value wave‖ ^ 2 ≤ _
    rw [truncate_apply]
    by_cases inside : wave ∈ observed radius
    · rw [if_pos inside, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact mul_nonneg (integerWaveViscousMultiplier_pos wave).le (sq_nonneg _)
    · rw [if_neg inside, sub_zero]
      have outside : wave.1 ∉ lowFrequencyCube radius := by simpa only [observed, Finset.mem_subtype] using inside
      have floor := (lowFrequencyCube_outside_normSq_gt radius wave.1 outside).le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left floor (sq_nonneg (2 * Real.pi))) (sq_nonneg _)
  have finite (frequencies : Finset Wave) :
      (∑ wave ∈ frequencies, (2 * Real.pi) ^ 2 * (radius : ℝ) ^ 2 *
        ‖(value - truncate (observed radius) value) wave‖ ^ 2) ≤ cap :=
    (Finset.sum_le_sum (fun wave _ => row wave)).trans (paid frequencies)
  have bound := Real.tsum_le_of_sum_le (fun wave => mul_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) finite
  simpa only [tsum_mul_left, ← norm_sq_sum] using bound

theorem exists_uniform_tail (cap : ℝ) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ radius : ℕ, ∀ value : State, CurlBudget value cap →
      ‖value - truncate (observed radius) value‖ < epsilon := by
  obtain ⟨radius, large⟩ := exists_nat_gt (Real.sqrt (max cap 0 + 1) / (2 * Real.pi * epsilon))
  refine ⟨radius, fun value paid => ?_⟩
  have denominator : 0 < 2 * Real.pi * epsilon := by positivity
  have large' := (div_lt_iff₀ denominator).mp large
  have square := (sq_lt_sq₀ (Real.sqrt_nonneg _) (le_of_lt ((Real.sqrt_nonneg _).trans_lt large'))).2 large'
  rw [Real.sq_sqrt (by positivity)] at square
  have scaled := tail_scaled value cap paid radius
  by_contra failure
  have lower : epsilon ^ 2 ≤ ‖value - truncate (observed radius) value‖ ^ 2 :=
    pow_le_pow_left₀ positive.le (le_of_not_gt failure) 2
  have contradiction := mul_le_mul_of_nonneg_left lower (mul_nonneg (sq_nonneg (2 * Real.pi)) (sq_nonneg (radius : ℝ)))
  have identity : (radius : ℝ) ^ 2 * (2 * Real.pi * epsilon) ^ 2 =
      (2 * Real.pi) ^ 2 * (radius : ℝ) ^ 2 * epsilon ^ 2 := by ring
  rw [mul_pow, identity] at square
  linarith [le_max_left cap 0]

theorem strong_of_rows (family : ℕ → State) (target : State) (f : Filter ℕ) (cap : ℝ)
    (paid : ∀ index, CurlBudget (family index) cap) (targetPaid : CurlBudget target cap)
    (rows : ∀ wave, Tendsto (fun index => family index wave) f (𝓝 (target wave))) :
    Tendsto family f (𝓝 target) := by
  rw [Metric.tendsto_nhds]
  intro epsilon positive
  obtain ⟨radius, tail⟩ := exists_uniform_tail cap (epsilon / 3) (by positivity)
  have finite : Tendsto (fun index => truncate (observed radius) (family index)) f
      (𝓝 (truncate (observed radius) target)) := by
    apply tendsto_finsetSum
    intro wave _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.tendsto _ |>.comp (rows wave)
  have near := Metric.tendsto_nhds.mp finite (epsilon / 3) (by positivity)
  filter_upwards [near] with index middle
  have first := tail (family index) (paid index)
  have last := tail target targetPaid
  rw [dist_eq_norm] at middle ⊢
  have triangle : ‖family index - target‖ ≤ ‖family index - truncate (observed radius) (family index)‖ +
      ‖truncate (observed radius) (family index) - truncate (observed radius) target‖ +
      ‖target - truncate (observed radius) target‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      (dist_triangle4 (family index) (truncate (observed radius) (family index)) (truncate (observed radius) target) target)
  linarith

theorem exists_strong_limit (family : ℕ → State) (f : Ultrafilter ℕ) (kinetic cap : ℝ)
    (bounded : ∀ index, ‖family index‖ ≤ kinetic) (paid : ∀ index, CurlBudget (family index) cap) :
    ∃ target : State, Tendsto family (f : Filter ℕ) (𝓝 target) ∧ ‖target‖ ≤ kinetic ∧ CurlBudget target cap := by
  let box : Set (Wave → ComplexCoordinateEuclidean) := pi univ (fun _ => Metric.closedBall 0 kinetic)
  have compact : IsCompact box := isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  let values (index : ℕ) (wave : Wave) := family index wave
  have included : ∀ index, values index ∈ box := by
    intro index wave _
    simpa only [Metric.mem_closedBall, dist_zero_right, values] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (family index) wave).trans (bounded index)
  have visited : box ∈ Ultrafilter.map values f := by
    change values ⁻¹' box ∈ (f : Filter ℕ)
    exact Eventually.of_forall included
  obtain ⟨result, _, tends⟩ := compact.ultrafilter_le_nhds' (Ultrafilter.map values f) visited
  have rowLimit : Tendsto values (f : Filter ℕ) (𝓝 result) := by
    change Filter.map values (f : Filter ℕ) ≤ 𝓝 result
    simpa only [Ultrafilter.coe_map] using tends
  have rangeBound : Bornology.IsBounded (range family) := isBounded_iff_forall_norm_le.mpr
    ⟨kinetic, by rintro _ ⟨index, rfl⟩; exact bounded index⟩
  let target : State := ⟨result, lp.memℓp_of_tendsto rangeBound rowLimit⟩
  have rows (wave : Wave) : Tendsto (fun index => family index wave) (f : Filter ℕ) (𝓝 (target wave)) :=
    tendsto_pi_nhds.mp rowLimit wave
  have targetPaid : CurlBudget target cap := by
    intro frequencies
    have convergence := tendsto_finsetSum frequencies (fun wave _ => ((rows wave).norm.pow 2).const_mul (integerWaveViscousMultiplier wave.1))
    exact le_of_tendsto convergence (Eventually.of_forall (fun index => paid index frequencies))
  exact ⟨target, strong_of_rows family target (f : Filter ℕ) cap paid targetPaid rows,
    lp.norm_le_of_tendsto (Eventually.of_forall bounded) rowLimit, targetPaid⟩

theorem norm_from_curl (value : State) (cap : ℝ) (paid : CurlBudget value cap) :
    ‖value‖ ≤ Real.sqrt (cap / (2 * Real.pi) ^ 2) := by
  have row (wave : Wave) : (2 * Real.pi) ^ 2 * ‖value wave‖ ^ 2 ≤ curlDensity value wave := by
    have floor : (2 * Real.pi) ^ 2 ≤ integerWaveViscousMultiplier wave.1 := by
      simpa only [mul_one, integerWaveViscousMultiplier] using
        mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq wave) (sq_nonneg (2 * Real.pi))
    exact mul_le_mul_of_nonneg_right floor (sq_nonneg _)
  have bounded := Real.tsum_le_of_sum_le (fun wave => mul_nonneg (sq_nonneg (2 * Real.pi)) (sq_nonneg ‖value wave‖))
    (fun frequencies => (Finset.sum_le_sum (fun wave _ => row wave)).trans (paid frequencies))
  rw [tsum_mul_left, ← norm_sq_sum] at bounded
  apply Real.le_sqrt_of_sq_le
  exact (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ 2)).mpr (by simpa only [mul_comm] using bounded)

theorem exists_strong_limit_of_curl (family : ℕ → State) (f : Ultrafilter ℕ) (cap : ℝ)
    (paid : ∀ index, CurlBudget (family index) cap) :
    ∃ target : State, Tendsto family (f : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤ cap := by
  obtain ⟨target, strong, _, targetPaid⟩ := exists_strong_limit family f
    (Real.sqrt (cap / (2 * Real.pi) ^ 2)) cap (fun index => norm_from_curl _ cap (paid index)) paid
  exact ⟨target, strong, budget_summable target cap targetPaid⟩

theorem exists_strong_limit_of_sum (family : ℕ → State) (f : Ultrafilter ℕ) (cap : ℝ)
    (summable : ∀ index, Summable (curlDensity (family index)))
    (bounded : ∀ index, (∑' wave, curlDensity (family index) wave) ≤ cap) :
    ∃ target : State, Tendsto family (f : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤ cap := by
  apply exists_strong_limit_of_curl family f cap
  intro index frequencies
  exact ((summable index).sum_le_tsum frequencies (fun wave _ =>
    mul_nonneg (integerWaveViscousMultiplier_pos wave).le (sq_nonneg _))).trans (bounded index)

end
end SaturationMonoid.NavierStokes.NativeResolventCompactness

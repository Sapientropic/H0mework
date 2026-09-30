import H0mework.Versions.X.NavierStokes.WindowPhysics.SpacetimeFourier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowLocalFourier

open Set Filter MeasureTheory Function
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier

noncomputable section

private theorem compact_derivative_bound {point : Spacetime} (bump : ContDiffBump point) (n : ℕ) :
    ∃ cap : ℝ, 0 ≤ cap ∧ ∀ x, ‖iteratedFDeriv ℝ n bump x‖ ≤ cap := by
  have continuous := (bump.contDiff : ContDiff ℝ ∞ bump).continuous_iteratedFDeriv
    (m := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  obtain ⟨cap, bounded⟩ := (bump.hasCompactSupport.image continuous.norm).bddAbove
  refine ⟨max cap 0, le_max_right _ _, fun x => ?_⟩
  by_cases inside : x ∈ tsupport bump
  · exact (bounded ⟨x, inside, rfl⟩).trans (le_max_left _ _)
  · have zero : iteratedFDeriv ℝ n bump x = 0 := by
      by_contra nonzero
      exact inside (support_iteratedFDeriv_subset n nonzero)
    rw [zero, norm_zero]
    exact le_max_right _ _

private theorem scalarMode_bound_at (coefficient : ℕ → IntegerWavevector → ℝ → ℂ)
    (evolves : ∀ n wave time, HasDerivAt (coefficient n wave) (coefficient (n + 1) wave time) time)
    (bound : ℕ → ℕ → ℝ) (pair : Spacetime)
    (bounded : ∀ rank order wave, frequencySize wave ^ order * ‖coefficient rank wave pair.1‖ ≤
      bound rank order * decay wave) (order : ℕ) (wave : IntegerWavevector) :
    ‖iteratedFDeriv ℝ order (scalarMode coefficient wave) pair‖ ≤ modeBudget bound order * decay wave := by
  apply (norm_iteratedFDeriv_mul_le (timeCoefficient_smooth coefficient evolves wave)
    (spaceMonomial_smooth wave) pair (n := order)
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).trans
  rw [modeBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro rank _
  have timeBound := timeCoefficient_bound coefficient evolves wave rank pair
  have spaceBound := spaceMonomial_bound wave (order - rank) pair
  calc
    _ ≤ (order.choose rank : ℝ) * (2 * Real.pi) ^ (order - rank) *
        (frequencySize wave ^ (order - rank) * ‖coefficient rank wave pair.1‖) := by
      have scaled := mul_le_mul_of_nonneg_left
        (mul_le_mul timeBound spaceBound (norm_nonneg _) (norm_nonneg _)) (Nat.cast_nonneg (order.choose rank))
      convert! scaled using 1
      · ring
      · rw [mul_pow]
        ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bounded rank (order - rank) wave)
        (mul_nonneg (Nat.cast_nonneg (order.choose rank)) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _))

theorem local_scalar_smooth (coefficient : ℕ → IntegerWavevector → ℝ → ℂ)
    (evolves : ∀ n wave time, HasDerivAt (coefficient n wave) (coefficient (n + 1) wave time) time)
    (left : ℝ) (bound : ℝ → ℕ → ℕ → ℝ)
    (nonnegative : ∀ H rank order, 0 ≤ bound H rank order)
    (bounded : ∀ H time, time ∈ Icc left H → ∀ rank order wave,
      frequencySize wave ^ order * ‖coefficient rank wave time‖ ≤ bound H rank order * decay wave)
    (point : Spacetime) (inside : left < point.1) :
    ContDiffAt ℝ ∞ (scalarField coefficient) point := by
  let radius := (point.1 - left) / 2
  have positive : 0 < radius := half_pos (sub_pos.mpr inside)
  let bump : ContDiffBump point := ⟨radius / 2, radius, half_pos positive, half_lt_self positive⟩
  let H := point.1 + radius
  have covered (x : Spacetime) (member : x ∈ tsupport bump) : x.1 ∈ Icc left H := by
    rw [bump.tsupport_eq, Metric.mem_closedBall] at member
    have near : dist x.1 point.1 ≤ radius :=
      (le_max_left (dist x.1 point.1) (dist x.2 point.2)).trans member
    rw [Real.dist_eq, abs_le] at near
    constructor <;> dsimp [H, radius] at * <;> linarith [near.1, near.2]
  choose cap cap_nonnegative cap_bound using compact_derivative_bound bump
  let B (order : ℕ) := ∑ rank ∈ Finset.range (order + 1),
    (order.choose rank : ℝ) * cap rank * modeBudget (bound H) (order - rank)
  have mode_nonnegative (n : ℕ) : 0 ≤ modeBudget (bound H) n := by
    apply Finset.sum_nonneg
    intro rank _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (nonnegative H rank (n - rank))
  have B_nonnegative (n : ℕ) : 0 ≤ B n :=
    Finset.sum_nonneg fun rank _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (cap_nonnegative rank)) (mode_nonnegative _)
  have modes_smooth (wave : IntegerWavevector) :
      ContDiff ℝ ∞ (fun x => bump x • scalarMode coefficient wave x) :=
    bump.contDiff.smul (scalarMode_smooth coefficient evolves wave)
  have modes_bound (order : ℕ) (wave : IntegerWavevector) (x : Spacetime) :
      ‖iteratedFDeriv ℝ order (fun y => bump y • scalarMode coefficient wave y) x‖ ≤
        B order * decay wave := by
    by_cases member : x ∈ tsupport bump
    · apply (norm_iteratedFDeriv_smul_le bump.contDiff (scalarMode_smooth coefficient evolves wave) x
        (n := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).trans
      dsimp only [B]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro rank _
      have mode_bound := scalarMode_bound_at coefficient evolves (bound H) x
        (bounded H x.1 (covered x member)) (order - rank) wave
      have actual := mul_le_mul_of_nonneg_left
        (mul_le_mul (cap_bound rank x) mode_bound (norm_nonneg _) (cap_nonnegative rank))
        (Nat.cast_nonneg (order.choose rank))
      simpa only [mul_assoc] using actual
    · have zero : iteratedFDeriv ℝ order (fun y => bump y • scalarMode coefficient wave y) x = 0 := by
        by_contra nonzero
        exact member (tsupport_smul_subset_left bump (scalarMode coefficient wave)
          (support_iteratedFDeriv_subset order nonzero))
      rw [zero, norm_zero]
      exact mul_nonneg (B_nonnegative order) (sq_nonneg _)
  have smooth := contDiff_tsum (N := (⊤ : ℕ∞)) modes_smooth
    (fun order _ => decay_summable.mul_left (B order))
    (fun order wave x _ => modes_bound order wave x)
  apply smooth.contDiffAt.congr_of_eventuallyEq
  filter_upwards [bump.eventuallyEq_one] with x same
  simp only [same, Pi.one_apply, one_smul]
  rfl

theorem compact_all_order_Lp_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : Spacetime → E) {s : Set Spacetime} (smooth : ContDiffOn ℝ ∞ field s) (openSet : IsOpen s)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain)
    (contained : domain ⊆ s) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  have continuous : ContinuousOn (iteratedFDeriv ℝ order field) domain :=
    (ContinuousOn.continuousOn_iteratedFDeriv smooth openSet
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).mono contained
  obtain ⟨ceiling, ceilingBound⟩ := (compact.image_of_continuousOn continuous.norm).bddAbove
  let bound := max ceiling 0
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have bounded : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order field point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (ceilingBound ⟨point, inside, rfl⟩).trans (le_max_left _ _)
  exact ⟨bound, le_max_right _ _, MemLp.of_bound
    (continuous.aestronglyMeasurable_of_isCompact compact compact.measurableSet) bound bounded,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bounded⟩

end
end SaturationMonoid.NavierStokes.NativeWindowLocalFourier

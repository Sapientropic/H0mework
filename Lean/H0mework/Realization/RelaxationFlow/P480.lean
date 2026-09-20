/-
  Proposition 480: sampled continuous envelope as infinite saturation series.

  P245 defines the continuous exponential envelope

      sigma(t) = 1 - exp(-lambda * t).

  P292 proves that finite sampled residual powers match that continuous
  envelope exactly.  P479 proves that every positive nonabsorbing saturation
  rate has infinite increment sum `1`.

  This file composes those facts.  If a one-step rate is sampled as
  `realDecayRate lambda step` and `0 < lambda * step`, then:

  * the sampled rate lies in `(0,1)`;
  * the actual zero-origin `bumpSatField` orbit after `N` steps is exactly the
    continuous-envelope rate at total sampled time `N * step`;
  * the infinite increment series sums to `1`;
  * the remaining tail after `N` steps is the continuous residual
    `exp(-lambda * (N * step))`.

  Boundary: this is an exact algebraic sampling theorem for the scalar
  saturation carrier.  It does not choose the physical clock, derive `lambda`,
  solve RG equations, or identify the scalar with physical energy.
-/

import H0mework.Realization.Residual.P479
import H0mework.Realization.RelaxationFlow.P292
import H0mework.Physics.YukawaSources.P379

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

open scoped BigOperators

/-! ## Positive sampled rates -/

/-- THEOREM 1: a positive sampled time-scale gives a positive sampled
saturation rate. -/
theorem realDecayRate_pos_of_mul_pos
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    0 < realDecayRate lambda step := by
  unfold realDecayRate realDecayResidual
  have hneg : (-lambda) * step < 0 := by
    nlinarith
  have hexp_lt_one : Real.exp ((-lambda) * step) < 1 := by
    exact Real.exp_lt_one_iff.mpr hneg
  linarith

/-- THEOREM 2: a positive sampled time-scale gives a rate in `(0,1)`. -/
theorem realDecayRate_mem_Ioo_of_mul_pos
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    realDecayRate lambda step ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨realDecayRate_pos_of_mul_pos hpos,
    realDecayRate_lt_one lambda step⟩

/-! ## Sampled finite orbit -/

/-- THEOREM 3: the actual zero-origin saturation orbit for a sampled one-step
rate equals the continuous-envelope rate at total sampled time. -/
theorem bumpSatField_iterate_zero_realDecayRate_eq_total_time
    (lambda step : ℝ) (N : ℕ) :
    (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 =
      realDecayRate lambda ((N : ℝ) * step) := by
  rw [bumpSatField_iterate_zero_eq_one_sub_keep_pow]
  exact effective_rate_of_realDecayRate_pow_eq_realDecayRate_nat_mul
    lambda step N

/-- THEOREM 4: the sampled per-step increment has the continuous residual
closed form. -/
theorem saturationIncrement_realDecayRate_eq_closed
    (lambda step : ℝ) (n : ℕ) :
    saturationIncrement (realDecayRate lambda step) n =
      realDecayRate lambda step *
        realDecayResidual lambda ((n : ℝ) * step) := by
  unfold saturationIncrement
  rw [residual_power_of_realDecayRate_eq_realDecayResidual]

/-! ## Infinite sampled accounting -/

/-- THEOREM 5: a positive sampled one-step rate has infinite increment sum
exactly one. -/
theorem hasSum_saturationIncrement_realDecayRate_one
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    HasSum (saturationIncrement (realDecayRate lambda step)) 1 := by
  exact hasSum_saturationIncrement_one
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)

/-- THEOREM 6: the sampled infinite increment `tsum` is exactly one. -/
theorem tsum_saturationIncrement_realDecayRate_eq_one
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    (∑' n : ℕ, saturationIncrement (realDecayRate lambda step) n) = 1 :=
  (hasSum_saturationIncrement_realDecayRate_one hpos).tsum_eq

/-- THEOREM 7: after `N` sampled steps, the infinite future tail sums to the
continuous residual at total sampled time. -/
theorem hasSum_saturationIncrement_realDecayRate_tail_residual
    {lambda step : ℝ} (hpos : 0 < lambda * step) (N : ℕ) :
    HasSum
      (fun k : ℕ =>
        saturationIncrement (realDecayRate lambda step) (N + k))
      (realDecayResidual lambda ((N : ℝ) * step)) := by
  have htail := hasSum_saturationIncrement_tail_keep_pow
    (sigma := realDecayRate lambda step)
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)
    N
  rw [residual_power_of_realDecayRate_eq_realDecayResidual] at htail
  exact htail

/-- THEOREM 8: the sampled tail `tsum` is the continuous residual at total
sampled time. -/
theorem tsum_saturationIncrement_realDecayRate_tail_eq_residual
    {lambda step : ℝ} (hpos : 0 < lambda * step) (N : ℕ) :
    (∑' k : ℕ,
        saturationIncrement (realDecayRate lambda step) (N + k)) =
      realDecayResidual lambda ((N : ℝ) * step) :=
  (hasSum_saturationIncrement_realDecayRate_tail_residual hpos N).tsum_eq

/-! ## Bundled receipt -/

/-- A compact receipt that the sampled continuous exponential envelope and the
infinite saturation accounting are the same scalar carrier law. -/
structure SampledInfiniteSaturationSeriesReceipt : Prop where
  sampled_rate_mem :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      realDecayRate lambda step ∈ Set.Ioo (0 : ℝ) 1
  orbit_total_time :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 =
        realDecayRate lambda ((N : ℝ) * step)
  increment_closed :
    ∀ lambda step : ℝ, ∀ n : ℕ,
      saturationIncrement (realDecayRate lambda step) n =
        realDecayRate lambda step *
          realDecayResidual lambda ((n : ℝ) * step)
  hasSum_one :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      HasSum (saturationIncrement (realDecayRate lambda step)) 1
  tsum_one :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      (∑' n : ℕ, saturationIncrement (realDecayRate lambda step) n) = 1
  tail_residual :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ,
      HasSum
        (fun k : ℕ =>
          saturationIncrement (realDecayRate lambda step) (N + k))
        (realDecayResidual lambda ((N : ℝ) * step))
  tail_tsum_residual :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ,
      (∑' k : ℕ,
          saturationIncrement (realDecayRate lambda step) (N + k)) =
        realDecayResidual lambda ((N : ℝ) * step)

/-- THEOREM 9: the sampled continuous-envelope / infinite-series receipt. -/
theorem sampledInfiniteSaturationSeriesReceipt :
    SampledInfiniteSaturationSeriesReceipt where
  sampled_rate_mem :=
    fun _ _ hpos => realDecayRate_mem_Ioo_of_mul_pos hpos
  orbit_total_time :=
    bumpSatField_iterate_zero_realDecayRate_eq_total_time
  increment_closed :=
    saturationIncrement_realDecayRate_eq_closed
  hasSum_one :=
    fun _ _ hpos => hasSum_saturationIncrement_realDecayRate_one hpos
  tsum_one :=
    fun _ _ hpos => tsum_saturationIncrement_realDecayRate_eq_one hpos
  tail_residual :=
    fun _ _ hpos N =>
      hasSum_saturationIncrement_realDecayRate_tail_residual hpos N
  tail_tsum_residual :=
    fun _ _ hpos N =>
      tsum_saturationIncrement_realDecayRate_tail_eq_residual hpos N

end

end AffineRelaxation
end SaturationMonoid

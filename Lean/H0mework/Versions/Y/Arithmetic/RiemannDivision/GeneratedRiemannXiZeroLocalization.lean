import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import H0mework.Versions.Y.Arithmetic.SonineSource.ModifiedWeakFEQuarterCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

/-- Entire source normalization of the completed Riemann function. -/
def generatedRiemannXi (owner : GlobalGermOwner) (s : ℂ) : ℂ :=
  s * (1 - s) * generatedCompletedRiemannZeta₀ owner s - 1

theorem differentiable_generatedRiemannXi (owner : GlobalGermOwner) :
    Differentiable ℂ (generatedRiemannXi owner) := by
  unfold generatedRiemannXi
  exact ((differentiable_id.mul
      ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)).mul
        (differentiable_generatedCompletedRiemannZeta₀ owner)).sub
    (differentiable_const (c := (1 : ℂ)))

theorem analytic_generatedRiemannXi (owner : GlobalGermOwner) :
    AnalyticOnNhd ℂ (generatedRiemannXi owner) Set.univ := by
  exact analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_generatedRiemannXi owner)

@[simp] theorem generatedRiemannXi_zero (owner : GlobalGermOwner) :
    generatedRiemannXi owner 0 = -1 := by
  simp [generatedRiemannXi]

theorem generatedRiemannXi_eq_completed
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (coordinateNe : coordinate ≠ 0) (coordinateNeOne : coordinate ≠ 1) :
    generatedRiemannXi owner coordinate =
      coordinate * (1 - coordinate) *
        generatedCompletedRiemannZeta owner coordinate := by
  rw [generatedRiemannXi,
    generatedCompletedRiemannZeta_pole_normal_form]
  have oneSubNe : 1 - coordinate ≠ 0 :=
    sub_ne_zero.mpr coordinateNeOne.symm
  field_simp [coordinateNe, oneSubNe]
  ring

theorem generatedRiemannXi_one_sub
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    generatedRiemannXi owner (1 - coordinate) =
      generatedRiemannXi owner coordinate := by
  by_cases coordinateZero : coordinate = 0
  · subst coordinate
    norm_num [generatedRiemannXi]
  by_cases coordinateOne : coordinate = 1
  · subst coordinate
    norm_num [generatedRiemannXi]
  have complementNeZero : 1 - coordinate ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm coordinateOne)
  have complementNeOne : 1 - coordinate ≠ 1 := by
    intro equality
    apply coordinateZero
    linear_combination -equality
  rw [generatedRiemannXi_eq_completed owner (1 - coordinate)
      complementNeZero complementNeOne,
    generatedRiemannXi_eq_completed owner coordinate
      coordinateZero coordinateOne,
    generatedCompletedRiemannZeta_one_sub]
  ring

theorem generatedRiemannXi_ne_eventually_zero
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    ¬ Filter.Eventually (fun s => generatedRiemannXi owner s = 0)
        (nhds coordinate) := by
  intro localZero
  have globalZero := (analytic_generatedRiemannXi owner)
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ coordinate) localZero
  have atZero := globalZero (Set.mem_univ 0)
  rw [generatedRiemannXi_zero] at atZero
  norm_num at atZero

/-- The source-selected Taylor expansion of `generatedRiemannXi` at one
exact spectral coordinate. -/
def generatedRiemannXiPowerSeries
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (analytic_generatedRiemannXi owner coordinate (Set.mem_univ coordinate)).choose

theorem generatedRiemannXi_hasFPowerSeriesAt
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    HasFPowerSeriesAt (generatedRiemannXi owner)
      (generatedRiemannXiPowerSeries owner coordinate) coordinate :=
  (analytic_generatedRiemannXi owner coordinate
    (Set.mem_univ coordinate)).choose_spec

theorem generatedRiemannXiPowerSeries_ne_zero
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    generatedRiemannXiPowerSeries owner coordinate ≠ 0 := by
  intro seriesZero
  apply generatedRiemannXi_ne_eventually_zero owner coordinate
  exact (generatedRiemannXi_hasFPowerSeriesAt owner coordinate
    ).locally_zero_iff.mpr seriesZero

/-- Analytic multiplicity of the exact spectral event. -/
def generatedRiemannXiZeroOrder
    (owner : GlobalGermOwner) (coordinate : ℂ) : Nat :=
  (generatedRiemannXiPowerSeries owner coordinate).order

/-- The entire factor left after removing the selected zero at its full
analytic multiplicity. -/
def generatedRiemannXiZeroLocalization
    (owner : GlobalGermOwner) (coordinate : ℂ) : ℂ → ℂ :=
  (Function.swap dslope coordinate)^[
    generatedRiemannXiZeroOrder owner coordinate]
      (generatedRiemannXi owner)

theorem generatedRiemannXi_factorization
    (owner : GlobalGermOwner) (coordinate value : ℂ) :
    generatedRiemannXi owner value =
      (value - coordinate) ^ generatedRiemannXiZeroOrder owner coordinate *
        generatedRiemannXiZeroLocalization owner coordinate value := by
  simpa [generatedRiemannXiZeroOrder,
    generatedRiemannXiZeroLocalization, smul_eq_mul] using
    (generatedRiemannXi_hasFPowerSeriesAt owner coordinate
      ).eq_pow_order_mul_iterate_dslope value

theorem generatedRiemannXiZeroLocalization_at_ne_zero
    (owner : GlobalGermOwner) (coordinate : ℂ) :
    generatedRiemannXiZeroLocalization owner coordinate coordinate ≠ 0 := by
  exact (generatedRiemannXi_hasFPowerSeriesAt owner coordinate
    ).iterate_dslope_fslope_ne_zero
      (generatedRiemannXiPowerSeries_ne_zero owner coordinate)

theorem generatedRiemannXi_eq_zero_of_completed_zero
    (owner : GlobalGermOwner) (coordinate : ℂ)
    (coordinateNe : coordinate ≠ 0) (coordinateNeOne : coordinate ≠ 1)
    (completedZero : generatedCompletedRiemannZeta owner coordinate = 0) :
    generatedRiemannXi owner coordinate = 0 := by
  have normalForm := generatedCompletedRiemannZeta_pole_normal_form
    owner coordinate
  rw [completedZero] at normalForm
  have corrected : generatedCompletedRiemannZeta₀ owner coordinate =
      1 / coordinate + 1 / (1 - coordinate) := by
    linear_combination -normalForm
  rw [generatedRiemannXi, corrected]
  have oneSubNe : 1 - coordinate ≠ 0 :=
    sub_ne_zero.mpr coordinateNeOne.symm
  field_simp [coordinateNe, oneSubNe]
  ring

theorem generatedRiemannXi_observation_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedRiemannXi owner observation.coordinate = 0 := by
  apply generatedRiemannXi_eq_zero_of_completed_zero
  · exact observation.coordinate_ne_zero
  · intro coordinateOne
    have below := observation.coordinate_re_lt_one
    rw [coordinateOne] at below
    norm_num at below
  · exact observation.completed_eq_zero_of_nontrivial nontrivial

theorem generatedRiemannXiZeroOrder_pos
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    0 < generatedRiemannXiZeroOrder owner observation.coordinate := by
  by_contra notPositive
  have orderZero :
      generatedRiemannXiZeroOrder owner observation.coordinate = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  have factorization := generatedRiemannXi_factorization owner
    observation.coordinate observation.coordinate
  rw [generatedRiemannXi_observation_zero observation nontrivial,
    orderZero, pow_zero, one_mul] at factorization
  exact (generatedRiemannXiZeroLocalization_at_ne_zero
    owner observation.coordinate) factorization.symm

theorem generatedRiemannXiZeroLocalization_eq_zero_of_other_zero
    (owner : GlobalGermOwner) (coordinate value : ℂ)
    (other : value ≠ coordinate)
    (valueZero : generatedRiemannXi owner value = 0) :
    generatedRiemannXiZeroLocalization owner coordinate value = 0 := by
  have factorization := generatedRiemannXi_factorization
    owner coordinate value
  have productZero :
      (value - coordinate) ^ generatedRiemannXiZeroOrder owner coordinate *
        generatedRiemannXiZeroLocalization owner coordinate value = 0 := by
    rw [← factorization, valueZero]
  exact (mul_eq_zero.mp productZero).resolve_left
    (pow_ne_zero _ (sub_ne_zero.mpr other))

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import Mathlib.Topology.Algebra.Polynomial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank

open BurnolPhysicalState UnitPowerJordanSource OriginalRieszFinitePairing.CoPoisson.Ward
open Filter MeasureTheory Polynomial Set
open scoped Topology

local notation "q" => (1/4 : ℝ)
local notation "μq" => Measure.restrict (volume : Measure ℝ) (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Z" => OriginalRieszSource.Constructor.zeroMean

private theorem counted_sum_read (c : BurnolCompletedMellinCoordinate) (indices : Finset Nat)
    (a : Nat → ℂ) :
    ((∑ k ∈ indices, a k • dividedLogColumn c k : Hq) : ℝ → ℂ) =ᵐ[μq]
      fun x => ∑ k ∈ indices, a k * dividedLogRaw c k x := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μq
  | insert k indices fresh prior =>
    simp only [Finset.sum_insert fresh]
    filter_upwards [Lp.coeFn_add (a k • dividedLogColumn c k)
        (∑ i ∈ indices, a i • dividedLogColumn c i),
      Lp.coeFn_smul (a k) (dividedLogColumn c k), dividedLogColumn_profile c k, prior]
      with x total scaled native tail
    rw [total, Pi.add_apply, scaled, Pi.smul_apply, smul_eq_mul, native, tail]

private theorem positive_read (c : BurnolCompletedMellinCoordinate) (indices : Finset Nat)
    (a : Nat → ℂ) (vanished : ∑ k ∈ indices, a k • centeredLogColumn c k = 0) :
    ∃ mean : ℂ, ∀ x ∈ Ioo (0:ℝ) q,
      (x:ℂ)^(star c.value-1) *
        (∑ k ∈ indices, monomial k (a k / (k.factorial:ℂ))).eval (Real.log (q/x) : ℂ) =
        mean := by
  let sum : Hq := ∑ k ∈ indices, a k • dividedLogColumn c k
  let mean := burnolQuarterMeanCoefficient sum
  let poly : ℂ[X] := ∑ k ∈ indices, monomial k (a k / (k.factorial:ℂ))
  let value (x : ℝ) := (x:ℂ)^(star c.value-1) * poly.eval (Real.log (q/x) : ℂ)
  have centered : Z sum = 0 := by
    simpa only [sum, map_sum, map_smul, centeredLogColumn] using vanished
  have raw := congrArg (fun v : BurnolQuarterMeanZeroCarrier => (v : Hq)) centered
  rw [OriginalRieszSource.Constructor.zeroMean_read, Submodule.coe_zero] at raw
  have constant : sum = mean • intervalConstant q := sub_eq_zero.mp raw
  have narrower : Ioo (0:ℝ) q ⊆ symmetricInterval q := fun _ h =>
    ⟨by linarith [h.1], h.2.le⟩
  have localRead : value =ᵐ[volume.restrict (Ioo (0:ℝ) q)] fun _ => mean := by
    filter_upwards [
      ae_restrict_of_ae_restrict_of_subset narrower (counted_sum_read c indices a),
      ae_restrict_of_ae_restrict_of_subset narrower (Lp.coeFn_smul mean (intervalConstant q)),
      ae_restrict_of_ae_restrict_of_subset narrower (intervalConstant_coeFn q),
      ae_restrict_mem measurableSet_Ioo] with x written scaled unit inside
    change sum x = _ at written
    rw [constant, scaled, Pi.smul_apply, smul_eq_mul, unit, mul_one] at written
    rw [written]
    unfold value poly
    rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_monomial, dividedLogRaw, SingularCounting.powerRaw, abs_of_pos inside.1]
    ring
  have continuous : ContinuousOn value (Ioo (0:ℝ) q) := by
    intro x inside
    have cpow := Complex.continuousAt_ofReal_cpow_const x (star c.value-1) (.inr inside.1.ne')
    have divided : ContinuousAt (fun t : ℝ => q/t) x :=
      continuousAt_const.div continuousAt_id inside.1.ne'
    have logged : ContinuousAt (fun t : ℝ => Real.log (q/t)) x :=
      (Real.continuousAt_log (div_ne_zero (by norm_num : q ≠ 0) inside.1.ne')).comp divided
    have complexLog := Complex.continuous_ofReal.continuousAt.comp logged
    exact (cpow.mul (poly.continuous.continuousAt.comp complexLog)).continuousWithinAt
  exact ⟨mean, Measure.eqOn_Ioo_of_ae_eq (volume : Measure ℝ) localRead continuous continuousOn_const⟩

private theorem polynomial_zero_of_quarter_read (c : BurnolCompletedMellinCoordinate)
    (poly : ℂ[X]) (mean : ℂ)
    (read : ∀ x ∈ Ioo (0:ℝ) q,
      (x:ℂ)^(star c.value-1) * poly.eval (Real.log (q/x) : ℂ) = mean) : poly = 0 := by
  let radius (t : ℝ) := q / Real.exp t
  let exponent := 1-c.value.re
  have exponentPositive : 0 < exponent := sub_pos.mpr c.belowOne
  have radiusLimit : Tendsto radius atTop (𝓝 0) := by
    simpa only [radius, div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop).const_mul q
  have radialLimit : Tendsto (fun t => ‖mean‖ * radius t ^ exponent) atTop (𝓝 0) := by
    have powered := (Real.continuousAt_rpow_const 0 exponent (.inr exponentPositive.le)).tendsto.comp radiusLimit
    simpa only [Real.zero_rpow exponentPositive.ne', mul_zero, Function.comp_def] using powered.const_mul ‖mean‖
  have normRead : (fun t : ℝ => ‖mean‖ * radius t ^ exponent) =ᶠ[atTop]
      (fun t : ℝ => ‖poly.eval (t:ℂ)‖) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t positive
    have rpos : 0 < radius t := div_pos (by norm_num) (Real.exp_pos _)
    have small : radius t < q :=
      (div_lt_iff₀ (Real.exp_pos _)).mpr (lt_mul_of_one_lt_right (by norm_num) (Real.one_lt_exp_iff.mpr positive))
    have logRead : Real.log (q/radius t) = t := by
      have argument : q/radius t = Real.exp t := by unfold radius; field_simp
      rw [argument, Real.log_exp]
    have balance := read (radius t) ⟨rpos,small⟩
    rw [logRead] at balance
    have multiplied := congrArg (fun z : ℂ => z * (radius t:ℂ)^(1-star c.value)) balance
    have power : (radius t:ℂ)^(star c.value-1) * (radius t:ℂ)^(1-star c.value) = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr rpos.ne'),
        show star c.value-1+(1-star c.value)=0 by ring, Complex.cpow_zero]
    have eval : poly.eval (t:ℂ) = mean * (radius t:ℂ)^(1-star c.value) := by
      calc
        _ = ((radius t:ℂ)^(star c.value-1) * (radius t:ℂ)^(1-star c.value)) * poly.eval (t:ℂ) := by
          rw [power, one_mul]
        _ = _ := by rw [mul_right_comm]; exact multiplied
    rw [eval, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos rpos]
    simp [exponent, Complex.sub_re]
  have limit := radialLimit.congr' normRead
  by_cases degree : 0 < poly.degree
  · have grows := poly.tendsto_norm_atTop degree
      (z := fun t : ℝ => (t:ℂ)) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop)
    exact (not_tendsto_atTop_of_tendsto_nhds limit grows).elim
  · have constant := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt degree)
    rw [constant] at limit
    have constantLimit : Tendsto (fun _ : ℝ => ‖poly.coeff 0‖) atTop (𝓝 0) := by
      simpa only [Polynomial.eval_C] using limit
    have zero := norm_eq_zero.mp (tendsto_nhds_unique constantLimit tendsto_const_nhds).symm
    rw [zero, map_zero] at constant
    exact constant

/-- The original centered divided-log columns retain all their independent finite coefficients. -/
theorem centered_log_columns_linearIndependent (c : BurnolCompletedMellinCoordinate) :
    LinearIndependent ℂ (centeredLogColumn c) := by
  classical
  rw [linearIndependent_iff']
  intro indices a vanishes k belongs
  let p : ℂ[X] := ∑ j ∈ indices, monomial j (a j / (j.factorial:ℂ))
  obtain ⟨mean,read⟩ := positive_read c indices a vanishes
  have erased : p = 0 := polynomial_zero_of_quarter_read c p mean read
  have coeff : p.coeff k = a k / (k.factorial:ℂ) := by
    simp [p, Polynomial.coeff_monomial, belongs]
  rw [erased, Polynomial.coeff_zero] at coeff
  exact (div_eq_zero_iff.mp coeff.symm).resolve_right (by exact_mod_cast Nat.factorial_ne_zero k)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

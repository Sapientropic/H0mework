import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open scoped Topology InnerProductSpace ContDiff
open private reciprocal_small sqrt_bound power_times_sqrt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalTail
open private fourier_raw_even_of_fixed from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier

private theorem c1_weight_derivative (raw slope : ℝ → ℂ)
    (derivative : ∀ x : ℝ, 0 < x → x ≤ q → HasDerivAt raw (slope x) x)
    (u : ℝ) (large : 4 ≤ u) :
    HasDerivAt (weight raw) (-((u : ℂ)⁻¹ ^ 2) * (raw u⁻¹ + (u⁻¹ : ℝ) * slope u⁻¹)) u := by
  have positive : 0 < u := by linarith
  have original := Complex.ofRealCLM.hasDerivAt.mul
    (derivative u⁻¹ (inv_pos.mpr positive) (reciprocal_small u large))
  have actual := original.scomp u ((hasDerivAt_id u).inv positive.ne')
  convert! actual using 1
  · funext v
    simp only [weight, Function.comp_apply, Pi.mul_apply, Complex.ofReal_inv,
      Complex.ofRealCLM_apply, div_eq_mul_inv]
    ring
  · simp only [Complex.real_smul, Complex.ofRealCLM_apply, id_eq]
    push_cast
    simp only [div_eq_mul_inv, inv_pow]
    ring

/-- Compact C1 values and slopes generate every analytic input to the original infinite source engine. -/
theorem actual_compact_c1_inputs (state : Hq) (raw slope : ℝ → ℂ)
    (_represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (_even : ∀ x ∈ symmetricInterval q, raw |x| = raw x)
    (measured : Measurable raw)
    (valueContinuous : ContinuousOn raw (Icc (0 : ℝ) q))
    (slopeContinuous : ContinuousOn slope (Icc (0 : ℝ) q))
    (derivative : ∀ x : ℝ, 0 < x → x ≤ q → HasDerivAt raw (slope x) x) :
    (∀ u : ℝ, 4 ≤ u → HasDerivAt (weight raw) (deriv (weight raw) u) u) ∧
      ContinuousOn (deriv (weight raw)) (Ici 4) ∧ Measurable (weight raw) ∧
      IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight raw))) (Ioi 4) ∧
      Tendsto (fun u : ℝ => Real.sqrt u * ‖weight raw u‖) atTop (𝓝 0) := by
  obtain ⟨oldB, valueBound⟩ := isCompact_Icc.exists_bound_of_continuousOn valueContinuous
  obtain ⟨oldD, slopeBound⟩ := isCompact_Icc.exists_bound_of_continuousOn slopeContinuous
  let B := max 0 oldB
  let D := max 0 oldD
  let C := B + q * D
  have Bnonnegative : 0 ≤ B := le_max_left _ _
  have Dnonnegative : 0 ≤ D := le_max_left _ _
  have Cnonnegative : 0 ≤ C := by dsimp only [C]; positivity
  have values (x : ℝ) (inside : x ∈ Icc (0 : ℝ) q) : ‖raw x‖ ≤ B :=
    (valueBound x inside).trans (le_max_right _ _)
  have slopes (x : ℝ) (inside : x ∈ Icc (0 : ℝ) q) : ‖slope x‖ ≤ D :=
    (slopeBound x inside).trans (le_max_right _ _)
  have weighted (x : ℝ) (inside : x ∈ Icc (0 : ℝ) q) : ‖raw x + (x : ℂ) * slope x‖ ≤ C := by
    calc
      _ ≤ ‖raw x‖ + ‖(x : ℂ) * slope x‖ := norm_add_le _ _
      _ ≤ B + q * D := by
        apply add_le_add (values x inside)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg inside.1]
        exact mul_le_mul inside.2 (slopes x inside) (norm_nonneg _) (by norm_num)
      _ = C := rfl
  have weightDerivative (u : ℝ) (large : 4 ≤ u) : HasDerivAt (weight raw) (deriv (weight raw) u) u :=
    (c1_weight_derivative raw slope derivative u large).differentiableAt.hasDerivAt
  have reciprocalContinuous : ContinuousOn (fun u : ℝ => u⁻¹) (Ici 4) := by
    intro u large
    exact (continuousAt_inv₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) large).ne').continuousWithinAt
  have reciprocalInside (u : ℝ) (large : u ∈ Ici (4 : ℝ)) : u⁻¹ ∈ Icc (0 : ℝ) q :=
    ⟨(inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) large)).le, reciprocal_small u large⟩
  have reciprocalComplex := Complex.continuous_ofReal.comp_continuousOn reciprocalContinuous
  have reciprocalValue := valueContinuous.comp reciprocalContinuous reciprocalInside
  have reciprocalSlope := slopeContinuous.comp reciprocalContinuous reciprocalInside
  have explicitContinuous : ContinuousOn
      (fun u : ℝ => -((u : ℂ)⁻¹ ^ 2) * (raw u⁻¹ + (u⁻¹ : ℝ) * slope u⁻¹)) (Ici 4) := by
    have native := (reciprocalComplex.pow 2).neg.mul
      (reciprocalValue.add (reciprocalComplex.mul reciprocalSlope))
    change ContinuousOn (fun u : ℝ => -((u⁻¹ : ℝ) : ℂ) ^ 2 *
      (raw u⁻¹ + ((u⁻¹ : ℝ) : ℂ) * slope u⁻¹)) (Ici 4) at native
    simpa only [Complex.ofReal_inv] using native
  have actualSlopeContinuous : ContinuousOn (deriv (weight raw)) (Ici 4) :=
    explicitContinuous.congr (fun u large => (c1_weight_derivative raw slope derivative u large).deriv)
  have derivativeBound (u : ℝ) (large : 4 ≤ u) : ‖deriv (weight raw) u‖ ≤ C * u⁻¹ ^ 2 := by
    have positive : 0 < u := by linarith
    rw [(c1_weight_derivative raw slope derivative u large).deriv, norm_mul, norm_neg,
      norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    exact (mul_le_mul_of_nonneg_left (weighted u⁻¹ (reciprocalInside u large)) (sq_nonneg _)).trans_eq (by ring)
  have tailBound (u : ℝ) (large : 4 ≤ u) :
      ‖deriv (weight raw) u‖ * (Real.sqrt u + 2) ≤ (3 * C) * u ^ (-(3 / 2 : ℝ)) := by
    have positive : 0 < u := by linarith
    have power : u⁻¹ ^ 2 * Real.sqrt u = u ^ (-(3 / 2 : ℝ)) := by
      have inversePower : u⁻¹ ^ 2 = u ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow]
      rw [inversePower, power_times_sqrt u positive, show (-2 : ℝ) + 1 / 2 = -(3 / 2 : ℝ) by ring]
    calc
      _ ≤ (C * u⁻¹ ^ 2) * (3 * Real.sqrt u) :=
        mul_le_mul (derivativeBound u large) (sqrt_bound u large) (by positivity)
          (mul_nonneg Cnonnegative (sq_nonneg _))
      _ = (3 * C) * (u⁻¹ ^ 2 * Real.sqrt u) := by ring
      _ = _ := by rw [power]
  have domain : IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight raw))) (Ioi 4) := by
    have dominant := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 4)).const_mul (3 * C)
    apply dominant.mono'
      (((measurable_deriv (weight raw)).norm.mul (Real.continuous_sqrt.measurable.add_const 2)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u large
    change ‖‖deriv (weight raw) u‖ * (Real.sqrt u + 2)‖ ≤ _
    rw [Real.norm_of_nonneg (by positivity)]
    exact tailBound u large.le
  have headBound (u : ℝ) (large : 4 ≤ u) :
      Real.sqrt u * ‖weight raw u‖ ≤ B * u ^ (-(1 / 2 : ℝ)) := by
    have positive : 0 < u := by linarith
    have power : u⁻¹ * Real.sqrt u = u ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one u, power_times_sqrt u positive]
      congr 1
      ring
    rw [weight, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    calc
      _ ≤ Real.sqrt u * (B / u) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (values u⁻¹ (reciprocalInside u large)) positive.le) (Real.sqrt_nonneg u)
      _ = B * (u⁻¹ * Real.sqrt u) := by ring
      _ = _ := by rw [power]
  have head : Tendsto (fun u : ℝ => Real.sqrt u * ‖weight raw u‖) atTop (𝓝 0) := by
    have dominant := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul B
    apply squeeze_zero' (Eventually.of_forall (fun u => mul_nonneg (Real.sqrt_nonneg u) (norm_nonneg _)))
      ((eventually_ge_atTop (4 : ℝ)).mono (fun u large => headBound u large))
    simpa only [mul_zero] using dominant
  exact ⟨weightDerivative, actualSlopeContinuous,
    (measured.comp measurable_inv).div (by fun_prop), domain, head⟩

theorem actual_compact_c1_forward (state : Hq) (raw slope : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (even : ∀ x ∈ symmetricInterval q, raw |x| = raw x)
    (measured : Measurable raw)
    (valueContinuous : ContinuousOn raw (Icc (0 : ℝ) q))
    (slopeContinuous : ContinuousOn slope (Icc (0 : ℝ) q))
    (derivative : ∀ x : ℝ, 0 < x → x ≤ q → HasDerivAt raw (slope x) x) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (E state)) atTop
      (𝓝 (InfiniteWeightedProgram.program (deriv (weight raw)) burnolUnitCountingPrimitiveL2)) := by
  obtain ⟨weightDerivative, actualSlopeContinuous, measuredWeight, domain, head⟩ :=
    actual_compact_c1_inputs state raw slope represents even measured valueContinuous slopeContinuous derivative
  exact actual_compact_forward state raw represents even weightDerivative actualSlopeContinuous measuredWeight domain head

/-- The literal original log-B return has a full ambient forward strong graph, with its complete Unit retained. -/
theorem actual_logB_return_forward (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (E (S (logBFirst coordinate 0) : Hq))) atTop
      (𝓝 (InfiniteWeightedProgram.program
        (deriv (weight (burnolMeanZeroFourierRaw (logBFirst coordinate 0)))) burnolUnitCountingPrimitiveL2)) := by
  let raw := burnolMeanZeroFourierRaw (logBFirst coordinate 0)
  have smooth := OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff (logBFirst coordinate 0)
  have fixed : reflectRestricted q (logBFirst coordinate 0 : Hq) = (logBFirst coordinate 0 : Hq) :=
    congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : Hq)) (log_B_even coordinate 0)
  have even (x : ℝ) : raw (-x) = raw x := by
    dsimp only [raw, burnolMeanZeroFourierRaw]
    rw [fourier_raw_even_of_fixed _ fixed x]
  apply actual_compact_c1_forward (S (logBFirst coordinate 0) : Hq) raw (deriv raw)
    (burnolMeanZeroFourier_ae_raw (logBFirst coordinate 0))
    (fun x _ => by
      by_cases positive : 0 ≤ x
      · rw [abs_of_nonneg positive]
      · rw [abs_of_neg (lt_of_not_ge positive), even])
    smooth.continuous.measurable smooth.continuous.continuousOn
    (smooth.continuous_deriv (by norm_num)).continuousOn
  intro x _ _
  exact (smooth.differentiable (by norm_num) x).hasDerivAt

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

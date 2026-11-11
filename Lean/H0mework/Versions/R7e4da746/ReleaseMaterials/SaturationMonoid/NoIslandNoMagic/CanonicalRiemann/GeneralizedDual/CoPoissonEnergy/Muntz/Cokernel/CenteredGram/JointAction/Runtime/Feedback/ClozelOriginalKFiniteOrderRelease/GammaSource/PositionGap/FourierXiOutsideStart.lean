import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalFourierJet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank

open BurnolPhysicalState OriginalCofinalFourierJet UnitPowerJordanSource Filter
open scoped Topology

open private bare_factor bare_analytic bare_nonzero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
open private finiteLogUnit power_quarter_programme from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalFourierJet

local notation "q" => (1/4 : ℝ)
local notation "Cq" => intervalConstant q
local notation "Z" => OriginalRieszSource.Constructor.zeroMean
local notation "R" => burnolDirectRightResolventCLM
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

abbrev xiOrder (c : BurnolCompletedMellinCoordinate) :=
  generatedRiemannXiZeroOrder ActualAnalyticOwner c.value

private def prefactor (s : ℂ) : ℂ :=
  (1-s) * 2 * (((((3/2:ℝ):ℂ)^s)-1)/s) * (q:ℂ)^(s-1)

private theorem arithmetic_unit_factored (s : ℂ) :
    arithmeticUnit s = riemannZeta s * prefactor s := by
  simp only [arithmeticUnit, arithmeticMoment, prefactor, div_eq_mul_inv]
  ring

private theorem coordinate_ne_zero (c : BurnolCompletedMellinCoordinate) : c.value ≠ 0 := by
  intro gone
  have positive := c.rightHalf
  rw [gone, Complex.zero_re] at positive
  norm_num at positive

private theorem coordinate_ne_one (c : BurnolCompletedMellinCoordinate) : 1-c.value ≠ 0 := by
  intro gone
  have same := congrArg Complex.re gone
  simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at same
  linarith [c.belowOne]

private theorem prefactor_analytic (c : BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ prefactor c.value := by
  have scale : AnalyticAt ℂ (fun s : ℂ => ((3/2:ℝ):ℂ)^s) c.value :=
    (differentiable_id.const_cpow (.inl (by norm_num : ((3/2:ℝ):ℂ) ≠ 0))).analyticAt c.value
  have quarter : AnalyticAt ℂ (fun s : ℂ => (q:ℂ)^(s-1)) c.value :=
    ((differentiable_id.sub_const 1).const_cpow (.inl (by norm_num : (q:ℂ) ≠ 0))).analyticAt c.value
  exact (((analyticAt_const.sub analyticAt_id).mul analyticAt_const).mul
    ((scale.sub analyticAt_const).div analyticAt_id (coordinate_ne_zero c))).mul quarter

private theorem scale_power_ne_one (c : BurnolCompletedMellinCoordinate) : ((3/2:ℝ):ℂ)^c.value ≠ 1 := by
  intro erased
  have normRead := congrArg norm erased
  norm_num only [norm_one] at normRead
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3/2)] at normRead
  exact (Real.one_lt_rpow (by norm_num : (1:ℝ)<3/2) (by linarith [c.rightHalf])).ne' normRead

private theorem prefactor_ne_zero (c : BurnolCompletedMellinCoordinate) : prefactor c.value ≠ 0 := by
  unfold prefactor
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (coordinate_ne_one c) (by norm_num))
    (div_ne_zero (sub_ne_zero.mpr (scale_power_ne_one c)) (coordinate_ne_zero c)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

private theorem arithmetic_unit_exact_jets (c : BurnolCompletedMellinCoordinate) :
    (∀ j < xiOrder c, iteratedDeriv j arithmeticUnit c.value = 0) ∧
      iteratedDeriv (xiOrder c) arithmeticUnit c.value ≠ 0 := by
  let leading (s : ℂ) := bare c.value s * prefactor s
  have analyticLeading : AnalyticAt ℂ leading c.value := (bare_analytic c).mul (prefactor_analytic c)
  have germ : arithmeticUnit =ᶠ[𝓝 c.value] fun s => (s-c.value)^(xiOrder c) * leading s := by
    filter_upwards [bare_factor c] with s native
    rw [arithmetic_unit_factored, native]
    exact mul_assoc _ _ _
  have analytic : AnalyticAt ℂ arithmeticUnit c.value :=
    (((analyticAt_id.sub analyticAt_const).pow (xiOrder c)).mul analyticLeading).congr germ.symm
  have exactOrder : analyticOrderAt arithmeticUnit c.value = (xiOrder c : ℕ∞) :=
    analytic.analyticOrderAt_eq_natCast.mpr
      ⟨leading, analyticLeading, mul_ne_zero (bare_nonzero c) (prefactor_ne_zero c),
        by
          filter_upwards [germ] with s read
          simpa only [smul_eq_mul] using read⟩
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero analytic).mp exactOrder

/-- The centered quarter is read directly from the actual original Fourier field. -/
def centeredFourierPower (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    BurnolQuarterMeanZeroCarrier :=
  Z (burnolQuarterRestriction (fourierL2 (((R c)^n) seed)))

private def quarterScale (c : BurnolCompletedMellinCoordinate) : ℂ :=
  2*(q:ℂ)^(1-c.value)/(1-c.value)

/-- The scalar of the first original centered log column, at the exact Xi boundary. -/
def firstOutsidePrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -(((2:ℂ)^(xiOrder c)/((xiOrder c).factorial:ℂ)) *
    iteratedDeriv (xiOrder c) arithmeticUnit c.value * quarterScale c)

theorem first_outside_price_ne_zero (c : BurnolCompletedMellinCoordinate) : firstOutsidePrice c ≠ 0 := by
  have scale : quarterScale c ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))) (coordinate_ne_one c)
  have jet := (arithmetic_unit_exact_jets c).2
  exact neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero (xiOrder c))) jet) scale)

/-- The original Fourier programme generates its first centered column immediately after the Xi order. -/
theorem actual_fourier_outside_start (c : BurnolCompletedMellinCoordinate) :
    centeredFourierPower c (xiOrder c+1) = firstOutsidePrice c • centeredLogColumn (barC c) 0 := by
  let m := xiOrder c
  have low := (arithmetic_unit_exact_jets c).1
  have unit : finiteLogUnit c 1 =
      (2/(1-c.value)) • Cq - quarterScale c • dividedLogColumn (barC c) 0 := by
    simp [finiteLogUnit, quarterScale]
  have collapse :
      (∑ k ∈ Finset.range (m+1), m.choose k •
        (iteratedDeriv k arithmeticUnit c.value • (((m-k).factorial:ℂ)/(2:ℂ)^(m-k)) •
          finiteLogUnit c (m-k+1))) =
        iteratedDeriv m arithmeticUnit c.value • finiteLogUnit c 1 := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro k within apart
      have earlier : k < m := by have := Finset.mem_range.mp within; omega
      simp [low k earlier]
    · intro missing
      exact False.elim (missing (Finset.mem_range.mpr (Nat.lt_succ_self m)))
  change Z (burnolQuarterRestriction (fourierL2 (((R c)^(m+1)) seed))) = _
  rw [power_quarter_programme, finiteQuarterJet, collapse, unit]
  simp only [map_smul, map_add, map_sub, OriginalRieszSource.Constructor.zeroMean_constant,
    smul_zero, zero_add, zero_sub]
  change _ = firstOutsidePrice c • Z (dividedLogColumn (barC c) 0)
  unfold firstOutsidePrice
  change _ = -(((2:ℂ)^m/(m.factorial:ℂ)) * iteratedDeriv m arithmeticUnit c.value * quarterScale c) • _
  module

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

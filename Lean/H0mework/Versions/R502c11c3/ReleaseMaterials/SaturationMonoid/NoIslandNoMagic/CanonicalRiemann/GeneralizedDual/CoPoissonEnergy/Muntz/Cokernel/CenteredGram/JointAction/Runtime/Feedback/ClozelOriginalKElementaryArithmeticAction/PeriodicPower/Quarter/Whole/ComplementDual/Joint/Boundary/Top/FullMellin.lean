import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.OutgoingMellin
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.PlainLog

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FullMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.CountingMellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.OutgoingMellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.MellinRead
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.PlainLog OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementDivisionJet
local notation "q" => (1 / 4 : ℝ)
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def probeRadius (c : BurnolCompletedMellinCoordinate) : ℝ := (c.value.re - 1 / 2) / 2
def probeStep (c : BurnolCompletedMellinCoordinate) (n : ℕ) : ℝ := probeRadius c / (n + 1)

private theorem radius_positive (c : BurnolCompletedMellinCoordinate) : 0 < probeRadius c := by
  dsimp only [probeRadius]
  linarith [c.rightHalf]

private theorem step_positive (c : BurnolCompletedMellinCoordinate) (n : ℕ) : 0 < probeStep c n := by
  unfold probeStep
  exact div_pos (radius_positive c) (by positivity)

private theorem step_bounded (c : BurnolCompletedMellinCoordinate) (n : ℕ) : probeStep c n ≤ probeRadius c := by
  apply (div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mpr
  nlinarith [mul_nonneg (radius_positive c).le (Nat.cast_nonneg (α := ℝ) n)]

def probeCoordinate (c : BurnolCompletedMellinCoordinate) (n : ℕ) : BurnolCompletedMellinCoordinate where
  value := c.value - (probeStep c n : ℂ)
  rightHalf := by
    simp only [sub_re, ofReal_re]
    have bound := step_bounded c n
    dsimp only [probeRadius] at bound
    linarith [c.rightHalf]
  belowOne := by
    simp only [sub_re, ofReal_re]
    linarith [step_positive c n, c.belowOne]

private theorem coordinate_below (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    (probeCoordinate c n).value.re < c.value.re := by
  change c.value.re - probeStep c n < c.value.re
  linarith [step_positive c n]

private theorem step_tendsto (c : BurnolCompletedMellinCoordinate) : Tendsto (probeStep c) atTop (𝓝 0) := by
  unfold probeStep
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat (probeRadius c)).comp (tendsto_add_atTop_nat 1)

private theorem coordinate_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : ℕ => (probeCoordinate c n).value) atTop (𝓝 c.value) := by
  have source := (tendsto_const_nhds (x := c.value)).sub (Complex.continuous_ofReal.tendsto 0 |>.comp (step_tendsto c))
  simpa only [Function.comp_def, ofReal_zero, sub_zero, probeCoordinate] using source

private theorem moment_tendsto (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (left : MellinConvergent (v : ℝ → ℂ) (1 - c.value))
    (right : MellinConvergent (v : ℝ → ℂ) (1 - (probeCoordinate c 0).value)) :
    Tendsto (fun n : ℕ => mellin (v : ℝ → ℂ) (1 - (probeCoordinate c n).value)) atTop
      (𝓝 (mellin (v : ℝ → ℂ) (1 - c.value))) := by
  have endpoint : 1 - (probeCoordinate c 0).value = (1 - c.value) + (probeRadius c : ℂ) := by
    simp only [probeCoordinate, probeStep, Nat.cast_zero, zero_add, div_one]
    ring
  rw [endpoint] at right
  have continuous := actual_mellin_right_continuity v (1 - c.value) (probeRadius c) left right
  have within : Tendsto (probeStep c) atTop (𝓝[Icc 0 (probeRadius c)] 0) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨step_tendsto c,
      Eventually.of_forall (fun n => ⟨(step_positive c n).le, step_bounded c n⟩)⟩
  have actual := continuous.tendsto.comp within
  have value (n : ℕ) : 1 - (probeCoordinate c n).value = (1 - c.value) + (probeStep c n : ℂ) := by
    change 1 - (c.value - (probeStep c n : ℂ)) = _
    ring
  simpa only [Function.comp_def, ofReal_zero, add_zero, ← value] using actual

private theorem physical_read_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : ℕ => burnolAmbientCompletedMellinEvaluator (probeCoordinate c n) (physicalCotest c : BurnolL2))
      atTop (𝓝 (burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2))) := by
  have source := moment_tendsto c (physicalCotest c : BurnolL2)
    (actual_physical_cotest_mellin c c).1 (actual_physical_cotest_mellin c (probeCoordinate c 0)).1
  have actual := source.congr' (Eventually.of_forall (fun n => (actual_physical_cotest_mellin c (probeCoordinate c n)).2))
  rw [(actual_physical_cotest_mellin c c).2] at actual
  exact actual

private theorem bare_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : ℕ => bare c.value (probeCoordinate c n).value) atTop (𝓝 (bare c.value c.value)) := by
  have regular := divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum
    ActualAnalyticOwner c.value c.value (by linarith [c.rightHalf]) c.belowOne
  exact regular.continuousAt.tendsto.comp (coordinate_tendsto c)

private theorem actual_probe_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (j n : ℕ) (before : j ≤ order c.value) :
    mellin (nativeOutgoingCotest c j : ℝ → ℂ) (1 - (probeCoordinate c n).value) =
      (2 : ℂ)^j * ((probeCoordinate c n).value - c.value)^(order c.value - j) *
        bare c.value (probeCoordinate c n).value *
          burnolAmbientCompletedMellinEvaluator (probeCoordinate c n) (physicalCotest c : BurnolL2) := by
  let d := probeCoordinate c n
  have source := (actual_native_outgoing_mellin c d zero j (coordinate_below c n)).2
  have notZero : d.value ≠ 0 := ne_of_apply_ne re (by
    simpa only [zero_re] using (show 0 < d.value.re by linarith [d.rightHalf]).ne')
  have notOne : d.value ≠ 1 := by intro same; simpa [same] using d.belowOne
  have zeta := generatedRiemannZeta_zero_factorization ActualAnalyticOwner c.value d.value notZero notOne
    (Gammaℝ_ne_zero_of_re_pos (by linarith [d.rightHalf]))
  rw [generatedRiemannZeta_eq_mathlib] at zeta
  have apart : d.value - c.value ≠ 0 := by
    intro same
    have realPart := congrArg Complex.re same
    simp only [sub_re, zero_re] at realPart
    linarith [coordinate_below c n]
  have powers : (d.value - c.value)^(order c.value) =
      (d.value - c.value)^j * (d.value - c.value)^(order c.value - j) := by
    rw [← pow_add, Nat.add_sub_of_le before]
  rw [source, zeta, powers, div_pow]
  field_simp [apart]
  rfl

/-- A genuine source quarter pays the Mellin limit at the original Xi order, retaining its first nonzero top. -/
theorem actual_native_moment_at_order (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (j : ℕ) (before : j ≤ order c.value) (coefficient : ℂ)
    (quarter : Constructor.zeroMean (burnolQuarterRestriction (nativeOutgoingCotest c j)) =
      coefficient • CenteredCountingDual.logarithm) :
    burnolAmbientCompletedMellinEvaluator c (nativeOutgoingCotest c j) -
      coefficient * (c.value * (q : ℂ)^(1 - c.value) / (1 - c.value)^2) =
        (2 : ℂ)^j * (0 : ℂ)^(order c.value - j) * bare c.value c.value *
          burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2) := by
  have honest := actual_log_quarter_mellin c (nativeOutgoingCotest c j) coefficient quarter
  have left := moment_tendsto c (nativeOutgoingCotest c j) honest.1
    (actual_native_outgoing_mellin c (probeCoordinate c 0) zero j (coordinate_below c 0)).1
  rw [honest.2] at left
  have difference := (coordinate_tendsto c).sub_const c.value
  simp only [sub_self] at difference
  have right := (((tendsto_const_nhds (x := (2 : ℂ)^j)).mul (difference.pow (order c.value - j))).mul
    (bare_tendsto c)).mul (physical_read_tendsto c)
  exact tendsto_nhds_unique (left.congr' (Eventually.of_forall (fun n => actual_probe_price c zero j n before))) right

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FullMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

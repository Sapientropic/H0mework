import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FullMellin
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteBill

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.Current
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.FullMellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.MellinRead
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TopUnit
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteSchur OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.PlainLog
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FiniteBill OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private gap_coefficient_mean from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.ForcingPrice
local notation "q" => (1 / 4 : ℝ)
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "ell" => CenteredCountingDual.logarithm
local notation "h₀" => Real.log stageZeroSonineQ

private theorem amplitude_read (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    nativeActedAmplitude c j = -2 * burnolAmbientCompletedMellinEvaluator c (nativeOutgoingCotest c j) := by
  simp only [nativeActedAmplitude, burnolAmbientCompletedMellinEvaluator,
    burnolRadiusAmbientCompletedMellinEvaluator, add_apply, smul_apply, smul_eq_mul,
    burnolRadiusMellinGapMoment, sourceTail, OriginalPrimitiveRankBalance.conjugateCoordinate,
    star_star, nativeActedQuarter, burnolUnscaledCommonGapRadius, gap_coefficient_mean]
  ring

private theorem amplitude_low_of_quarter (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (j : ℕ) (before : j < order c.value)
    (quarter : nativeActedSchur c j = plainCoefficient c j • ell) :
    nativeActedAmplitude c j + plainContact c * plainCoefficient c j = 0 := by
  have source := actual_native_moment_at_order c zero j before.le (plainCoefficient c j) quarter
  have positive : order c.value - j ≠ 0 := Nat.sub_ne_zero_of_lt before
  rw [zero_pow positive, mul_zero, zero_mul, zero_mul] at source
  rw [amplitude_read]
  unfold plainContact
  linear_combination -2 * source

/-- The original low Xi relations actually clear every fractional column before the true m-th top is read. -/
theorem actual_native_plain_through_order (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (j : ℕ) (before : j ≤ order c.value) :
    nativeActedSchur c j = plainCoefficient c j • ell := by
  revert before
  induction j with
  | zero =>
    intro _
    rw [actual_native_initial_log c zero]
    simp only [plainCoefficient, pow_zero, one_mul]
    rfl
  | succ j previous =>
    intro before
    have quarter := previous (by omega)
    have amplitude := amplitude_low_of_quarter c zero j (by omega) quarter
    have generated := actual_native_acted_schur_step c zero j
    rw [quarter, map_smul, actual_plain_log_step] at generated
    have coefficient : plainCoefficient c (j + 1) = (2 / (1 - c.value)) * plainCoefficient c j := by
      unfold plainCoefficient
      rw [pow_succ]
      ring
    rw [coefficient]
    have paid := congrArg (fun scalar : ℂ => scalar • SingularCounting.centeredPower (barC c)) amplitude
    rw [add_smul, zero_smul] at paid
    unfold plainContact at paid
    linear_combination (norm := module) generated + paid

theorem actual_native_low_amplitude (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (j : ℕ) (before : j < order c.value) :
    nativeActedAmplitude c j + plainContact c * plainCoefficient c j = 0 :=
  amplitude_low_of_quarter c zero j before (actual_native_plain_through_order c zero j before.le)

/-- At m the same source keeps the first actual Xi residue, rather than reusing a lower zero read. -/
theorem actual_native_top_amplitude (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    nativeActedAmplitude c (order c.value) + plainContact c * plainCoefficient c (order c.value) =
      -2 * ((2 : ℂ)^(order c.value) * bare c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) := by
  have source := actual_native_moment_at_order c zero (order c.value) le_rfl
    (plainCoefficient c (order c.value)) (actual_native_plain_through_order c zero (order c.value) le_rfl)
  simp only [Nat.sub_self, pow_zero, mul_one] at source
  rw [amplitude_read]
  unfold plainContact
  linear_combination -2 * source

theorem actual_native_top_hasMellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    HasMellin (nativeOutgoingCotest c (order c.value) : ℝ → ℂ) (1 - c.value)
      ((2 : ℂ)^(order c.value) * bare c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) := by
  have quarter := actual_native_plain_through_order c zero (order c.value) le_rfl
  have source := actual_log_quarter_mellin c (nativeOutgoingCotest c (order c.value))
    (plainCoefficient c (order c.value)) quarter
  have price := actual_native_moment_at_order c zero (order c.value) le_rfl
    (plainCoefficient c (order c.value)) quarter
  simp only [Nat.sub_self, pow_zero, mul_one] at price
  rw [price] at source
  exact source

/-- Every finite current coefficient is cleared by its own earlier original Xi relation. -/
theorem actual_native_coefficient_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (j : ℕ) (before : j ≤ order c.value) (k : ℕ) : nativeCoefficient c j k = 0 := by
  revert before k
  induction j with
  | zero => intro _ k; rfl
  | succ j previous =>
    intro before k
    cases k with
    | zero =>
      rw [nativeCoefficient]
      have sum : (∑ k ∈ Finset.range j, (2 * meanContact (barC c) k) * nativeCoefficient c j k) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [previous (by omega) k, mul_zero]
      rw [sum, add_zero]
      linear_combination actual_native_low_amplitude c zero j (by omega)
    | succ k => rw [nativeCoefficient, previous (by omega) k, mul_zero]

/-- The actual installed finite bill consumes the full top residue and all generated lower-column cancellations. -/
theorem actual_original_top_bill (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    finiteNativeBill c (order c.value) =
      -(2 : ℂ)^(order c.value) * star (bare c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) := by
  unfold finiteNativeBill
  rw [actual_native_top_amplitude c zero]
  have sum : (∑ k ∈ Finset.range (order c.value), star (nativeCoefficient c (order c.value) k) *
      inner ℂ (centeredLogColumn (barC c) k) (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.correction c.value c.belowOne)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [actual_native_coefficient_zero c zero _ le_rfl, star_zero, zero_mul]
  rw [sum, add_zero]
  simp only [star_mul, star_neg, star_pow, star_ofNat]
  ring

/-- The physical cotest uses the original Riesz reader and the original fixed shift. -/
theorem actual_cotest_original_read (c : BurnolCompletedMellinCoordinate) :
    star (burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) =
      OriginalRieszFinitePairing.evaluatorSource c h₀ := by
  have read := congrArg (fun functional => functional (physicalCotest c))
    (burnolAmbientCompletedMellinEvaluator_restrict c)
  change burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2) =
    burnolCompletedMellinEvaluator c (physicalCotest c) at read
  rw [← burnolCompletedMellinRieszVector_readback] at read
  have fee := actual_projection_fee c (burnolCompletedMellinRieszVector c : BurnolL2)
  have fixed : burnolEvenAmbientProjection (burnolCompletedMellinRieszVector c : BurnolL2) =
      burnolCompletedMellinRieszVector c := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [fixed, actual_original_boundary_fee] at fee
  rw [read]
  change star (inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (physicalCotest c : BurnolL2)) = _
  exact (inner_conj_symm _ _).trans fee.symm

/-- Exact source normalization identifies the paid top with the original residual, with no missing half-axis factor. -/
theorem actual_original_top_normalization (c : BurnolCompletedMellinCoordinate) :
    -(2 : ℂ)^(order c.value) * star (bare c.value c.value *
      burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) =
        rieszAmplitude c * OriginalRieszFinitePairing.evaluatorSource c h₀ := by
  rw [star_mul, actual_cotest_original_read, rieszAmplitude, actual_bare_conjugate]
  ring


end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.Current
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedValue
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKFiniteOrderRelease.QuarterSourceCommutator OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
open scoped Topology InnerProductSpace
open private cotest_forward_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedValue
open private fourier_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private centered_constant_step from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "P0" => Constructor.zeroMean
local notation "mu" => burnolQuarterMeanCoefficient
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "R" => burnolDirectRightResolventCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Cq" => intervalConstant q

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c) = c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate, star_star]

def nativeOutgoingCotest (c : BurnolCompletedMellinCoordinate) (j : ℕ) : BurnolL2 :=
  ((sourceStep (barC c))^j) (pairedCotestForward c)

def nativeActedQuarter (c : BurnolCompletedMellinCoordinate) (j : ℕ) : Hq := Rq (nativeOutgoingCotest c j)

def nativeActedSchur (c : BurnolCompletedMellinCoordinate) (j : ℕ) : M := P0 (nativeActedQuarter c j)

def nativeActedAmplitude (c : BurnolCompletedMellinCoordinate) (j : ℕ) : ℂ :=
  -2 * (sourceTail (barC c) (nativeOutgoingCotest c j) +
    mu (nativeActedQuarter c j) * (q : ℂ)^(1 - star (barC c).value) / (1 - star (barC c).value))

private theorem outgoing_step (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    nativeOutgoingCotest c (j+1) = sourceStep (barC c) (nativeOutgoingCotest c j) := by
  rw [nativeOutgoingCotest, pow_succ', mul_apply_eq_comp]
  rfl

theorem actual_native_outgoing_cotest (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    nativeOutgoingCotest c j = ((sourceVolterraResolvent c)^j) (pairedCotestForward c) := by
  simp only [nativeOutgoingCotest, sourceStep, conjugate_twice]

private theorem outgoing_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    reflectL2 (nativeOutgoingCotest c j) = nativeOutgoingCotest c j := by
  induction j with
  | zero => simpa only [nativeOutgoingCotest, pow_zero, one_apply_eq_self] using cotest_forward_even c zero
  | succ j previous =>
    rw [outgoing_step]
    change reflectL2 (sourceVolterraResolvent _ (nativeOutgoingCotest c j)) = _
    rw [sourceVolterraResolvent_reflect, previous]
    rfl

private theorem acted_schur_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    sourceMeanZeroReflection (nativeActedSchur c j) = nativeActedSchur c j := by
  apply Subtype.ext
  change reflectRestricted q (burnolQuarterMeanZeroProjection (restrictToInterval q (nativeOutgoingCotest c j))) = _
  rw [← burnolQuarterMeanZeroProjection_reflect, ← restrictToInterval_reflectL2, outgoing_even c zero j]
  rfl

private theorem inverse_fourier_R (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    fourierL2.symm (R c value) = sourceStep (barC c) (fourierL2.symm value) := by
  have source := congrArg fourierL2.symm (fourier_source (barC c) (fourierL2.symm value))
  rw [fourierL2.symm_apply_apply, conjugate_twice, fourierL2.apply_symm_apply] at source
  exact source.symm

private theorem inverse_fourier_power (c : BurnolCompletedMellinCoordinate) (j : ℕ) (value : BurnolL2) :
    fourierL2.symm (((R c)^j) value) = ((sourceStep (barC c))^j) (fourierL2.symm value) := by
  induction j with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ j previous =>
    rw [pow_succ', mul_apply_eq_comp, inverse_fourier_R, previous, pow_succ', mul_apply_eq_comp]

/-- This is exactly the acted quarter input of the native boundary consumer. -/
theorem actual_native_acted_schur (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    P0 (Rq (fourierL2.symm (((R c)^j) (nativeCotest c)))) = nativeActedSchur c j := by
  rw [nativeCotest, actual_paired_cotest_common_value c zero, inverse_fourier_power]
  have even := cotest_forward_even c zero
  have fourier := congrArg fourierL2.symm (fourierL2_fourierL2 (pairedCotestForward c))
  rw [fourierL2.symm_apply_apply, even] at fourier
  rw [← fourier, fourierL2.symm_apply_apply]
  rfl

/-- The whole previous cotest supplies its tail and ordinary quarter mean to the next acted input. -/
theorem actual_native_acted_quarter_step (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    nativeActedQuarter c (j+1) = quarterStep (barC c) (nativeActedQuarter c j) +
      (-2 * sourceTail (barC c) (nativeOutgoingCotest c j)) • SingularCounting.powerL2 (barC c) := by
  rw [nativeActedQuarter, outgoing_step]
  exact source_quarter_step (barC c) _ (outgoing_even c zero j)

theorem actual_native_acted_schur_step (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (j : ℕ) :
    nativeActedSchur c (j+1) = centeredQuarterStep (barC c) (nativeActedSchur c j) +
      nativeActedAmplitude c j • SingularCounting.centeredPower (barC c) := by
  have full := congrArg P0 (actual_native_acted_quarter_step c zero j)
  rw [map_add, map_smul] at full
  have split : nativeActedQuarter c j = (nativeActedSchur c j : Hq) + mu (nativeActedQuarter c j) • Cq := by
    rw [nativeActedSchur, Constructor.zeroMean_read]
    module
  conv_rhs at full => rw [split]
  rw [map_add, map_smul, map_add, map_smul, centered_constant_step] at full
  change nativeActedSchur c (j+1) =
    (centeredQuarterStep (barC c) (nativeActedSchur c j) +
      mu (nativeActedQuarter c j) • ((-(2 : ℂ) * (q : ℂ)^(1 - star (barC c).value) /
        (1 - star (barC c).value)) • SingularCounting.centeredPower (barC c))) +
      (-2 * sourceTail (barC c) (nativeOutgoingCotest c j)) • SingularCounting.centeredPower (barC c) at full
  rw [nativeActedAmplitude]
  linear_combination (norm := module) full

private theorem schur_quarter_commutator (c : BurnolCompletedMellinCoordinate) (value : M)
    (even : sourceMeanZeroReflection value = value) :
    L (centeredQuarterStep c value) = centeredQuarterStep c (L value) + contactAction c (value : Hq) := by
  rw [← centered_contact_source c value even]
  change centeredQuarterStep c value - S (S (centeredQuarterStep c value)) =
    centeredQuarterStep c (value - S (S value)) +
      (centeredQuarterStep c (S (S value)) - S (S (centeredQuarterStep c value)))
  rw [map_sub]
  module

/-- The acted Schur word is generated at each real source step by the complete original six contacts. -/
theorem actual_native_acted_schur_source_step (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (j : ℕ) :
    L (nativeActedSchur c (j+1)) =
      centeredQuarterStep (barC c) (L (nativeActedSchur c j)) +
      contactAction (barC c) (nativeActedSchur c j : Hq) +
      nativeActedAmplitude c j • L (SingularCounting.centeredPower (barC c)) := by
  rw [actual_native_acted_schur_step c zero j, map_add, map_smul,
    schur_quarter_commutator _ _ (acted_schur_even c zero j)]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

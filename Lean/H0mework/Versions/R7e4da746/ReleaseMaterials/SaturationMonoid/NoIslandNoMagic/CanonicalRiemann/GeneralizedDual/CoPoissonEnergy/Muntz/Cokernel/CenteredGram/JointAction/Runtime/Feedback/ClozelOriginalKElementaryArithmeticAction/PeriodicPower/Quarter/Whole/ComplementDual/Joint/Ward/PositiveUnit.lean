import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitShell

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKFourierKernelDependentRAction OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => burnolMultiplicativeDilation

/-- The two original inverse terms combine into the actual smooth homogeneous source. -/
theorem actual_native_return_smooth_source (coordinate : BurnolCompletedMellinCoordinate) :
    nativeReturn coordinate = E (burnolRieszSingleFourierSource coordinate : Hq) -
      fourierL2 (OriginalRieszSourceGreen.gapState coordinate) +
      fourierL2 (E (S (smooth (dualRaw coordinate.value coordinate.belowOne)
        (actual_dual_integrable coordinate.value coordinate.belowOne)) : Hq)) := by
  have original := actual_original_FK_single_source coordinate
  change fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
    fourierL2 (OriginalRieszSourceGreen.gapState coordinate) +
      (fourierL2 (E (S (burnolRieszSingleFourierSource coordinate) : Hq)) -
        E (burnolRieszSingleFourierSource coordinate : Hq)) at original
  rw [nativeReturn, original, actual_original_dual_fourier_source, map_sub, map_smul]
  simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
  abel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
include nontrivial

private theorem unit_forward_original_B_zero (j : Nat) (before : j < m) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (U j) (D h (E (burnolRieszSingleFourierSource c : Hq))) = 0 := by
  let b := burnolRieszSingleFourierSource c
  let physical : BurnolPaAmbientCarrier :=
    ⟨U j, OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half j before⟩
  have centered : burnolQuarterMeanZeroProjection (Rq (U j)) = 0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr physical.property.1.1
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  have gap := OriginalKForcingGapAction.quarter_dilation_constant _ _ (sub_eq_zero.mp centered)
    (-h) (neg_nonpos.mpr nonnegative)
  have moved := (D (-h)).inner_map_eq_flip (U j) (E (b : Hq))
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  change inner ℂ (U j) (D h (E (b : Hq))) = 0
  rw [← moved]
  have restricted := ContinuousLinearMap.adjoint_inner_right Rq (D (-h) (U j)) (b : Hq)
  change inner ℂ (D (-h) (U j)) (E (b : Hq)) = inner ℂ (Rq (D (-h) (U j))) (b : Hq)
    at restricted
  have meanZero : inner ℂ (intervalConstant (1 / 4 : ℝ)) (b : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp b.property _ (Submodule.mem_span_singleton_self _)
  rw [restricted, gap, inner_smul_left, meanZero, mul_zero]

private theorem unit_fourier_shift_pair (j : Nat) (before : j < m) (h : ℝ) (value : BurnolL2) :
    inner ℂ (U j) (D h (fourierL2 value)) = inner ℂ (D h (fourierL2 (U j))) value := by
  have even : reflectL2 (D (-h) (U j)) = D (-h) (U j) := by
    rw [reflectL2_burnolMultiplicativeDilation, mem_evenL2ClosedFace_iff.mp
      (OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half j before).2]
  have inverse : fourierL2.symm (D (-h) (U j)) = fourierL2 (D (-h) (U j)) := by
    rw [fourierL2_symm_eq_reflect_fourierL2, ← fourierL2_reflectL2_commute, even]
  have moved := (D (-h)).inner_map_eq_flip (U j) (fourierL2 value)
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  rw [← moved]
  have fourier := fourierL2.inner_map_map (fourierL2.symm (D (-h) (U j))) value
  rw [fourierL2.apply_symm_apply, inverse] at fourier
  rw [fourier, fourierL2_burnolMultiplicativeDilation, neg_neg]

/-- The complete positive price is a single original smooth-source primitive and the full ambient mean/tail. -/
theorem actual_native_unit_positive_source (j : Nat) (before : j < m) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (U j) (D h (nativeReturn c)) =
      inner ℂ (Rq (D h (fourierL2 (U j))))
        (S (smooth (dualRaw (c).value (c).belowOne) (actual_dual_integrable (c).value (c).belowOne)) : Hq) -
      inner ℂ (D h (fourierL2 (U j))) (OriginalRieszSourceGreen.gapState c) := by
  rw [actual_native_return_smooth_source, map_add, map_sub, inner_add_right, inner_sub_right,
    unit_forward_original_B_zero observation nontrivial half j before h nonnegative, zero_sub,
    unit_fourier_shift_pair observation nontrivial half j before h,
    unit_fourier_shift_pair observation nontrivial half j before h]
  have restricted := ContinuousLinearMap.adjoint_inner_right Rq (D h (fourierL2 (U j)))
    (S (smooth (dualRaw (c).value (c).belowOne) (actual_dual_integrable (c).value (c).belowOne)) : Hq)
  change inner ℂ (D h (fourierL2 (U j))) (E _) = _ at restricted
  rw [restricted]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

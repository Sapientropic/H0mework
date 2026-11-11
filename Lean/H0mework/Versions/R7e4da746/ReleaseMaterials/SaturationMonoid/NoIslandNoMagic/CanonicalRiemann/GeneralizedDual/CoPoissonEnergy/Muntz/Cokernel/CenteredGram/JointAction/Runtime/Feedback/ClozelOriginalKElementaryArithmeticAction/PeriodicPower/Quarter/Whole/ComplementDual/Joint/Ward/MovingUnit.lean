import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.NativeUnitPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => burnolMultiplicativeDilation

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

theorem actual_unit_inward_log_return_zero (j : Nat) (before : j < m) (h : ℝ) (inward : h ≤ 0) :
    inner ℂ (U j) (D h (fourierL2 (E (S (logBFirst c 0) : Hq)))) = 0 := by
  let z : M := S (logBFirst c 0)
  have meanZero : inner ℂ (intervalConstant (1 / 4 : ℝ)) (z : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp z.property _ (Submodule.mem_span_singleton_self _)
  let physical : BurnolPaAmbientCarrier :=
    ⟨U j, OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half j before⟩
  let sibling := evenFaceFourierEquiv (1 / 4 : ℝ) physical
  have centered : burnolQuarterMeanZeroProjection (Rq (fourierL2 (U j))) = 0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr sibling.property.1.1
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  have gap := OriginalKForcingGapAction.quarter_dilation_constant _ _ (sub_eq_zero.mp centered) h inward
  have even : reflectL2 (D (-h) (U j)) = D (-h) (U j) := by
    rw [reflectL2_burnolMultiplicativeDilation, mem_evenL2ClosedFace_iff.mp physical.property.2]
  have inverse : fourierL2.symm (D (-h) (U j)) = fourierL2 (D (-h) (U j)) := by
    rw [fourierL2_symm_eq_reflect_fourierL2, ← fourierL2_reflectL2_commute, even]
  have moved := (D (-h)).inner_map_eq_flip (U j) (fourierL2 (E (z : Hq)))
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at moved
  change inner ℂ (U j) (D h (fourierL2 (E (z : Hq)))) = 0
  rw [← moved]
  have fourier := fourierL2.inner_map_map (fourierL2.symm (D (-h) (U j))) (E (z : Hq))
  rw [fourierL2.apply_symm_apply, inverse] at fourier
  rw [fourier, fourierL2_burnolMultiplicativeDilation, neg_neg]
  have restricted := ContinuousLinearMap.adjoint_inner_right Rq (D h (fourierL2 (U j))) (z : Hq)
  change inner ℂ (D h (fourierL2 (U j))) (E (z : Hq)) =
    inner ℂ (Rq (D h (fourierL2 (U j)))) (z : Hq) at restricted
  rw [restricted, gap, inner_smul_left, meanZero, mul_zero]

omit nontrivial in
private theorem original_fourier_kernel_shift (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    D h (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      fullMellinTranslationCharacter (star coordinate.value) (-h) •
        fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      fourierL2 (forcingIntegral coordinate (-h)) := by
  have actual := congrArg fourierL2 (original_finite_action coordinate (-h))
  rw [fourierL2_burnolMultiplicativeDilation, neg_neg, map_add, map_smul] at actual
  exact actual

theorem actual_native_unit_inward_top (h : ℝ) (inward : h ≤ 0) :
    inner ℂ (U (m - 1)) (D h (nativeReturn c)) =
      -fullMellinTranslationCharacter (star (c).value) (-h) * star e -
        inner ℂ (fourierL2 (U (m - 1))) (forcingIntegral c (-h)) := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have inverse : fourierL2.symm (U (m - 1)) = fourierL2 (U (m - 1)) := by
    have even : reflectL2 (U (m - 1)) = U (m - 1) := mem_evenL2ClosedFace_iff.mp
      (OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half (m - 1) (by omega)).2
    rw [fourierL2_symm_eq_reflect_fourierL2, ← fourierL2_reflectL2_commute, even]
  have paired := fourierL2.inner_map_map (fourierL2.symm (U (m - 1))) (forcingIntegral c (-h))
  rw [fourierL2.apply_symm_apply, inverse] at paired
  rw [nativeReturn, map_sub, map_smul, inner_sub_right, inner_smul_right,
    actual_unit_inward_log_return_zero observation nontrivial half (m - 1) (by omega) h inward,
    mul_zero, zero_sub, original_fourier_kernel_shift, inner_add_right, inner_smul_right, paired,
    ← inner_conj_symm (U (m - 1)) (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)),
    OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_top observation nontrivial half]
  simp only [starRingEnd_apply]
  ring

theorem actual_native_unit_minus_fixed_top :
    inner ℂ (U (m - 1)) (D (-Real.log stageZeroSonineQ) (nativeReturn c)) =
      -fullMellinTranslationCharacter (star (c).value) (Real.log stageZeroSonineQ) * star e -
        inner ℂ (fourierL2 (U (m - 1))) (forcingIntegral c (Real.log stageZeroSonineQ)) := by
  have nonnegative : 0 ≤ Real.log stageZeroSonineQ := Real.log_nonneg (by
    change 1 ≤ Real.sqrt 3
    exact Real.le_sqrt_of_sq_le (by norm_num))
  simpa only [neg_neg] using actual_native_unit_inward_top observation nontrivial half
    (-Real.log stageZeroSonineQ) (neg_nonpos.mpr nonnegative)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

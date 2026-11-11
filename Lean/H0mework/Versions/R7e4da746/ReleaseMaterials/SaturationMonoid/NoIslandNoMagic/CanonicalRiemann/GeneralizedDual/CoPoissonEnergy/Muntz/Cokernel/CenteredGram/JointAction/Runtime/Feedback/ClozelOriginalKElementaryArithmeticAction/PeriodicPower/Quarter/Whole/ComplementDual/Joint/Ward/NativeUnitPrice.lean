import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native OriginalRieszSource.Translator
open scoped InnerProductSpace Topology
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

/-- The acted full unit has its own actual Fourier quarter constant; the complete mean-zero return is read there. -/
theorem actual_unit_log_return_zero (j : Nat) (before : j < m) :
    inner ℂ (U j) (fourierL2 (E (S (logBFirst c 0) : Hq))) = 0 := by
  let z : M := S (logBFirst c 0)
  have meanZero : inner ℂ (intervalConstant (1 / 4 : ℝ)) (z : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp z.property _ (Submodule.mem_span_singleton_self _)
  have even : reflectL2 (U j) = U j := mem_evenL2ClosedFace_iff.mp
    (OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half j before).2
  have inverse : fourierL2.symm (U j) = fourierL2 (U j) := by
    rw [fourierL2_symm_eq_reflect_fourierL2, ← fourierL2_reflectL2_commute, even]
  have moved := fourierL2.inner_map_map (fourierL2.symm (U j)) (E (z : Hq))
  rw [fourierL2.apply_symm_apply, inverse] at moved
  change inner ℂ (U j) (fourierL2 (E (z : Hq))) = 0
  rw [moved]
  have restricted := ContinuousLinearMap.adjoint_inner_right Rq (fourierL2 (U j)) (z : Hq)
  change inner ℂ (fourierL2 (U j)) (E (z : Hq)) = inner ℂ (Rq (fourierL2 (U j))) (z : Hq)
    at restricted
  let physical : BurnolPaAmbientCarrier :=
    ⟨U j, OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half j before⟩
  let sibling := evenFaceFourierEquiv (1 / 4 : ℝ) physical
  have centered : burnolQuarterMeanZeroProjection (Rq (fourierL2 (U j))) = 0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr sibling.property.1.1
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  rw [restricted, sub_eq_zero.mp centered, inner_smul_left, meanZero, mul_zero]

theorem actual_native_unit_low (j : Nat) (before : j + 1 < m) :
    inner ℂ (U j) (nativeReturn c) = 0 := by
  rw [nativeReturn, inner_sub_right, inner_smul_right,
    actual_unit_log_return_zero observation nontrivial half j (by omega), mul_zero, zero_sub]
  have low := OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_low
    observation nontrivial half j before
  rw [← inner_conj_symm, low]
  simp only [map_zero, neg_zero]

/-- The first surviving source price is the original full unit top read, with its conjugation fixed. -/
theorem actual_native_unit_top : inner ℂ (U (m - 1)) (nativeReturn c) = -star e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  rw [nativeReturn, inner_sub_right, inner_smul_right,
    actual_unit_log_return_zero observation nontrivial half (m - 1) (by omega), mul_zero, zero_sub]
  rw [← inner_conj_symm,
    OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_top observation nontrivial half]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

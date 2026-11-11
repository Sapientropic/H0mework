import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.MovingUnit
import H0mework.Versions.R7e4da746.Arithmetic.RiemannNativeCurrent.UnitResponseRadius

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalRieszSource OriginalRieszFiniteSource
open scoped InnerProductSpace Topology
open private allPa_fourier_power_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
local notation "D" => burnolMultiplicativeDilation

private theorem resolvent_power_dilation (coordinate : BurnolCompletedMellinCoordinate)
    (j : Nat) (h : ℝ) (value : BurnolL2) :
    ((burnolDirectRightResolventCLM coordinate)^j) (D h value) =
      D h (((burnolDirectRightResolventCLM coordinate)^j) value) := by
  induction j with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ j ih =>
      simp only [pow_succ', mul_apply_eq_comp, ih]
      exact burnolDirectRightResolvent_dilation (coordinate.value / 2) h _

private theorem character_star (coordinate : ℂ) (h : ℝ) :
    star (fullMellinTranslationCharacter coordinate h) =
      fullMellinTranslationCharacter (star coordinate) h := by
  simp only [fullMellinTranslationCharacter, Complex.star_def]
  rw [← Complex.exp_conj]
  simp [map_ofNat]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
local notation "FK" => fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation

/-- The original radius source generates the whole shell before its actual Pa read. -/
theorem actual_unit_shell_dilation (j : Nat) (h : ℝ)
    (above : (1 / 4 : ℝ) < 4 * Real.exp (-h))
    (below : 4 * Real.exp (-h) < 4) :
    D h (U j) = fullMellinTranslationCharacter (c).value h • U j +
      fullMellinTranslationCharacter (c).value h •
        Rpow j (burnolActualUnitPowerShellPaState c (4 * Real.exp (-h)) above below : BurnolL2) := by
  have bounded : (4 * Real.exp (-h))⁻¹ ≤ 4 := by
    simpa only [one_div, inv_inv] using
      (inv_le_inv₀ (by positivity : (0 : ℝ) < 4 * Real.exp (-h))
        (by norm_num : (0 : ℝ) < 1 / 4)).mpr above.le
  have radius := burnolUnitTailResponse_radius_dilation c 4 (by norm_num) (by norm_num) h bounded
  have shell := burnolUnitTailResponse_shell c (4 * Real.exp (-h)) above below
  have split : burnolUnitTailResponse c (4 * Real.exp (-h)) =
      burnolUnitTailResponse c 4 + burnolUnitPowerShellWave c (4 * Real.exp (-h)) := by
    rw [← shell]
    abel
  change D h (((burnolDirectRightResolventCLM c)^j) (burnolUnitTailResponse c 4)) = _
  rw [← resolvent_power_dilation, radius, split, map_smul, map_add, smul_add]
  rfl

include nontrivial

theorem actual_unit_shell_fourier_price (j : Nat) (before : j < m) (h : ℝ)
    (above : (1 / 4 : ℝ) < 4 * Real.exp (-h))
    (below : 4 * Real.exp (-h) < 4) :
    inner ℂ FK (D h (U j)) =
      fullMellinTranslationCharacter (c).value h * inner ℂ FK (U j) := by
  have zero := allPa_fourier_power_zero observation nontrivial half
    (burnolActualUnitPowerShellPaState c (4 * Real.exp (-h)) above below)
    (burnolActualUnitPowerShellPaState_mem c (4 * Real.exp (-h)) above below) j before
  rw [actual_unit_shell_dilation observation half j h above below,
    inner_add_right, inner_smul_right, inner_smul_right, zero, mul_zero, add_zero]

theorem actual_native_unit_reverse_shell_top (h : ℝ) (nonnegative : 0 ≤ h)
    (above : (1 / 4 : ℝ) < 4 * Real.exp (-h))
    (below : 4 * Real.exp (-h) < 4) :
    inner ℂ (U (m - 1)) (D (-h) (nativeReturn c)) =
      -fullMellinTranslationCharacter (star (c).value) h * star e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have price := actual_unit_shell_fourier_price observation nontrivial half (m - 1) (by omega) h above below
  rw [OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_fourier_top observation nontrivial half] at price
  have moved := (D h).inner_map_eq_flip (U (m - 1)) FK
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at moved
  rw [nativeReturn, map_sub, map_smul, inner_sub_right, inner_smul_right,
    actual_unit_inward_log_return_zero observation nontrivial half (m - 1) (by omega)
      (-h) (neg_nonpos.mpr nonnegative), mul_zero, zero_sub, ← moved,
    ← inner_conj_symm, price]
  simp only [starRingEnd_apply, star_mul, character_star]
  ring

omit nontrivial in
private theorem fixed_shell_bounds :
    (1 / 4 : ℝ) < 4 * Real.exp (-Real.log stageZeroSonineQ) ∧
      4 * Real.exp (-Real.log stageZeroSonineQ) < 4 := by
  have rootSquare : stageZeroSonineQ ^ 2 = 3 := by
    change Real.sqrt 3 ^ 2 = 3
    exact Real.sq_sqrt (by norm_num)
  have lower : 1 < stageZeroSonineQ := by nlinarith [stageZeroSonineQ_pos]
  have upper : stageZeroSonineQ < 2 := by nlinarith [stageZeroSonineQ_pos]
  rw [Real.exp_neg, Real.exp_log stageZeroSonineQ_pos, ← div_eq_mul_inv]
  constructor
  · rw [lt_div_iff₀ stageZeroSonineQ_pos]
    linarith
  · rw [div_lt_iff₀ stageZeroSonineQ_pos]
    linarith

theorem actual_native_unit_minus_fixed_shell_top :
    inner ℂ (U (m - 1)) (D (-Real.log stageZeroSonineQ) (nativeReturn c)) =
      -fullMellinTranslationCharacter (star (c).value) (Real.log stageZeroSonineQ) * star e :=
  actual_native_unit_reverse_shell_top observation nontrivial half (Real.log stageZeroSonineQ)
    (Real.log_nonneg (le_of_lt (by
      have rootSquare : stageZeroSonineQ ^ 2 = 3 := by
        change Real.sqrt 3 ^ 2 = 3
        exact Real.sq_sqrt (by norm_num)
      nlinarith [stageZeroSonineQ_pos]))) fixed_shell_bounds.1 fixed_shell_bounds.2

theorem actual_original_unit_fixed_forcing_zero :
    inner ℂ (fourierL2 (U (m - 1))) (forcingIntegral c (Real.log stageZeroSonineQ)) = 0 := by
  have complete := actual_native_unit_minus_fixed_top observation nontrivial half
  rw [actual_native_unit_minus_fixed_shell_top observation nontrivial half] at complete
  exact (sub_eq_self.mp complete.symm)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

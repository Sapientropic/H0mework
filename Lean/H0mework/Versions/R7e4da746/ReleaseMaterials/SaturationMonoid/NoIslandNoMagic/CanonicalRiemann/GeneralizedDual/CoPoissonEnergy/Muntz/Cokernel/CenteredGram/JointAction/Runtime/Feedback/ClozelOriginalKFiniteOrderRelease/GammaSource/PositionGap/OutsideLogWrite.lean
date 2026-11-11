import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierXiOutsideStart
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank

open BurnolPhysicalState UnitPowerJordanSource UnitPowerJordanAction
open scoped BigOperators

open private fourier_R from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction
open private position_read actual_position_step source_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction

local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => burnolDirectRightResolventCLM
local notation "F₂" => fourierL2
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "M" => BurnolQuarterMeanZeroCarrier

abbrev LogStock := Nat →₀ ℂ

def logSynthesis (c : BurnolCompletedMellinCoordinate) : LogStock →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ (centeredLogColumn c)

/-- The old log degrees advance by one, and the original centering contact enters degree zero. -/
def logInventoryStep (c : BurnolCompletedMellinCoordinate) : LogStock →ₗ[ℂ] LogStock :=
  (-2:ℂ) • Finsupp.lmapDomain ℂ ℂ Nat.succ +
    (Finsupp.lsingle 0).comp (Finsupp.linearCombination ℂ fun k => 2*meanContact c k)

theorem log_inventory_synthesis (c : BurnolCompletedMellinCoordinate) (a : LogStock) :
    logSynthesis c (logInventoryStep c a) = centeredQuarterStep c (logSynthesis c a) := by
  have same : (logSynthesis c).comp (logInventoryStep c) =
      (centeredQuarterStep c).toLinearMap.comp (logSynthesis c) := by
    apply Finsupp.lhom_ext
    intro k z
    simp only [logInventoryStep, logSynthesis, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, map_add, map_smul, ContinuousLinearMap.coe_coe,
      centered_log_step]
    module
  exact LinearMap.congr_fun same a

private theorem log_inventory_succ (c : BurnolCompletedMellinCoordinate) (a : LogStock) (k : Nat) :
    logInventoryStep c a (k+1) = (-2:ℂ)*a k := by
  simp only [logInventoryStep, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.lsingle_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_eq_of_ne (Nat.succ_ne_zero k), add_zero]
  rw [Finsupp.mapDomain_apply Nat.succ_injective]
  rfl

private def headPrice (c : BurnolCompletedMellinCoordinate) (n : Nat) : ℂ :=
  GenericSourceStepBAction.currentAmplitude (barC c) (F₂ (((R c)^n) seed))

private theorem centered_fourier_power_succ (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    centeredFourierPower c (n+1) =
      centeredQuarterStep (barC c) (centeredFourierPower c n) +
        headPrice c n • centeredLogColumn (barC c) 0 := by
  let value := ((R c)^n) seed
  have evenValue : reflectL2 value = value := by
    dsimp only [value]
    rw [← CofinalCanonicalSourceMaterial.actual_iterate_power]
    exact CofinalCanonicalSourceMaterial.actual_iterate_even c seed
      (mem_evenL2ClosedFace_iff.mp (burnolPaCombApproximation 0).property.2) n
  have even : reflectL2 (F₂ value) = F₂ value := by
    rw [← fourierL2_reflectL2_commute, evenValue]
  have paid := actual_position_step (barC c) (F₂ value) even
  rw [position_read _ (source_even (barC c) _ even), position_read _ even] at paid
  unfold centeredFourierPower
  rw [pow_succ', mul_apply_eq_comp, fourier_R]
  exact paid

/-- The original Xi boundary and each actual Fourier head generate the finite outside log inventory. -/
def logCoefficients (c : BurnolCompletedMellinCoordinate) : Nat → LogStock :=
  Nat.rec (Finsupp.single 0 (firstOutsidePrice c)) fun k old =>
    logInventoryStep (barC c) old + Finsupp.single 0 (headPrice c (xiOrder c+1+k))

private theorem log_coefficients_succ (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    logCoefficients c (k+1) = logInventoryStep (barC c) (logCoefficients c k) +
      Finsupp.single 0 (headPrice c (xiOrder c+1+k)) := rfl

theorem actual_fourier_log_inventory (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    logSynthesis (barC c) (logCoefficients c k) = centeredFourierPower c (xiOrder c+1+k) := by
  induction k with
  | zero =>
    rw [Nat.add_zero, actual_fourier_outside_start]
    exact Finsupp.linearCombination_single _ _ _
  | succ k previous =>
    rw [log_coefficients_succ, map_add, log_inventory_synthesis, previous,
      show xiOrder c+1+(k+1) = (xiOrder c+1+k)+1 by omega, centered_fourier_power_succ]
    change _ + Finsupp.linearCombination ℂ (centeredLogColumn (barC c))
      (Finsupp.single 0 (headPrice c (xiOrder c+1+k))) = _
    rw [Finsupp.linearCombination_single]

/-- The generated coefficient at the current highest degree comes from the original Xi boundary. -/
theorem log_coefficients_top (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    logCoefficients c k k = (-2:ℂ)^k * firstOutsidePrice c := by
  induction k with
  | zero => simp [logCoefficients]
  | succ k prior =>
    rw [log_coefficients_succ, Finsupp.add_apply, log_inventory_succ,
      Finsupp.single_eq_of_ne (Nat.succ_ne_zero k), add_zero, prior, pow_succ']
    ring

theorem log_coefficients_above (c : BurnolCompletedMellinCoordinate) (k j : Nat) (beyond : k < j) :
    logCoefficients c k j = 0 := by
  induction k generalizing j with
  | zero =>
    change Finsupp.single 0 (firstOutsidePrice c) j = 0
    exact Finsupp.single_eq_of_ne (Nat.ne_of_gt beyond)
  | succ k previous =>
    cases j with
    | zero => omega
    | succ j =>
      rw [log_coefficients_succ, Finsupp.add_apply, log_inventory_succ,
        Finsupp.single_eq_of_ne (Nat.succ_ne_zero j), add_zero,
        previous j (Nat.lt_of_succ_lt_succ beyond), mul_zero]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

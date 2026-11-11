import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CombConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.LogAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor

open BurnolPhysicalState
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.FiniteLogCounting
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open BurnolPhysicalState.OriginalRSourceJointContact.LogAction
open CombConductor

open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource

local notation "R" => burnolDirectRightResolventCLM
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

private theorem right_quarter (c : BurnolCompletedMellinCoordinate) : 1/4 < (c.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

private def positionHistory (c : BurnolCompletedMellinCoordinate) (step : Nat) : BurnolL2 :=
  Nat.rec seedPositionLog (fun k old =>
    R c old - directLogMoment (c.value/2) (((R c)^k) seed)) step

private theorem position_history_graph (c : BurnolCompletedMellinCoordinate) (step : Nat) :
    LogPair (((R c)^step) seed) (positionHistory c step) := by
  induction step with
  | zero => exact actual_comb_seed_position_log
  | succ step previous =>
    rw [pow_succ', mul_apply_eq_comp]
    exact actual_direct_R_log (c.value/2) (right_quarter c) _ _ previous

private theorem conductor_history_graph (c : BurnolCompletedMellinCoordinate) (step : Nat) :
    GammaPair (((R c)^step) seed) (((R c)^step) seedGamma) := by
  induction step with
  | zero => exact actual_comb_seed_gamma
  | succ step previous =>
    rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    exact actual_Gamma_R c _ _ previous

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
private abbrev sourceIndex (ordinal : Nat) : Nat := m + (ordinal+2)

local notation "idx" => sourceIndex observation

private theorem literal_raw (ordinal : Nat) : raw ordinal = ((R c)^(idx ordinal)) seed := by
  have same : OriginalKCombPhysicalAction.R observation nontrivial half = R c :=
    ContinuousLinearMap.ext (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half)
  rw [OriginalKCombFirstFullSourceDynamics.raw_xi_source, same, ← ContinuousLinearMap.toLinearMap_pow]
  rfl

/-- The original Xi order and actual cofinal index select the conductor of the whole raw field. -/
def gammaAt (ordinal : Nat) : BurnolL2 := ((R c)^(idx ordinal)) seedGamma

def positionLogAt (ordinal : Nat) : BurnolL2 := positionHistory c (idx ordinal)

def inverseLogAt (ordinal : Nat) : BurnolL2 :=
  fourierL2.symm (gammaAt observation half ordinal - positionLogAt observation half ordinal)

theorem actual_division_conductor (ordinal : Nat) :
    GammaPair (raw ordinal) (gammaAt observation half ordinal) ∧
      LogPair (raw ordinal) (positionLogAt observation half ordinal) ∧
      LogPair (fourierL2.symm (raw ordinal)) (inverseLogAt observation half ordinal) := by
  rw [literal_raw observation nontrivial half depth]
  exact ⟨conductor_history_graph c _, position_history_graph c _,
    inverse_log_from_complete_source _ _ _ (conductor_history_graph c _) (position_history_graph c _)⟩

/-- The same literal write gives the conductor recurrence and the directed position-log correction. -/
theorem actual_division_conductor_step (ordinal : Nat) :
    gammaAt observation half (ordinal+1) = R c (gammaAt observation half ordinal) ∧
      positionLogAt observation half (ordinal+1) =
        R c (positionLogAt observation half ordinal) - directLogMoment ((c).value/2) (raw ordinal) := by
  have tick : idx (ordinal+1) = idx ordinal + 1 := by
    dsimp [sourceIndex]
    omega
  constructor
  · unfold gammaAt
    rw [tick, pow_succ', mul_apply_eq_comp]
  · unfold positionLogAt
    rw [tick, literal_raw observation nontrivial half depth]
    rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

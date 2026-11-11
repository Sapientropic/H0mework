import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJetStepSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusJetFeedbackSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReturnJetStepSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace S
export OriginalWholeDebtRJointMobiusJetFeedbackSource
  (nextPa nextQ nextOutside nextWhole actual_next_Pa actual_next_Q actual_next_outside actual_next_whole)
end S
namespace J
export OriginalKFiniteOrderRelease.UnitPowerJordanSource (sourceStep sourceStep_actual)
end J
open private coordinate_is_division from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceCalculation

def paResult (c : BurnolCompletedMellinCoordinate) (environment : Env Value Var) : BurnolPaAmbientCarrier :=
  OriginalKCombCofinalPaAction.E ((stepCode c).eval environment)

theorem pa_code_result (c : BurnolCompletedMellinCoordinate) (environment : Env Value Var) :
    (paCode c).eval environment = (paResult c environment : BurnolL2) := rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
variable (environment : Env Value Var)
variable (source : environment () 0 = OriginalWholeDebtRJointMobiusReturnJordanSource.jet
  observation nontrivial half (generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate))

include source

theorem actual_step_code : (stepCode c).eval environment = J.sourceStep c
    (OriginalWholeDebtRJointMobiusReturnJordanSource.jet observation nontrivial half m) := by
  change (burnolDirectRightResolventCLM c).adjoint (environment () 0) = _
  rw [source, J.sourceStep_actual]

theorem actual_pa_result : paResult c environment = S.nextPa observation nontrivial half := by
  unfold paResult
  rw [actual_step_code observation nontrivial half environment source]
  exact S.actual_next_Pa observation nontrivial half

theorem actual_pa_code : (paCode c).eval environment = (S.nextPa observation nontrivial half : BurnolL2) := by
  rw [pa_code_result, actual_pa_result observation nontrivial half environment source]

theorem actual_step_Q : OriginalKCombCofinalPaAction.Q ((stepCode c).eval environment) =
    S.nextQ observation nontrivial half := by
  rw [actual_step_code observation nontrivial half environment source]
  exact S.actual_next_Q observation nontrivial half

theorem actual_step_outside : OriginalKCombPhysicalAction.physicalRemainder ((stepCode c).eval environment) =
    S.nextOutside observation nontrivial half := by
  rw [actual_step_code observation nontrivial half environment source]
  exact S.actual_next_outside observation nontrivial half

theorem actual_step_whole : (stepCode c).eval environment =
    (S.nextPa observation nontrivial half : BurnolL2) +
      (S.nextQ observation nontrivial half : BurnolL2) + S.nextOutside observation nontrivial half := by
  rw [actual_step_code observation nontrivial half environment source]
  exact S.actual_next_whole observation nontrivial half

omit source
variable (pa : environment () 0 = (S.nextPa observation nontrivial half : BurnolL2))
include pa

theorem actual_prefix_code : (prefixCode c m).eval environment =
    CombSource.Division.rawIterate observation half.down m (S.nextPa observation nontrivial half : BurnolL2) := by
  rw [OriginalKReturnJordanSourceCalculation.prefix_code_eval, pa,
    coordinate_is_division observation nontrivial half]
  rfl

theorem actual_next_code : (nextCode c m).eval environment =
    CombSource.Division.rawIterate observation half.down (m + 1) (S.nextPa observation nontrivial half : BurnolL2) := by
  change burnolDirectRightResolventCLM c ((prefixCode c m).eval environment) = _
  rw [OriginalKReturnJordanSourceCalculation.prefix_code_eval, pa,
    coordinate_is_division observation nontrivial half]
  change CombSource.Division.rawAction observation half.down
    (((CombSource.Division.rawAction observation half.down)^m) _) = _
  rw [CombSource.Division.rawIterate, pow_succ', mul_apply_eq_comp]

end OriginalKReturnJetStepSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

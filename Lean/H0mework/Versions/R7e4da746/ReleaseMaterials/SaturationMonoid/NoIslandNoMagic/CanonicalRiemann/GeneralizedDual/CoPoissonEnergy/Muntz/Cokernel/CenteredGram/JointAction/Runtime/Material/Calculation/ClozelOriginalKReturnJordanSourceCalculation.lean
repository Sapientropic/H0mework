import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnJordanSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReturnJordanSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource OriginalKDirectRCofinalOutsideVolterraSource
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "u" => OriginalWholeDebtRJointMobiusUnitSource.response c

private theorem coordinate_is_division : c = burnolDivisionZeroCompletedMellinCoordinate observation half.down := by
  apply coordinate_eq
  rfl

variable (environment : Env Value Var)
variable (response : environment () 0 =
  OriginalWholeDebtRJointMobiusUnitSource.response
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))
variable (result : environment () 1 = OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half)

include response result

theorem actual_return_code : (returnCode c).eval environment =
    (OriginalWholeDebtRJointMobiusReturnAction.returned observation nontrivial half : BurnolL2) := by
  change (burnolEvenAmbientProjection
    (sourceCayley (OriginalPrimitiveRankBalance.conjugateCoordinate c)
      (environment () 0 + (sourceDamping (OriginalPrimitiveRankBalance.conjugateCoordinate c) : ℂ) •
        (burnolEvenAmbientProjection (fourierL2 (environment () 1)) : BurnolL2))) : BurnolL2) = _
  rw [response, result, OriginalWholeDebtRJointMobiusReturnAction.returned,
    OriginalWholeDebtRJointMobiusReturnAction.actual_source_return_input,
    ← OriginalWholeDebtRJointMobiusTateRSource.actual_updated_wave]
  unfold OriginalWholeDebtRJointMobiusReturnSource.value
  rfl

theorem actual_difference_code : (differenceCode c).eval environment =
    OriginalWholeDebtRJointMobiusReturnJordanSource.returnDifference observation nontrivial half := by
  change (returnCode c).eval environment + (-1 : ℂ) • environment () 0 = _
  rw [actual_return_code observation nontrivial half environment response result, response, neg_one_smul,
    OriginalWholeDebtRJointMobiusReturnJordanSource.returnDifference, sub_eq_add_neg]

theorem actual_source_code : (sourceCode c).eval environment =
    OriginalWholeDebtRJointMobiusReturnJordanSource.returnSource observation nontrivial half := by
  change jQuarterAmplitude c • (differenceCode c).eval environment -
    hQuarterAmplitude c • fourierL2 ((differenceCode c).eval environment) = _
  rw [actual_difference_code observation nontrivial half environment response result]
  rfl

theorem actual_jet_code (order : Nat) : (jetCode c order).eval environment =
    OriginalWholeDebtRJointMobiusReturnJordanSource.jet observation nontrivial half order := by
  induction order with
  | zero => exact actual_source_code observation nontrivial half environment response result
  | succ order previous =>
    change (burnolDirectRightResolventCLM c).adjoint ((jetCode c order).eval environment) = _
    rw [previous, OriginalWholeDebtRJointMobiusReturnJordanSource.actual_jet_next]

theorem actual_pa_code : (paCode c m).eval environment =
    (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2) := by
  change (OriginalKCombCofinalPaAction.E ((jetCode c m).eval environment) : BurnolL2) = _
  rw [actual_jet_code observation nontrivial half environment response result]
  rfl

omit response result

theorem prefix_code_eval (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) :
    (prefixCode coordinate order).eval environment =
      ((burnolDirectRightResolventCLM coordinate)^order) (environment () 0) := by
  induction order with
  | zero => rfl
  | succ order previous =>
    change burnolDirectRightResolventCLM coordinate ((prefixCode coordinate order).eval environment) = _
    rw [previous, pow_succ', mul_apply_eq_comp]

variable (pa : environment () 0 =
  (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half
    (generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate) : BurnolL2))

include pa

theorem actual_prefix_code : (prefixCode c m).eval environment =
    CombSource.Division.rawIterate observation half.down m
      (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2) := by
  rw [prefix_code_eval, pa, coordinate_is_division]
  rfl

theorem actual_next_code : (nextCode c m).eval environment =
    CombSource.Division.rawIterate observation half.down (m+1)
      (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2) := by
  change burnolDirectRightResolventCLM c ((prefixCode c m).eval environment) = _
  rw [prefix_code_eval, pa, coordinate_is_division]
  change CombSource.Division.rawAction observation half.down
    (((CombSource.Division.rawAction observation half.down)^m) _) = _
  rw [CombSource.Division.rawIterate, pow_succ', mul_apply_eq_comp]

end OriginalKReturnJordanSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusRSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKJointMobiusRSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution

theorem actual_response_code (c : BurnolCompletedMellinCoordinate) :
    (responseCode c).eval sourceEnvironment = OriginalWholeDebtRJointMobiusUnitSource.response c := by
  change burnolEvenAmbientProjection
      ((OriginalKJointMobiusSourceCalculation.sourceCode c).eval sourceEnvironment) +
      (-1 : ℂ) • OriginalWholeDebtRJointMobiusSource.paWave c +
      (-1 : ℂ) • (OriginalWholeDebtRJointMobiusUnitSource.unitCoefficient c •
        burnolUnitTailResponse c 4) = _
  rw [neg_one_smul, neg_one_smul]
  simp only [← sub_eq_add_neg]
  change (OriginalWholeDebtRJointMobiusSource.jointValue c : BurnolL2) -
    OriginalWholeDebtRJointMobiusSource.paWave c -
      OriginalWholeDebtRJointMobiusUnitSource.unitCoefficient c • burnolUnitTailResponse c 4 = _
  rw [OriginalWholeDebtRJointMobiusProgramme.actual_joint_wave_response,
    OriginalWholeDebtRJointMobiusUnitSource.actual_source_update]
  abel

theorem actual_input_code (c : BurnolCompletedMellinCoordinate) :
    (inputCode c).eval sourceEnvironment =
      fourierL2 (OriginalWholeDebtRJointMobiusUnitSource.response c) := by
  change fourierL2 ((responseCode c).eval sourceEnvironment) = _
  rw [actual_response_code]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

theorem actual_code_field :
    (code c).eval sourceEnvironment =
      OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half := by
  rw [code_eval, actual_input_code]
  rfl

theorem actual_code_source_effect :
    OriginalKCombPhysicalAction.physicalRemainder ((code c).eval sourceEnvironment) =
      (2 * OriginalNextEndpointProgramme.programmePrice c (Real.log stageZeroSonineQ)) •
        OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c := by
  rw [actual_code_field]
  exact OriginalWholeDebtRJointMobiusRActionSource.actual_source_effect observation nontrivial half

end OriginalKJointMobiusRSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativeCayleySourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativeCayleyFaithfulness

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleySourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
namespace Native
export OriginalKCrossParameterRAdjointSource.PaNativePortSource
  (Pa correction actual_original_R)
end Native
namespace Original
export OriginalWholeDebtRJointMobiusPaCayleySource
  (rawUpdate sourceNext sourceQ unitQ actual_source_Q actual_whole_update actual_outside_zero)
end Original
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Read only the actual R and Pa inputs; this operation does not execute another R. -/
theorem raw_code_read (c : BurnolCompletedMellinCoordinate) (environment : Env Value Var) :
    (rawCode c).eval environment = environment () 1 +
      (sourceDamping c : ℂ) • environment () 0 := rfl

def paResult (environment : Env Value Var) : BurnolPaAmbientCarrier :=
  OriginalKCombCofinalPaAction.E (environment () 0)

def qResult (environment : Env Value Var) : BurnolPaAmbientCarrier :=
  OriginalKCombCofinalPaAction.Q (environment () 0)

theorem pa_code_result (environment : Env Value Var) :
    paCode.eval environment = (paResult environment : BurnolL2) := rfl

theorem q_code_result (environment : Env Value Var) :
    qCode.eval environment = (qResult environment : BurnolL2) := rfl

theorem actual_raw_code (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) (input : BurnolL2)
    (actualR : environment () 0 = burnolDirectRightResolventCLM c input)
    (actualPa : environment () 1 = input) :
    (rawCode c).eval environment = sourceCayley c input := by
  rw [raw_code_read, actualR, actualPa, sourceCayley_apply]
  rfl

/-- The full true unit survives before either projection is read. -/
theorem actual_full_unit_code (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) (input : ↥Native.Pa)
    (actualR : environment () 0 = burnolDirectRightResolventCLM c (input.val : BurnolL2))
    (actualPa : environment () 1 = (input.val : BurnolL2)) :
    (rawCode c).eval environment = (input.val : BurnolL2) +
      (sourceDamping c : ℂ) • ((Native.correction c input).val : BurnolL2) +
        ((sourceDamping c : ℂ) * burnolPaResolventSourceCoefficient c input.val) •
          burnolUnitTailResponse c 4 := by
  have original := Native.actual_original_R c 0 input
  change burnolDirectRightResolventCLM c (input.val : BurnolL2) =
    ((Native.correction c input).val : BurnolL2) +
      burnolPaResolventSourceCoefficient c input.val • burnolUnitTailResponse c 4 at original
  rw [raw_code_read, actualR, actualPa, original, smul_add, smul_smul]
  module

/-- Whole-U conservation precedes Pa loss or any debt interpretation. -/
theorem actual_whole_norm (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) (input : BurnolL2)
    (actualR : environment () 0 = burnolDirectRightResolventCLM c input)
    (actualPa : environment () 1 = input) :
    ‖(rawCode c).eval environment‖ = ‖input‖ := by
  rw [actual_raw_code c environment input actualR actualPa]
  exact sourceCayley_norm c input

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

theorem actual_pa_result (environment : Env Value Var) (input : ↥Native.Pa)
    (actualU : environment () 0 = Original.rawUpdate observation nontrivial half input) :
    paResult environment = (Original.sourceNext observation nontrivial half input).val := by
  change OriginalKCombCofinalPaAction.E (environment () 0) = _
  rw [actualU]
  rfl

theorem actual_Q_result (environment : Env Value Var) (input : ↥Native.Pa)
    (actualU : environment () 0 = Original.rawUpdate observation nontrivial half input) :
    qResult environment = Original.sourceQ observation nontrivial half input := by
  change OriginalKCombCofinalPaAction.Q (environment () 0) = _
  rw [actualU]
  exact Original.actual_source_Q observation nontrivial half input

theorem actual_Q_vector (environment : Env Value Var) (input : ↥Native.Pa)
    (actualU : environment () 0 = Original.rawUpdate observation nontrivial half input) :
    qResult environment =
      ((sourceDamping c : ℂ) * burnolPaResolventSourceCoefficient c input.val) •
        Original.unitQ observation nontrivial half :=
  actual_Q_result observation nontrivial half environment input actualU

theorem actual_whole_code (environment : Env Value Var) (input : ↥Native.Pa)
    (actualR : environment () 0 = burnolDirectRightResolventCLM c (input.val : BurnolL2))
    (actualPa : environment () 1 = (input.val : BurnolL2)) :
    (rawCode c).eval environment =
      ((Original.sourceNext observation nontrivial half input).val : BurnolL2) +
        (Original.sourceQ observation nontrivial half input : BurnolL2) := by
  rw [actual_raw_code c environment (input.val : BurnolL2) actualR actualPa]
  exact Original.actual_whole_update observation nontrivial half input

/-- Both executed projections read the same first actual U value. -/
theorem actual_shared_whole (environment paEnvironment qEnvironment : Env Value Var) (input : ↥Native.Pa)
    (actualR : environment () 0 = burnolDirectRightResolventCLM c (input.val : BurnolL2))
    (actualPa : environment () 1 = (input.val : BurnolL2))
    (paU : paEnvironment () 0 = (rawCode c).eval environment)
    (qU : qEnvironment () 0 = (rawCode c).eval environment) :
    (rawCode c).eval environment = paCode.eval paEnvironment + qCode.eval qEnvironment := by
  have raw : (rawCode c).eval environment = Original.rawUpdate observation nontrivial half input :=
    actual_raw_code c environment (input.val : BurnolL2) actualR actualPa
  rw [pa_code_result, q_code_result,
    actual_pa_result observation nontrivial half paEnvironment input (paU.trans raw),
    actual_Q_result observation nontrivial half qEnvironment input (qU.trans raw)]
  exact actual_whole_code observation nontrivial half environment input actualR actualPa

end OriginalKPaNativeCayleySourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

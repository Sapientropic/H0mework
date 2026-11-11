import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReciprocalCotestSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReciprocalCotestSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution

open private sub_eval from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram

namespace NativeSource
export OriginalWholeDebtRReciprocalCotestActionSource
  (nativeInput sourceY fourierColumn reciprocalCotest weightedField weighted_field_action)
end NativeSource

theorem native_input_code_eval (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (nativeInputCode c).eval environment = NativeSource.nativeInput c := by
  rw [nativeInputCode, sub_eval]
  rfl

theorem sourceY_code_eval (c : BurnolCompletedMellinCoordinate) (endpoint : ℝ)
    (environment : Env Value Var) :
    (sourceYCode c endpoint).eval environment = NativeSource.sourceY c endpoint := by
  rw [sourceYCode, sub_eval]
  change Wave.nativeAction (c.value - 1/2) endpoint ((nativeInputCode c).eval environment) -
    Coupling.coupling1 c •
      (Wave.edgeIntegralCode (Wave.starCoordinate c) endpoint).eval environment = _
  rw [native_input_code_eval, OriginalKPowerWaveSourceCalculation.edge_integral_code_eval]
  rfl

/-- The fixed source program retains the original wave's actual second column. -/
theorem second_column_code_eval (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (secondColumnCode c fixedShift).eval environment = NativeSource.fourierColumn c := by
  change (1/2 : ℂ) • ((sourceYCode c (-fixedShift)).eval environment +
    (sourceYCode c fixedShift).eval environment) = _
  rw [sourceY_code_eval, sourceY_code_eval]
  rfl

theorem actual_reciprocal_value (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (reciprocalCode c fixedShift).eval environment = NativeSource.reciprocalCotest c := by
  rw [reciprocal_code_eval, second_column_code_eval]
  rfl

/-- The runtime expression's R result consumes the paid full forcing/contact equation. -/
theorem actual_code_value (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (code c fixedShift).eval environment = NativeSource.weightedField c := by
  rw [code_eval, actual_reciprocal_value]
  exact (NativeSource.weighted_field_action c).symm

theorem reader_value (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader observation nontrivial half occurrence).expression.eval
      (reader observation nontrivial half occurrence).environment =
        NativeSource.weightedField (coordinate observation nontrivial half occurrence) :=
  actual_code_value _ _

end OriginalKReciprocalCotestSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

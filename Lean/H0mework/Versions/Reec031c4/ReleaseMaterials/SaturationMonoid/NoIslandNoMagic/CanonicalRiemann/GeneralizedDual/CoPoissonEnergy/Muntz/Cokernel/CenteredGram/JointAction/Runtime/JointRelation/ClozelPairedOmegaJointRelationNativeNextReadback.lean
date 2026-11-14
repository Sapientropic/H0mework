import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationNativeNextTransition
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationShiftActionReadback

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistoryTransition

noncomputable section

theorem nativeNextJoint_transport_originalEvaluator
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    step.faithful.completionEvaluation
        (runtimeJointFaithfulSoundnessAt observation nontrivial depth)
        (nativeNextJointCompletionMap depth
          ((nativeNextJointHistory (depth + 1)).completionProjection
            (rawJointPhaseGenerator
              (CanonicalUnitArithmeticRoot.emitted
                (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
              stage))) =
      runtimeJointRelationGeneratorValue observation nontrivial
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current +
          (stage + 1), .phase) := by
  dsimp only
  have transported := nativeNextJoint_phase_transport_eq_sourceShift depth stage
  have evaluated := rawJointShift_phase_originalEvaluator
    observation nontrivial depth stage
  calc
    _ = (runtimeJointFaithfulStepAt observation nontrivial depth
          ).faithful.completionEvaluation
          (runtimeJointFaithfulSoundnessAt observation nontrivial depth)
          (rawJointShiftOnCompletion
            (CanonicalUnitArithmeticRoot.emitted
              (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
            ((nativeNextJointHistory depth).completionProjection
              (rawJointPhaseGenerator
                (CanonicalUnitArithmeticRoot.emitted
                  (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
                stage))) := congrArg _ transported
    _ = _ := evaluated

theorem nativeNextJoint_transport_originalRoot_consumer
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    (step.faithful.completionEvaluation
        (runtimeJointFaithfulSoundnessAt observation nontrivial depth)
        (nativeNextJointCompletionMap depth
          ((nativeNextJointHistory (depth + 1)).completionProjection
            (rawJointPhaseGenerator
              (CanonicalUnitArithmeticRoot.emitted
                (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
              stage))) =
      runtimeJointRelationGeneratorValue observation nontrivial
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current +
          (stage + 1), .phase)) ∧
      (nativeNextJointCompletionMap depth
        ((nativeNextJointHistory (depth + 1)).completionProjection
          (rawJointPhaseGenerator
            (CanonicalUnitArithmeticRoot.emitted
              (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
            stage)) =
      rawJointShiftOnCompletion
        (CanonicalUnitArithmeticRoot.emitted
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
        ((nativeNextJointHistory depth).completionProjection
          (rawJointPhaseGenerator
            (CanonicalUnitArithmeticRoot.emitted
              (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
            stage))) ∧
      (CanonicalUnitArithmeticRoot.nativeWriteAt
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current).target =
          (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current ∧
      HEq step.wholeLedgerWriteBack
        ((runtimeJointFaithfulRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeJointFaithfulVisitAt observation nontrivial depth).current) ∧
      step.nextCurrent.visit.current =
        (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current ∧
      step.nextCurrent =
        (runtimeJointFaithfulRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimeJointFaithfulVisitAt observation nontrivial depth) := by
  have transport := nativeNextJoint_phase_transport_eq_sourceShift depth stage
  have evaluation := nativeNextJoint_transport_originalEvaluator
    observation nontrivial depth stage
  have write := (nativeNextJoint_nativeWrite_receipt depth).1
  rcases runtimeJointFaithfulStep_factorizes
      observation nontrivial depth with
    ⟨_sourceRoot, _faithfulRoot, ledger, next, _projection⟩
  exact ⟨evaluation, transport, write, ledger, rfl, next⟩

end
end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

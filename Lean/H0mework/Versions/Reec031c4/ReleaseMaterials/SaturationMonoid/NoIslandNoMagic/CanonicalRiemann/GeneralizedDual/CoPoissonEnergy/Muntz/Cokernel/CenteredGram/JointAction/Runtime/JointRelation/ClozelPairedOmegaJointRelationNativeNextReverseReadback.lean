import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationNativeNextReverseResidual
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationNativeNextReadback

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
open CofinalHistoryTransition

noncomputable section

/-- The original native next gives a lawful forward completion transport,
while the previous stage's actual phase atom is an exact reverse generator
residual.  The old evaluator and original row/next read the same two visits;
the residual is not claimed as a paid old disposition. -/
theorem nativeNextJoint_reverseResidual_originalRoot_consumer
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    ∃ residual : CofinalHistoryTransition.GeneratorResidual
        (nativeNextJointHistory depth)
        (nativeNextJointHistory (depth + 1)),
      CofinalHistoryTransition.settle
          (nativeNextJointHistory depth)
          (nativeNextJointHistory (depth + 1)) =
        .generatorResidual residual ∧
      (nativeNextJoint_reverseGeneratorResidual depth).coordinate =
        runtimeJointRelationAtom depth .phase ∧
      nativeNextJointCompletionMap depth
          ((nativeNextJointHistory (depth + 1)).completionProjection
            (rawJointPhaseGenerator
              (CanonicalUnitArithmeticRoot.emitted
                (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
              0)) =
        rawJointShiftOnCompletion
          (CanonicalUnitArithmeticRoot.emitted
            (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
          ((nativeNextJointHistory depth).completionProjection
            (rawJointPhaseGenerator
              (CanonicalUnitArithmeticRoot.emitted
                (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
              0)) ∧
      step.faithful.completionEvaluation
          (runtimeJointFaithfulSoundnessAt observation nontrivial depth)
          (nativeNextJointCompletionMap depth
            ((nativeNextJointHistory (depth + 1)).completionProjection
              (rawJointPhaseGenerator
                (CanonicalUnitArithmeticRoot.emitted
                  (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
                0))) =
        runtimeJointRelationGeneratorValue observation nontrivial
          (currentEffectStage
            (CanonicalUnitArithmeticRoot.finiteVisit depth).current + 1,
            .phase) ∧
      (CanonicalUnitArithmeticRoot.nativeWriteAt
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current).target =
          (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current ∧
      (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current ≠
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current ∧
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
  obtain ⟨residual, classified⟩ :=
    nativeNextJoint_reverse_settle_generatorResidual depth
  rcases nativeNextJoint_transport_originalRoot_consumer
      observation nontrivial depth 0 with
    ⟨evaluated, transported, nativeWrite, ledger, nextVisit, next⟩
  exact ⟨residual, classified, rfl, transported, evaluated, nativeWrite,
    nativeNextJoint_visits_distinct depth, ledger, nextVisit, next⟩

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

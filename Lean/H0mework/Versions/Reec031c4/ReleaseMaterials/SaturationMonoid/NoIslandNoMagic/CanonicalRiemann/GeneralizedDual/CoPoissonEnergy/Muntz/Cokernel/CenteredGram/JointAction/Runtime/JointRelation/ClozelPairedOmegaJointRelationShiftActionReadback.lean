import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationShiftAction
import H0mework.Versions.Y.Arithmetic.SonineSource.PairedOmegaJointRelationDisposition

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

noncomputable section

/-- The old faithful evaluator consumes the actual shifted formal occurrence:
the next phase is read from the source action, not supplied as a commuting
target value. -/
theorem rawJointShift_phase_originalEvaluator
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    let occurrence := CanonicalUnitArithmeticRoot.emitted
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current
    let history := runtimeJointRawHistoryAt occurrence
    (runtimeJointFaithfulStepAt observation nontrivial depth).faithful.completionEvaluation
        (runtimeJointFaithfulSoundnessAt observation nontrivial depth)
        (rawJointShiftOnCompletion occurrence
          (history.completionProjection
            (rawJointPhaseGenerator occurrence stage))) =
      runtimeJointRelationGeneratorValue observation nontrivial
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current +
          (stage + 1), .phase) := by
  dsimp only
  have shiftReadback := rawJointShift_phase_completion
    (CanonicalUnitArithmeticRoot.emitted
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current) stage
  rw [shiftReadback]
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointRelationAtom
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current +
          (stage + 1)) .phase) = _
  simp [runtimeJointRelationEvaluator, runtimeJointRelationAtom]

/-- The source-generated action equation is consumed at the very old joint
step that owns the whole-ledger write-back and canonical next.  This states
co-occurrence; it does not make the shift a paid old ledger disposition. -/
theorem rawJointShift_originalRoot_consumer
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    let occurrence := CanonicalUnitArithmeticRoot.emitted
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current
    let history := runtimeJointRawHistoryAt occurrence
    (step.faithful.completionEvaluation
        (runtimeJointFaithfulSoundnessAt observation nontrivial depth)
        (rawJointShiftOnCompletion occurrence
          (history.completionProjection
            (rawJointPhaseGenerator occurrence stage))) =
      runtimeJointRelationGeneratorValue observation nontrivial
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current +
          (stage + 1), .phase)) ∧
      step.history.root.root = step.sourceOccurrence ∧
      HEq step.wholeLedgerWriteBack
        ((runtimeJointFaithfulRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeJointFaithfulVisitAt observation nontrivial depth).current) ∧
      step.nextCurrent =
        (runtimeJointFaithfulRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimeJointFaithfulVisitAt observation nontrivial depth) := by
  have action := rawJointShift_phase_originalEvaluator
    observation nontrivial depth stage
  rcases runtimeJointFaithfulStep_factorizes
      observation nontrivial depth with
    ⟨sourceRoot, _faithfulRoot, ledger, next, _projection⟩
  exact ⟨action, sourceRoot, ledger, next⟩

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

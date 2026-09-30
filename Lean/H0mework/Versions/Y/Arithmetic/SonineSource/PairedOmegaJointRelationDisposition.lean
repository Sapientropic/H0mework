import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaJointRelationCoverage
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.ClozelPairedOmegaJointRelationRuntimeReadback

/-!
# Full joint mapping disposition and detector consumer

The previous effect, detector history and detector evaluator remain installed
after adjoining the full joint face.  The balance branch of every generated
joint observation is literally the old detector relation, and the balance
projection of the full evaluator is the old detector evaluator.

Whole-closure soundness removes the generic unsound branch.  The remaining
outcome is exactly a faithful full-joint quotient or an explicit kernel or
coverage coordinate; no branch is claimed to vanish here.
-/

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

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalFaithfulSettlementFace
open CofinalFaithfulSettlementFace.RootGeneratedCofinalFaithfulSettlementStepAt
open CofinalHistorySettlement

noncomputable section

def runtimeEffectFaithfulInstallationAtJointRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeJointFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectFaithfulInstallation observation nontrivial).trans
    (runtimeJointFaithfulInheritedInstallation observation nontrivial)

def runtimeEffectHistoryInstallationAtJointRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectRelationMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeJointFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectHistoryInstallationAtFaithfulRoot observation nontrivial).trans
    (runtimeJointFaithfulInheritedInstallation observation nontrivial)

def runtimeEffectInstallationAtJointRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectLaw observation nontrivial).toProjectionLaw
      (runtimeJointFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectInstallationAtFaithfulRoot observation nontrivial).trans
    (runtimeJointFaithfulInheritedInstallation observation nontrivial)

theorem runtimeJointFaithfulStep_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    step.history.root.root = step.sourceOccurrence ∧
      step.faithful.root = step.history.root ∧
      HEq step.wholeLedgerWriteBack
        ((runtimeJointFaithfulRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeJointFaithfulVisitAt observation nontrivial depth).current) ∧
      step.nextCurrent =
        (runtimeJointFaithfulRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimeJointFaithfulVisitAt observation nontrivial depth) ∧
      HEq
        ((runtimeJointFaithfulRoot observation nontrivial
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            ((runtimeJointFaithfulRecognition observation nontrivial
              ).installation.embed PUnit.unit)
            step.sourceOccurrence)
        ((runtimeJointFaithfulRecognition observation nontrivial
          ).materialLaw.toProjectionLaw.outcomeAt
            PUnit.unit step.sourceOccurrence) := by
  exact ⟨(runtimeJointFaithfulStepAt observation nontrivial depth
      ).history_root_payload_eq_sourceOccurrence,
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful_root_eq_history_root,
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).wholeLedgerWriteBack_eq_root,
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).nextCurrent_eq_root,
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).installedFaithful_factorizes⟩

/-- The previous detector presentation is a literal generated branch of the
full history, not a second occurrence compared afterward. -/
theorem runtimeJointFaithful_detectorRelation_exposed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeEffectRelationToJointRelation
        (runtimeEffectStageRelation (depth + stage)) =
        runtimeJointBalanceStageRelation (depth + stage) ∧
      PresentedRelationEventAt.relation
          (runtimeJointBalanceStageRelation (depth + stage)) ∈
        ((runtimeJointFaithfulStepAt observation nontrivial depth
          ).history.observation stage).trace := by
  refine ⟨runtimeEffectRelationToJointRelation_stage (depth + stage), ?_⟩
  apply RootedAccountedUnfolding.frontier_mem_trace
  have frontierEq := runtimeJointFaithfulObservation_frontier
    observation nontrivial depth stage
  have listMem :
      PresentedRelationEventAt.relation
          (runtimeJointBalanceStageRelation (depth + stage)) ∈
        [runtimeJointBalancePresentedEvent (depth + stage)] := by
    simp [runtimeJointBalancePresentedEvent]
  exact frontierEq.symm ▸ listMem

/-- Evaluator-level commuting square for the same detector branch. -/
theorem runtimeJointFaithful_detectorEvaluator_projection
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeJointBalanceFace.comp
        (runtimeJointFaithfulStepAt observation nontrivial depth
          ).faithful.freeEvaluation).comp
          runtimeEffectRelationToJointRelation =
      runtimeEffectRelationEvaluator observation nontrivial := by
  change
    (runtimeJointBalanceFace.comp
      (runtimeJointRelationEvaluator observation nontrivial)).comp
        runtimeEffectRelationToJointRelation = _
  exact runtimeJointRelationEvaluator_extends_detector
    observation nontrivial

/-- The old detector consumes the single-generator equation made by the
evaluator value in the new fixed root's raw joint source projection. -/
theorem runtimeJointFaithful_sourceDetector_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) (generator : RuntimeEffectRelationGenerator)
    (coefficient : ℤ) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    runtimeJointBalanceFace
        (step.faithful.freeEvaluation
          (Finsupp.single
            (runtimeEffectGeneratorToJointGenerator generator) coefficient)) =
      runtimeEffectRelationEvaluator observation nontrivial
        (Finsupp.single generator coefficient) ∧
    step.faithful.freeEvaluation
        (Finsupp.single
          (runtimeEffectGeneratorToJointGenerator generator) coefficient) =
      coefficient •
        (((runtimeJointFaithfulRecognition observation nontrivial).materialLaw
          ).toProjectionLaw.project PUnit.unit step.sourceOccurrence PUnit.unit
          ).evaluator.root
            (runtimeEffectGeneratorToJointGenerator generator) := by
  dsimp
  constructor
  · have detector := congrArg
      (fun relationMap => relationMap (Finsupp.single generator coefficient))
      (runtimeJointFaithful_detectorEvaluator_projection
        observation nontrivial depth)
    have mappedSingle :
        runtimeEffectRelationToJointRelation
            (Finsupp.single generator coefficient) =
          Finsupp.single
            (runtimeEffectGeneratorToJointGenerator generator) coefficient := by
      rcases generator with ⟨stage, role⟩
      cases role <;> simp [runtimeEffectRelationToJointRelation,
        runtimeEffectGeneratorToJointGenerator]
    change runtimeJointBalanceFace
        ((runtimeJointFaithfulStepAt observation nontrivial depth
          ).faithful.freeEvaluation
            (runtimeEffectRelationToJointRelation
              (Finsupp.single generator coefficient))) = _ at detector
    rw [mappedSingle] at detector
    exact detector
  · exact (runtimeJointFaithfulStepAt observation nontrivial depth
      ).sourceFreeEvaluation_single
        (runtimeEffectGeneratorToJointGenerator generator) coefficient

theorem runtimeJointFaithfulSoundnessAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    GeneratedRelationSoundnessAt
      (runtimeJointFaithfulStepAt observation nontrivial depth).faithful := by
  let face :=
    (runtimeJointFaithfulStepAt observation nontrivial depth).faithful
  cases h : face.settleRelations with
  | sound soundness => exact soundness
  | unsound obstruction =>
      exact False.elim
        (obstruction.notSound
          (runtimeJointFaithful_relationsSound
            observation nontrivial depth))

/-- Soundness deletes the generic unsound branch. -/
theorem runtimeJointFaithful_soundResidualDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeJointFaithfulStepAt observation nontrivial depth
    (∃ (soundness : GeneratedRelationSoundnessAt step.faithful)
        (coverage : GeneratedCoverageResidualZeroAt step.faithful soundness)
        (realization : GeneratedFaithfulRealizationAt
          step.faithful soundness coverage),
      step.residualDisposition =
        .faithful soundness coverage realization) ∨
    (∃ (soundness : GeneratedRelationSoundnessAt step.faithful)
        (obstruction : GeneratedCoverageResidualObstructionAt
          step.faithful soundness)
        (coordinate : GeneratedKernelResidualCoordinateAt
          step.faithful soundness),
      step.residualDisposition =
        .kernelResidual soundness obstruction coordinate) ∨
    (∃ (soundness : GeneratedRelationSoundnessAt step.faithful)
        (obstruction : GeneratedCoverageResidualObstructionAt
          step.faithful soundness)
        (coordinate : GeneratedCoverageResidualCoordinateAt
          step.faithful soundness),
      step.residualDisposition =
        .coverageResidual soundness obstruction coordinate) := by
  let step := runtimeJointFaithfulStepAt observation nontrivial depth
  have sourceEq := runtimeJointFaithfulStep_residual_eq_raw
    observation nontrivial depth
  cases h : runtimeJointRawResidualAt observation nontrivial
      (CanonicalUnitArithmeticRoot.emitted
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current) with
  | faithful soundness coverage realization =>
      exact Or.inl ⟨soundness, coverage, realization, sourceEq.trans h⟩
  | unsound obstruction coordinate =>
      exact False.elim
        (obstruction.notSound
          (runtimeJointFaithful_relationsSound
            observation nontrivial depth))
  | kernelResidual soundness obstruction coordinate =>
      exact Or.inr (Or.inl ⟨soundness, obstruction, coordinate,
        sourceEq.trans h⟩)
  | coverageResidual soundness obstruction coordinate =>
      exact Or.inr (Or.inr ⟨soundness, obstruction, coordinate,
        sourceEq.trans h⟩)

#print axioms runtimeJointFaithful_sourceDetector_single

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

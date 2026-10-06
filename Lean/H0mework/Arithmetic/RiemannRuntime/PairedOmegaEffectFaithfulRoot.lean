import H0mework.Foundation.Source.TraceAdvance
import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Arithmetic.RiemannRuntime.PairedOmegaEffectFaithfulMaterial

/-!
# Same-root faithful settlement of the paired-Omega detector history

The history/evaluator pair is adjoined before emission to the existing
effect-relation authority source.  The inherited formal-history and effect
coordinates remain installed.  Relation soundness is proved for the whole
generated closure, so the generic residual disposition cannot take its
unsound branch; it must return a faithful quotient, a kernel coordinate or a
coverage coordinate.
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

open CanonicalUnitArithmeticRoot
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistorySettlementFace
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalFaithfulSettlementFace
open CofinalFaithfulSettlementFace.RootGeneratedCofinalFaithfulSettlementStepAt

noncomputable section

def runtimeEffectFaithfulAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeEffectRelationAuthoritySource observation nontrivial
    ).withProjectionCoface
      (runtimeEffectFaithfulMaterialLaw observation nontrivial).toProjectionLaw

def runtimeEffectFaithfulLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeEffectFaithfulAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeEffectFaithfulAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimeEffectFaithfulRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeEffectFaithfulLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeEffectFaithfulRoot_reuses_lower_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeEffectFaithfulRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeEffectFaithfulRoot observation nontrivial).emitted = emitted := by
  exact ⟨rfl, rfl⟩

def runtimeEffectFaithfulInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectFaithfulMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeEffectRelationAuthoritySource observation nontrivial)
    (runtimeEffectFaithfulMaterialLaw observation nontrivial).toProjectionLaw

def runtimeEffectFaithfulInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectRelationAuthoritySource observation nontrivial).projectionLaw
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeEffectRelationAuthoritySource observation nontrivial)
    (runtimeEffectFaithfulMaterialLaw observation nontrivial).toProjectionLaw

def runtimeEffectHistoryInstallationAtFaithfulRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectRelationMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectRelationInstallation observation nontrivial).trans
    (runtimeEffectFaithfulInheritedInstallation observation nontrivial)

def runtimeEffectInstallationAtFaithfulRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectLaw observation nontrivial).toProjectionLaw
      (runtimeEffectFaithfulAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectInstallationAtRelationRoot observation nontrivial).trans
    (runtimeEffectFaithfulInheritedInstallation observation nontrivial)

abbrev runtimeEffectFaithfulRecognition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalFaithfulRecognitionAt QRich.ClozelJPair
      (runtimeEffectFaithfulRoot observation nontrivial) :=
  SourceNativeCofinalFaithfulRecognitionAt.create
    (runtimeEffectFaithfulMaterialLaw observation nontrivial)
    (runtimeEffectFaithfulInstallation observation nontrivial)

def runtimeEffectFaithfulVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeEffectFaithfulRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

abbrev runtimeEffectFaithfulStepAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    RootGeneratedCofinalFaithfulSettlementStepAt
      (runtimeEffectFaithfulRecognition observation nontrivial)
      (runtimeEffectFaithfulVisitAt observation nontrivial depth) :=
  (runtimeEffectFaithfulRecognition observation nontrivial).generateStepAt
    (runtimeEffectFaithfulVisitAt observation nontrivial depth)

theorem runtimeEffectFaithfulStep_history_eq_relationStep_history
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectFaithfulStepAt observation nontrivial depth).history =
      (runtimeEffectRelationStepAt observation nontrivial depth).history :=
  rfl

def IsRuntimeEffectStageRelation
    (relation : RuntimeEffectRelationGenerator →₀ ℤ) : Prop :=
  ∃ stage, relation = runtimeEffectStageRelation stage

private theorem runtimeEffectObservation_relation_generated
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat)
    (relation : RuntimeEffectRelationGenerator →₀ ℤ)
    (membership : PresentedRelationEventAt.relation relation ∈
      ((runtimeEffectRelationStepAt observation nontrivial depth
        ).history.observation stage).trace) :
    IsRuntimeEffectStageRelation relation := by
  induction stage with
  | zero =>
      change PresentedRelationEventAt.relation relation ∈
        (runtimeEffectRelationSeedAt
          (currentEffectStage
            (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).trace
        at membership
      rw [currentEffectStage_finiteVisit] at membership
      change PresentedRelationEventAt.relation relation ∈
        [runtimeEffectPresentedRelationEvent depth] at membership
      simp only [List.mem_singleton] at membership
      exact ⟨depth, PresentedRelationEventAt.relation.inj membership⟩
  | succ stage inductionHypothesis =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ] at membership
      cases RootedAccountedUnfolding.trace_advance_cases
          (runtimeEffectRelationStepAt observation nontrivial depth
            ).history.actualContinuation
          ((runtimeEffectRelationStepAt observation nontrivial depth
            ).history.observation stage) _ membership with
      | inl old => exact inductionHypothesis old
      | inr generated =>
          obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
          rw [runtimeEffectRelationObservation_frontier] at leaf_mem
          have leaf_eq : leaf =
              runtimeEffectPresentedRelationEvent (depth + stage) := by
            exact List.mem_singleton.mp leaf_mem
          subst leaf
          change PresentedRelationEventAt.relation relation ∈
            (RootedAccountedUnfolding.zero
              (runtimeEffectShiftPresentedEvent
                (runtimeEffectPresentedRelationEvent (depth + stage)))).trace
            at generated_mem
          rw [runtimeEffectShiftPresentedEvent_stage] at generated_mem
          change PresentedRelationEventAt.relation relation ∈
            [runtimeEffectPresentedRelationEvent (depth + stage + 1)]
            at generated_mem
          simp only [List.mem_singleton] at generated_mem
          exact ⟨depth + stage + 1,
            PresentedRelationEventAt.relation.inj generated_mem⟩

theorem runtimeEffectObserved_relation_generated
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth historyStage : Nat)
    (relation : RuntimeEffectRelationGenerator →₀ ℤ)
    (membership : PresentedRelationEventAt.relation relation ∈
      (runtimeEffectRelationStepAt observation nontrivial depth
        ).history.observedEvents historyStage) :
    IsRuntimeEffectStageRelation relation := by
  unfold RootGeneratedCofinalHistoryAt.observedEvents at membership
  obtain ⟨stage, _stage_mem, relation_mem⟩ :=
    List.mem_flatMap.mp membership
  exact runtimeEffectObservation_relation_generated
    observation nontrivial depth stage relation relation_mem

theorem runtimeEffectFaithful_freeEvaluation_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation =
        runtimeEffectRelationEvaluator observation nontrivial :=
  rfl

theorem runtimeEffectFaithful_freeEvaluation_stageRelation_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation (runtimeEffectStageRelation stage) = 0 := by
  rw [runtimeEffectFaithful_freeEvaluation_eq
    observation nontrivial depth]
  exact runtimeEffectStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeEffectFaithful_relationsSound
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).faithful.RelationsSound := by
  apply iSup_le
  intro historyStage
  apply Submodule.span_le.mpr
  intro relation relationEvent
  have relationEvent' : PresentedRelationEventAt.relation relation ∈
      (runtimeEffectRelationStepAt observation nontrivial depth
        ).history.observedEvents historyStage := by
    rw [← runtimeEffectFaithfulStep_history_eq_relationStep_history]
    exact relationEvent
  obtain ⟨stage, rfl⟩ := runtimeEffectObserved_relation_generated
    observation nontrivial depth historyStage relation relationEvent'
  exact runtimeEffectFaithful_freeEvaluation_stageRelation_zero
    observation nontrivial depth stage

theorem runtimeEffectFaithfulSoundnessAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    GeneratedRelationSoundnessAt
      (runtimeEffectFaithfulStepAt observation nontrivial depth).faithful := by
  let face :=
    (runtimeEffectFaithfulStepAt observation nontrivial depth).faithful
  cases h : face.settleRelations with
  | sound soundness => exact soundness
  | unsound obstruction =>
      exact False.elim
        (obstruction.notSound
          (runtimeEffectFaithful_relationsSound
            observation nontrivial depth))

theorem runtimeEffectFaithfulStep_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeEffectFaithfulStepAt observation nontrivial depth
    step.history.root.root = step.sourceOccurrence ∧
      step.faithful.root = step.history.root ∧
      HEq step.wholeLedgerWriteBack
        ((runtimeEffectFaithfulRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeEffectFaithfulVisitAt observation nontrivial depth).current) ∧
      step.nextCurrent =
        (runtimeEffectFaithfulRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimeEffectFaithfulVisitAt observation nontrivial depth) ∧
      HEq
        ((runtimeEffectFaithfulRoot observation nontrivial
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            ((runtimeEffectFaithfulRecognition observation nontrivial
              ).installation.embed PUnit.unit)
            step.sourceOccurrence)
        ((runtimeEffectFaithfulRecognition observation nontrivial
          ).materialLaw.toProjectionLaw.outcomeAt
            PUnit.unit step.sourceOccurrence) := by
  exact ⟨(runtimeEffectFaithfulStepAt observation nontrivial depth
      ).history_root_payload_eq_sourceOccurrence,
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).faithful_root_eq_history_root,
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).wholeLedgerWriteBack_eq_root,
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).nextCurrent_eq_root,
    (runtimeEffectFaithfulStepAt observation nontrivial depth
      ).installedFaithful_factorizes⟩

/-- Relation soundness removes the generic unsound branch.  The exact
remaining disposition is faithful, kernel-residual or coverage-residual. -/
theorem runtimeEffectFaithful_soundResidualDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeEffectFaithfulStepAt observation nontrivial depth
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
  let step := runtimeEffectFaithfulStepAt observation nontrivial depth
  cases h : step.residualDisposition with
  | faithful soundness coverage realization =>
      exact Or.inl ⟨soundness, coverage, realization, h⟩
  | unsound obstruction coordinate =>
      exact False.elim
        (obstruction.notSound
          (runtimeEffectFaithful_relationsSound
            observation nontrivial depth))
  | kernelResidual soundness obstruction coordinate =>
      exact Or.inr (Or.inl ⟨soundness, obstruction, coordinate, h⟩)
  | coverageResidual soundness obstruction coordinate =>
      exact Or.inr (Or.inr ⟨soundness, obstruction, coordinate, h⟩)

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

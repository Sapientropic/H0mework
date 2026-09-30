import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaEffectRelationOccurrence

/-!
# Same-root installation of the paired-Omega effect relation history

The formal relation history is adjoined as one pre-emitter projection coface
of the already installed effect authority source.  The effect projection is
inherited compositionally.  At every canonical finite visit, one zero-field
settlement step reads the relation history, whole ledger and generated next
from the same compiler image.

This is a formal cofinal dependent face at a finite root visit.  It is not an
authority-bearing cofinal visit or a convergence theorem.
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
open CofinalHistorySettlementFace.RootGeneratedCofinalHistorySettlementStepAt
open CofinalHistoryResidualCoordinate

noncomputable section

def runtimeEffectRelationAuthoritySource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeAuthoritySource N V :=
  (runtimeEffectAuthoritySource observation nontrivial).withProjectionCoface
    (runtimeEffectRelationMaterialLaw observation nontrivial).toProjectionLaw

def runtimeEffectRelationLivingSource
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingAuthoritySource N V where
  base := runtimeEffectRelationAuthoritySource observation nontrivial
  terminalHandoff :=
    (runtimeEffectRelationAuthoritySource observation nontrivial
      ).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

def runtimeEffectRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootClosure N V where
  source := runtimeEffectRelationLivingSource observation nontrivial
  emitted := emitted
  compiler_commutes := authoritativeRoot.compiler_commutes

theorem runtimeEffectRelationRoot_reuses_lower_source_emitter
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeEffectRelationRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot.source = ledgerSource ∧
      (runtimeEffectRelationRoot observation nontrivial).emitted = emitted := by
  exact ⟨rfl, rfl⟩

def runtimeEffectRelationInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectRelationMaterialLaw observation nontrivial).toProjectionLaw
      (runtimeEffectRelationAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (runtimeEffectAuthoritySource observation nontrivial)
    (runtimeEffectRelationMaterialLaw observation nontrivial).toProjectionLaw

def runtimeEffectInheritedInstallation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectAuthoritySource observation nontrivial).projectionLaw
      (runtimeEffectRelationAuthoritySource observation nontrivial
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (runtimeEffectAuthoritySource observation nontrivial)
    (runtimeEffectRelationMaterialLaw observation nontrivial).toProjectionLaw

/-- The original recursive-effect component remains installed after adjoining
the relation-history face. -/
def runtimeEffectInstallationAtRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw.InstallationAt
      (runtimeEffectLaw observation nontrivial).toProjectionLaw
      (runtimeEffectRelationAuthoritySource observation nontrivial
        ).projectionLaw :=
  (runtimeEffectRecognition observation nontrivial).installation.trans
    (runtimeEffectInheritedInstallation observation nontrivial)

def runtimeEffectRecognitionAtRelationRoot
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeEffectDynamicalRecognitionAt
      (runtimeEffectRelationRoot observation nontrivial) where
  effectLaw := runtimeEffectLaw observation nontrivial
  installation := runtimeEffectInstallationAtRelationRoot
    observation nontrivial

theorem runtimeEffectRelationRoot_effectOutcome_heq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    HEq
      ((runtimeEffectRelationRoot observation nontrivial
        ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
          ((runtimeEffectInstallationAtRelationRoot observation nontrivial
            ).embed PUnit.unit) occurrence)
      ((runtimeEffectLaw observation nontrivial).toProjectionLaw.outcomeAt
        PUnit.unit occurrence) :=
  (runtimeEffectInstallationAtRelationRoot observation nontrivial
    ).outcome_heq occurrence PUnit.unit

abbrev runtimeEffectRelationRecognition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeCofinalHistoryRecognitionAt
      (runtimeEffectRelationRoot observation nontrivial) where
  materialLaw := runtimeEffectRelationMaterialLaw observation nontrivial
  installation := runtimeEffectRelationInstallation observation nontrivial

def runtimeEffectRelationVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeEffectRelationRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

def runtimeEffectRelationStepAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    RootGeneratedCofinalHistorySettlementStepAt
      (runtimeEffectRelationRecognition observation nontrivial)
      (runtimeEffectRelationVisitAt observation nontrivial depth) :=
  (runtimeEffectRelationRecognition observation nontrivial).generateStepAt
    (runtimeEffectRelationVisitAt observation nontrivial depth)

@[simp] theorem runtimeEffectRelationStepAt_seed_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectRelationStepAt observation nontrivial depth
      ).history.seed.root = runtimeEffectPresentedRelationEvent depth := by
  change runtimeEffectPresentedRelationEvent
      (currentEffectStage
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current) = _
  rw [currentEffectStage_finiteVisit]

@[simp] theorem runtimeEffectRelationStepAt_continuation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat)
    (event : PresentedRelationEventAt RuntimeEffectRelationGenerator) :
    (runtimeEffectRelationStepAt observation nontrivial depth
      ).history.actualContinuation event =
        RootedAccountedUnfolding.zero
          (runtimeEffectShiftPresentedEvent event) :=
  rfl

theorem runtimeEffectRelationObservation_frontier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    ((runtimeEffectRelationStepAt observation nontrivial depth
      ).history.observation stage).frontier =
        [runtimeEffectPresentedRelationEvent (depth + stage)] := by
  induction stage with
  | zero =>
      change [runtimeEffectPresentedRelationEvent
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current)] = _
      rw [currentEffectStage_finiteVisit]
      simp
  | succ stage inductionHypothesis =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ,
        RootedAccountedUnfolding.frontier_advance,
        inductionHypothesis]
      change
        (RootedAccountedUnfolding.zero
          (runtimeEffectShiftPresentedEvent
            (runtimeEffectPresentedRelationEvent (depth + stage)))).frontier = _
      rw [runtimeEffectShiftPresentedEvent_stage]
      congr 2

/-- Every formal history relation is killed by the actual installed effect
evaluator at the matching compiler stage. -/
theorem runtimeEffectRelationObservation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeEffectRelationEvaluator observation nontrivial
        (runtimeEffectStageRelation (depth + stage)) = 0 :=
  runtimeEffectStageRelation_evaluates_zero
    observation nontrivial (depth + stage)

theorem runtimeEffectRelationStep_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeEffectRelationStepAt observation nontrivial depth
    step.history.root.root = step.sourceOccurrence ∧
      HEq step.wholeLedgerWriteBack
        ((runtimeEffectRelationRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeEffectRelationVisitAt observation nontrivial depth).current) ∧
      step.nextCurrent =
        (runtimeEffectRelationRoot observation nontrivial
          ).generatedNextCurrentAt
            (runtimeEffectRelationVisitAt observation nontrivial depth) ∧
      HEq
        ((runtimeEffectRelationRoot observation nontrivial
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            ((runtimeEffectRelationRecognition observation nontrivial
              ).installation.embed PUnit.unit)
            step.sourceOccurrence)
        ((runtimeEffectRelationRecognition observation nontrivial
          ).materialLaw.toProjectionLaw.outcomeAt
            PUnit.unit step.sourceOccurrence) := by
  exact ⟨(runtimeEffectRelationStepAt observation nontrivial depth
      ).history_root_payload_eq_sourceOccurrence,
    (runtimeEffectRelationStepAt observation nontrivial depth
      ).wholeLedgerWriteBack_eq_root,
    (runtimeEffectRelationStepAt observation nontrivial depth
      ).nextCurrent_eq_root,
    (runtimeEffectRelationStepAt observation nontrivial depth
      ).installedHistory_factorizes⟩

/-- Direct generic consumer: the installed actual relation history is settled
into the compact/perfect branch or an explicit persistent coordinate. -/
theorem runtimeEffectRelation_totalDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let step := runtimeEffectRelationStepAt observation nontrivial depth
    (∃ trace : GeneratedHistoricalCompactnessAt step.history,
      ∃ readout : GeneratedCompactPerfectReadoutAt step.history trace,
        step.totalDisposition = .inl ⟨trace, readout⟩) ∨
    (∃ coordinate : GeneratedPresentedResidualCoordinateAt step.history,
      step.totalDisposition = .inr coordinate ∧
        coordinate.coordinate ≠ 0 ∧
        coordinate.representative ∉
          LinearMap.range
            (step.history.stagePresentedToCompletion coordinate.stage)) :=
  (runtimeEffectRelationStepAt observation nontrivial depth
    ).totalDisposition_positive_or_residual

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

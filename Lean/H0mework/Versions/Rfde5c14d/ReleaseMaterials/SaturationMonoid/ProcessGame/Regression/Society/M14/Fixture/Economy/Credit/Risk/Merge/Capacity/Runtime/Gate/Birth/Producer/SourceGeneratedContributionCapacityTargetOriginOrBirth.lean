import H0mework.Foundation.Ledger.OriginOrBirth
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Action.SourceGeneratedContributionCapacityU8TargetState
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Gate.Producer.SourceGeneratedContributionCapacityJointSettlementGateFrontier

/-!
# Contribution-capacity target origin or birth

Ordinary joint-settlement ingress has only old target origins.  The non-
conservative capacity-U8 representation change supplies the positive birth
case: relative to the embedded pre-revision old target face, its generated
residual is a fresh debt and arrives with its compiler row, initial causal
authority, lifecycle obligation, existing parent bearer and root consumer.

The producer accepts no target entry, birth verdict, coverage list, bearer,
consumer or future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityTargetOriginOrBirth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementGateFrontier

/-! ## Ordinary joint-settlement targets are all old-origin -/

def contributionCapacityJointSettlementA13TargetDebtOriginAt
    (oldVisit : OldVisit)
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) :
    ExactTargetDebtOriginAt
      (contributionCapacityJointSettlementLiveLedger oldVisit) targetEntry :=
  let ingress := contributionCapacityJointSettlementIngressPresentation oldVisit
  ⟨ingress.forward (ingress.backward targetEntry),
    ⟨rfl, congrArg OpenResponsibilityAt.claim
      (ingress.forward_backward targetEntry)⟩⟩

theorem contributionCapacityJointSettlementTargetFresh_isEmpty
    (oldVisit : OldVisit)
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) :
    IsEmpty
      (RootDebtFreshAt (JointSettlementNAt oldVisit)
        (contributionCapacityJointSettlementLiveLedger oldVisit).support
        targetEntry) :=
  ⟨fun fresh => PEmpty.elim
    ((contributionCapacityJointSettlementA13TargetDebtOriginAt oldVisit
      targetEntry).excludesFresh fresh)⟩

/-! ## Pre-revision old face inside the revised network -/

def contributionCapacityU8EmbeddedOldTargetSupport
    (oldVisit : OldVisit) : (CapacityU8NAt oldVisit).Support :=
  (CapacityCofaceAt oldVisit).translation.support.forward
    (contributionCapacityCutTargetSupport
      (capacityActionRootedAt oldVisit))

def contributionCapacityU8PreRevisionLedger
    (oldVisit : OldVisit) : CompleteLiveLedgerAt (CapacityU8NAt oldVisit) :=
  ⟨contributionCapacityU8EmbeddedOldTargetSupport oldVisit⟩

def contributionCapacityU8EmbeddedOldEntry
    (oldVisit : OldVisit)
    (oldEntry : OpenResponsibilityAt
      (CutN (capacityActionRootedAt oldVisit))
      (contributionCapacityCutTargetSupport
        (capacityActionRootedAt oldVisit))) :
    (contributionCapacityU8PreRevisionLedger oldVisit).Entry :=
  (CapacityCofaceAt oldVisit).oldFaceOpenLedgerPresentation
      (contributionCapacityCutTargetSupport
        (capacityActionRootedAt oldVisit))
    |>.forward oldEntry

def contributionCapacityU8InheritedContributionOrigin
    (oldVisit : OldVisit) :
    ExactTargetDebtOriginAt (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8InheritedContribution oldVisit) :=
  ⟨contributionCapacityU8EmbeddedOldEntry oldVisit
      (contributionCapacityCutTargetContribution
        (capacityActionRootedAt oldVisit)),
    ⟨rfl, rfl⟩⟩

def contributionCapacityU8InheritedObstructionOrigin
    (oldVisit : OldVisit) :
    ExactTargetDebtOriginAt (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8InheritedObstruction oldVisit) :=
  ⟨contributionCapacityU8EmbeddedOldEntry oldVisit
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit)),
    ⟨rfl, rfl⟩⟩

def contributionCapacityU8GeneratedResidualFresh
    (oldVisit : OldVisit) :
    RootDebtFreshAt (CapacityU8NAt oldVisit)
      (contributionCapacityU8PreRevisionLedger oldVisit).support
      (contributionCapacityU8GeneratedResidual oldVisit) where
  noPrior := by
    rintro ⟨responsibility, isOpen⟩ sameDebt
    cases responsibility with
    | inl oldResponsibility =>
        change (CutN (capacityActionRootedAt oldVisit)).OpenAt
          (contributionCapacityCutTargetSupport
            (capacityActionRootedAt oldVisit)) oldResponsibility at isOpen
        exact False.elim
          ((CapacityCofaceAt oldVisit).obstructionClaim_hasNoOldPreimage.false
            ⟨(CutN (capacityActionRootedAt oldVisit)).openClaimAt isOpen,
              PLift.up sameDebt.claim_eq⟩)
    | inr direction => exact PEmpty.elim isOpen

def ContributionCapacityU8TargetProvenanceAt
    (oldVisit : OldVisit) : Fin 3 → Type :=
  Fin.cases
    (ExactTargetDebtOriginAt (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8InheritedContribution oldVisit))
    (fun tail => Fin.cases
      (ExactTargetDebtOriginAt
        (contributionCapacityU8PreRevisionLedger oldVisit)
        (contributionCapacityU8InheritedObstruction oldVisit))
      (fun _ => RootDebtFreshAt (CapacityU8NAt oldVisit)
        (contributionCapacityU8PreRevisionLedger oldVisit).support
        (contributionCapacityU8GeneratedResidual oldVisit)) tail)

def contributionCapacityU8TargetProvenanceAt
    (oldVisit : OldVisit) :
    (entryIndex : Fin 3) →
      ContributionCapacityU8TargetProvenanceAt oldVisit entryIndex :=
  Fin.cases (contributionCapacityU8InheritedContributionOrigin oldVisit)
    (fun tail => Fin.cases
      (contributionCapacityU8InheritedObstructionOrigin oldVisit)
      (fun _ => contributionCapacityU8GeneratedResidualFresh oldVisit) tail)

/-- Every actual target entry is recovered by the complete Fin-3
presentation before its source-generated provenance is read. -/
def contributionCapacityU8AnyTargetProvenanceAt
    (oldVisit : OldVisit)
    (targetEntry : (contributionCapacityU8Ledger oldVisit).Entry) :
    Sigma fun entryIndex : Fin 3 =>
      PLift (contributionCapacityU8EntryAt oldVisit entryIndex = targetEntry) ×
        ContributionCapacityU8TargetProvenanceAt oldVisit entryIndex :=
  ⟨contributionCapacityU8EntryIndex oldVisit targetEntry,
    PLift.up (contributionCapacityU8EntryAt_index oldVisit targetEntry),
    contributionCapacityU8TargetProvenanceAt oldVisit
      (contributionCapacityU8EntryIndex oldVisit targetEntry)⟩

def contributionCapacityU8InitialAnswerFaceAt
    (oldVisit : OldVisit) :
    SourceNativeRootSemanticFaceAt (CapacityU8RootAt oldVisit)
      (contributionCapacityU8TemporalVisitAt oldVisit 0) where
  projection := ContributionCapacityU8Projection.answer
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacityU8InitialResidualConsumer
    (oldVisit : OldVisit) :
    SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (contributionCapacityU8InitialGenerated oldVisit).occurrence)
      (contributionCapacityU8GeneratedResidual oldVisit)
      (contributionCapacityU8InitialAnswerFaceAt oldVisit) where
  projection := ContributionCapacityU8Projection.consumer 2
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

/-- Full birth admission indexed by one exact U8 target entry.  Its private
constructor prevents a bare no-preimage proof or caller-selected target from
minting birth.  This open dependent family replaces, rather than duplicates,
the residual-specialized mouth; it is not a target registry. -/
structure ExactContributionCapacityTargetBirthAdmissionAt
    (oldVisit : OldVisit)
    (targetEntry : (contributionCapacityU8Ledger oldVisit).Entry) : Type 12 where
  private mk ::
  freshDebt : RootDebtFreshAt (CapacityU8NAt oldVisit)
    (contributionCapacityU8PreRevisionLedger oldVisit).support
    targetEntry
  noOldPreimage : IsEmpty
    (Sigma fun oldEntry : OpenResponsibilityAt
        (CutN (capacityActionRootedAt oldVisit))
        (contributionCapacityCutTargetSupport
          (capacityActionRootedAt oldVisit)) =>
      PLift
        ((CapacityCofaceAt oldVisit).cofaceLedgerRetract.forward oldEntry =
          targetEntry))
  generatedRow :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      targetEntry
  initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (CapacityU8RootAt oldVisit)
    (contributionCapacityU8TemporalVisitAt oldVisit 0)
    targetEntry
  obligation : AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit)
  obligationExact : obligation = contributionCapacityU8ObligationAt oldVisit
    exactSourceGeneratedLossAllocationMaterialWitness targetEntry
  bearerExisting : obligation.bearer =
    contributionCapacityU8BearerAt oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness targetEntry
  consumer : SourceNativeInquiryAnswerConsumerAt ()
    (ULift.up.{1, 0}
      (contributionCapacityU8InitialGenerated oldVisit).occurrence)
    targetEntry
    (contributionCapacityU8InitialAnswerFaceAt oldVisit)

/-- Backward-compatible generated-residual specialization. -/
abbrev ExactGeneratedContributionCapacityResidualBirthAdmissionAt
    (oldVisit : OldVisit) :=
  ExactContributionCapacityTargetBirthAdmissionAt oldVisit
    (contributionCapacityU8GeneratedResidual oldVisit)

def sourceGeneratedContributionCapacityResidualBirthAdmission
    (oldVisit : OldVisit) :
    ExactGeneratedContributionCapacityResidualBirthAdmissionAt oldVisit where
  freshDebt := contributionCapacityU8GeneratedResidualFresh oldVisit
  noOldPreimage :=
    (generatedContributionCapacityTypedRevisionAt oldVisit
      ).newOnlyEntry_hasNoOldPreimage
  generatedRow := contributionCapacityU8GeneratedResidualRow oldVisit
  initialAuthority := contributionCapacityU8InitialResidualAuthorityAt oldVisit
  obligation := contributionCapacityU8ObligationAt oldVisit
    exactSourceGeneratedLossAllocationMaterialWitness
    (contributionCapacityU8GeneratedResidual oldVisit)
  obligationExact := rfl
  bearerExisting := rfl
  consumer := contributionCapacityU8InitialResidualConsumer oldVisit

theorem contributionCapacityResidualBirth_hasNoCallerTarget : True := by
  let birth := sourceGeneratedContributionCapacityResidualBirthAdmission
  fail_if_success exact birth.target
  fail_if_success exact birth.targetEntry
  fail_if_success exact birth.future
  fail_if_success exact birth.registry
  trivial

end
end M14SourceGeneratedContributionCapacityTargetOriginOrBirth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityTargetOriginOrBirth.contributionCapacityJointSettlementA13TargetDebtOriginAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityTargetOriginOrBirth.contributionCapacityU8TargetProvenanceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityTargetOriginOrBirth.contributionCapacityU8AnyTargetProvenanceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityTargetOriginOrBirth.sourceGeneratedContributionCapacityResidualBirthAdmission

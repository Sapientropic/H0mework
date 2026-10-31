import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.ActualActorEvent
import H0mework.Foundation.Responsibility.Lineage

/-!
# Responsibility-lifecycle transfer adapter for actor succession

The singleton-fibre succession case consumes the existing responsibility
lifecycle mouth.  The vocabulary below is intentionally minimal: it installs
one indexed `TransferAcceptedAt` receipt and no responsibility process,
state, registry, or ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle

open ResponsibilityLifecycle ComplementObservation

inductive ActorBearer where
  | source (token : SourceToken)
  | target (token : TargetToken)
  deriving DecidableEq, Repr

inductive DebtLineage where
  | debt
  | other
  deriving DecidableEq, Repr

/-- The only inhabitable accepted-transfer receipt is indexed by the exact
middle event and the two neutral actor endpoints. -/
inductive ExactTransferAcceptedAt :
    EventState → ActorBearer → ActorBearer → Unit → Type
  | generated : ExactTransferAcceptedAt .after
      (.source .s5) (.target .t4) ()

/-- Minimal installation of the framework lifecycle vocabulary.  All
non-transfer evidence is inert `Unit`; no live state or ledger is created. -/
def actorLifecycleVocabulary : Vocabulary where
  SourceEvent := EventState
  Content := Unit
  Residual := Unit
  Bearer := ActorBearer
  ProtectedInterest := Unit
  Scope := Unit
  Lineage := DebtLineage
  Incidence := Unit
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun _ =>
    MinimalRegistrableSourceAnchor.canonical () DebtLineage.debt
  sourceIncidence := fun _ => ()
  ObstructionAt := fun _ => Unit
  demandContent := fun _ => ()
  demandResidual := fun _ => ()
  CommitmentAt := fun _ _ => Unit
  MandateOriginAt := fun _ _ => Unit
  AcceptedTaskAt := fun _ _ => Unit
  ActiveDependencyAt := fun _ _ => Unit
  ProtectedRiskAt := fun _ _ => Unit
  AdmissionAuthorityAt := fun _ _ => Unit
  AcceptedAt := fun _ _ _ => Unit
  StandingMandateAt := fun _ _ _ => Unit
  DischargeJurisdiction := fun _ _ => Unit
  ProgressAt := fun _ _ _ _ => Unit
  MaintenanceAt := fun _ _ _ => Unit
  TypedDeferAt := fun _ _ _ => Unit
  ScopeNarrowingAt := fun _ _ _ => Unit
  TransferAcceptedAt := ExactTransferAcceptedAt
  FulfilledAt := fun _ _ _ => Unit
  WaivedAt := fun _ _ _ => Unit
  InvalidatedAt := fun _ _ _ => Unit
  AbandonedAt := fun _ _ _ => Unit
  ImpossibleResidueAcceptedAt := fun _ _ _ => Unit
  SupersessionAt := fun _ _ _ _ _ _ _ => Unit
  ReopenAt := fun _ _ _ _ _ _ _ => Unit
  JurisdictionEndedAt := fun _ _ _ => Unit
  ConsentRevokedAt := fun _ _ _ => Unit
  CapacityReleasedAt := fun _ _ _ => Unit
  UpperRouteAt := fun _ _ _ => Unit
  NextActorSignal := Unit
  AgeSignal := Unit
  TransferOfferSignal := Unit

abbrev LifecycleVocabulary := actorLifecycleVocabulary

def sourceObligationPayload : NativeAdmissionPayload LifecycleVocabulary where
  sourceEvent := .before
  content := ()
  residual := ()
  bearer := .source .s5
  beneficiary := ()
  scope := ()
  lineage := .debt
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def sourceObligation : AdmittedObligation LifecycleVocabulary :=
  sourceObligationPayload.toObligation

def exactAcceptedTransferReceipt :
    LifecycleVocabulary.TransferAcceptedAt .after
      sourceObligation.bearer (.target .t4) sourceObligation.scope :=
  .generated

def acceptedTransferCarry :
    ActiveCarryDisposition LifecycleVocabulary sourceObligation
      .after :=
  .transferred (.target .t4) exactAcceptedTransferReceipt

/-- Direct framework consumer: the indexed accepted transfer preserves the
same debt lineage while changing bearer. -/
theorem acceptedTransferCarry_sameDebtLineage :
    SameDebtLineage sourceObligation acceptedTransferCarry.target :=
  acceptedTransfer_preserves_lineage exactAcceptedTransferReceipt

@[simp] theorem sourceObligation_lineage :
    sourceObligation.lineage = .debt :=
  rfl

theorem sourceObligation_lineage_nontrivial :
    sourceObligation.lineage ≠ .other := by
  intro lineageEqual
  cases lineageEqual

@[simp] theorem acceptedTransferCarry_targetBearer :
    acceptedTransferCarry.target.bearer = .target .t4 :=
  rfl

/-- A transfer token is the existing indexed lifecycle receipt itself, with
its endpoints exposed only through dependent sigma projections. -/
abbrev AcceptedTransferToken :=
  Sigma fun source : SourceToken =>
    Sigma fun target : TargetToken =>
      LifecycleVocabulary.TransferAcceptedAt .after
        (.source source) (.target target) ()

def acceptedTransferSeedAt (_source : Unit) (state : EventState)
    (_receipt : AcceptedTransferToken) : Prop :=
  state = .after

def acceptedTransferSeed :
    SourceSeed actualEventOccurrenceOf AcceptedTransferToken
      acceptedTransferSeedAt () :=
  ⟨⟨.s5, ⟨.t4, ExactTransferAcceptedAt.generated⟩⟩, .after,
    by simp [actualEventOccurrenceOf], rfl⟩

/-- Exact lifecycle receipt aligned with generated actor endpoints.  No
target actor or lifecycle verdict is accepted as input. -/
def AcceptedActorTransfer (source : SourceActor)
    (target : TargetActor) : Prop :=
  ∃ receipt :
      SourceSeed actualEventOccurrenceOf AcceptedTransferToken
        acceptedTransferSeedAt (),
    receipt.1.1 = source.1 ∧ receipt.1.2.1 = target.1

@[simp] theorem acceptedActorTransfer_iff
    (source : SourceActor) (target : TargetActor) :
    AcceptedActorTransfer source target ↔
      source.1 = .s5 ∧ target.1 = .t4 := by
  constructor
  · rintro ⟨⟨⟨sourceToken, targetToken, receipt⟩, _witness⟩,
      sourceEndpoint, targetEndpoint⟩
    cases receipt
    constructor
    · exact sourceEndpoint.symm
    · exact targetEndpoint.symm
  · rintro ⟨sourceValue, targetValue⟩
    refine ⟨acceptedTransferSeed, ?_, ?_⟩
    · change SourceToken.s5 = source.1
      change source.1 = SourceToken.s5 at sourceValue
      exact sourceValue.symm
    · change TargetToken.t4 = target.1
      change target.1 = TargetToken.t4 at targetValue
      exact targetValue.symm

/-- Any actor-level accepted transfer is backed by the framework receipt and
therefore by its same-debt-lineage theorem. -/
theorem AcceptedActorTransfer.sameDebtLineage
    {source : SourceActor} {target : TargetActor}
    (transfer : AcceptedActorTransfer source target) :
    source.1 = .s5 ∧
      target.1 = .t4 ∧
      sourceObligation.bearer = .source source.1 ∧
      acceptedTransferCarry.target.bearer = .target target.1 ∧
      sourceObligation.bearer ≠ acceptedTransferCarry.target.bearer ∧
      SameDebtLineage sourceObligation acceptedTransferCarry.target := by
  have endpoints := (acceptedActorTransfer_iff source target).mp transfer
  rcases endpoints with ⟨sourceEndpoint, targetEndpoint⟩
  refine ⟨sourceEndpoint, targetEndpoint, ?_, ?_, ?_,
    acceptedTransferCarry_sameDebtLineage⟩
  · change ActorBearer.source SourceToken.s5 = .source source.1
    rw [sourceEndpoint]
  · change ActorBearer.target TargetToken.t4 = .target target.1
    rw [targetEndpoint]
  · intro bearersEqual
    cases bearersEqual

end Lifecycle
end Society
end ProcessGame
end SaturationMonoid

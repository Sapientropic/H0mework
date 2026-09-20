import H0mework.Foundation.Responsibility.ResponsibilityCapacityKernel
import H0mework.Foundation.Responsibility.ObserverClassicalFactorization

/-!
# Focused responsibility lifecycle regression

The fixture covers a positive accepted admission, a standing-mandate override,
minimal negative controls, native review/exit/reopen, consumer-relative hidden
NULL, lineage and source-anchor anti-laundering countermodels, and exact
anchor/incidence ownership of actual-run carrying debit.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace Regression

open NativeResponsibilityProcess

inductive SourceEvent
  | obstruction
  | promise
  | mandate
  | review
  | terminal
  | reopen
  | capacity
  deriving DecidableEq

inductive Content
  | primary
  | replacement
  deriving DecidableEq

inductive Bearer
  | agent
  | successor
  deriving DecidableEq

inductive ProtectedInterest
  | user
  deriving DecidableEq

inductive Scope
  | local
  | upper
  deriving DecidableEq

inductive Lineage
  | original
  deriving DecidableEq

def fixtureVocabulary : Vocabulary where
  SourceEvent := SourceEvent
  Content := Content
  Residual := Nat
  Bearer := Bearer
  ProtectedInterest := ProtectedInterest
  Scope := Scope
  Lineage := Lineage
  Incidence := Unit
  SourceObservation := ComplementObservation.canonicalComplementPair
  sourceAnchor := fun _ =>
    MinimalRegistrableSourceAnchor.canonical .local .original
  sourceIncidence := fun _ => ()
  ObstructionAt := fun _ => Unit
  demandContent := fun _ => .primary
  demandResidual := fun _ => 3
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
  TransferAcceptedAt := fun _ _ _ _ => Unit
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
  NextActorSignal := Bearer
  AgeSignal := Nat
  TransferOfferSignal := Unit

abbrev V := fixtureVocabulary

/-- List-membership equalities used by the fixture proofs below; these replace
`simpa` scripts that no longer close against the pinned Mathlib simp set. -/
private theorem mem_singleton_eq {α : Type _} {a x : α} (h : x ∈ [a]) : x = a :=
  List.mem_singleton.1 h

private theorem mem_doubleton_eq {α : Type _} {a x : α} (h : x ∈ [a, a]) : x = a := by
  rcases List.mem_cons.1 h with h' | h'
  · exact h'
  · exact List.mem_singleton.1 h'

def acceptedPayload : NativeAdmissionPayload V where
  sourceEvent := .promise
  content := .primary
  residual := (3 : Nat)
  bearer := .agent
  beneficiary := .user
  scope := .local
  lineage := .original
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def mandatedPayload : NativeAdmissionPayload V where
  sourceEvent := .mandate
  content := .primary
  residual := (3 : Nat)
  bearer := .agent
  beneficiary := .user
  scope := .local
  lineage := .original
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .standingMandate ()
  authority := ()
  assumption := .mandated ()
  dischargeJurisdiction := ()

inductive AdmissionEvent
  | accepted
  | standingMandate

inductive BoundaryEvent (_obligation : AdmittedObligation V)
  | progress
  | progressTransfer
  | maintain
  | defer
  | narrow
  | transfer
  | terminal
  | supersede
  | bearerRelease

def boundaryDisposition
    {obligation : AdmittedObligation V} :
    BoundaryEvent obligation → BoundaryDisposition V obligation .review
  | .progress => .carry (.progressed (2 : Nat) ())
  | .progressTransfer =>
      .carry (.progressedAndTransferred (2 : Nat) .successor () ())
  | .maintain => .carry (.maintained ())
  | .defer => .carry (.deferred ())
  | .narrow => .carry (.narrowed .upper () ())
  | .transfer => .carry (.transferred .successor ())
  | .terminal => .terminal (.final (.fulfilled ()))
  | .supersede =>
      .terminal (.superseded
        { successor := obligation
          incidence := ()
          lineage_eq := rfl
          anchorTransport := SourceAnchorTransport.refl _ })
  | .bearerRelease =>
      .bearerRelease (.capacityReleasedWithResidue () ())

def reopenPayload (archive : TerminalArchive V) :
    NativeReopenPayload V archive where
  sourceEvent := .reopen
  admission :=
    { sourceEvent := .reopen
      content := archive.obligation.content
      residual := archive.obligation.residual
      bearer := archive.obligation.bearer
      beneficiary := archive.obligation.beneficiary
      scope := archive.obligation.admission.admittedScope
      lineage := archive.obligation.lineage
      anchor_scope_eq := archive.obligation.admittedScope_eq_sourceAnchorScope
      anchor_lineage_eq := archive.obligation.lineage_eq_sourceAnchorLineage
      origin := .explicitCommitment ()
      authority := ()
      assumption := .accepted ()
      dischargeJurisdiction := () }
  source_eq := rfl
  incidence := ()
  lineage_eq := rfl
  anchorTransport := SourceAnchorTransport.refl _

def process : NativeResponsibilityProcess V where
  AdmissionEvent := AdmissionEvent
  admissionPayload
    | .accepted => acceptedPayload
    | .standingMandate => mandatedPayload
  BoundaryEvent := BoundaryEvent
  boundarySource := fun _ => .review
  boundary_anchor_eq := fun _ => rfl
  boundary_incidence_eq := fun _ => rfl
  boundaryDisposition := boundaryDisposition
  ReopenEvent := fun _ => Unit
  reopenPayload := fun {_} _ => reopenPayload _

abbrev P := process

def emptyState : ResponsibilityState V := ResponsibilityState.empty V

def acceptedEdge : P.Edge emptyState := .admit .accepted

def acceptedState : ResponsibilityState V := acceptedEdge.target

def mandatedEdge : P.Edge emptyState := .admit .standingMandate

def mandatedState : ResponsibilityState V := mandatedEdge.target

theorem explicit_commitment_and_acceptance_admit :
    acceptedState.LiveAt 0 := by
  refine ⟨acceptedPayload.toObligation, ?_⟩
  exact admit_target_slot (P := P) .accepted

theorem standing_mandate_override_admits :
    mandatedState.LiveAt 0 := by
  refine ⟨mandatedPayload.toObligation, ?_⟩
  exact admit_target_slot (P := P) .standingMandate

theorem acceptedFreshAllocation :
    ResponsibilityState.FreshlyAllocatedAt emptyState acceptedState 0 := by
  exact ⟨rfl, explicit_commitment_and_acceptance_admit⟩

def acceptedAdmissionWitness :
    P.FreshAdmissionWitness acceptedEdge 0 :=
  NativeResponsibilityProcess.Edge.freshlyAllocated_generates_admission
    P acceptedEdge 0 acceptedFreshAllocation

def fixtureObstruction : V.ObstructionAt .obstruction := ()

def fixtureDemand : ProducerDemand V :=
  producerDemandOfObstruction fixtureObstruction

theorem obstruction_generates_demand_not_bearer_assignment :
    fixtureDemand.content = .primary ∧ fixtureDemand.residual = (3 : Nat) := by
  exact ⟨rfl, rfl⟩

/-- Dirty fixture: with no acceptance or standing mandate, an admission
payload cannot be constructed even though an obstruction demand exists. -/
def noAssumptionVocabulary : Vocabulary :=
  { fixtureVocabulary with
    AcceptedAt := fun _ _ _ => Empty
    StandingMandateAt := fun _ _ _ => Empty }

instance noAssumptionPayloadIsEmpty :
    IsEmpty (NativeAdmissionPayload noAssumptionVocabulary) where
  false payload := by
    cases payload.assumption with
    | accepted receipt => exact nomatch receipt
    | mandated receipt => exact nomatch receipt

theorem obstruction_only_does_not_admit :
    Nonempty (ProducerDemand noAssumptionVocabulary) ∧
      IsEmpty (NativeAdmissionPayload noAssumptionVocabulary) := by
  refine ⟨⟨producerDemandOfObstruction (V := noAssumptionVocabulary)
    (source := .obstruction) ()⟩, inferInstance⟩

theorem next_actor_and_age_do_not_mutate_lifecycle :
    NativeResponsibilityProcess.ResponsibilityState.observeNonAdmission
        emptyState (.nextActor Bearer.successor) = emptyState ∧
      NativeResponsibilityProcess.ResponsibilityState.observeNonAdmission
        emptyState (.age (100 : Nat)) = emptyState :=
  ⟨rfl, rfl⟩

def acceptedSlot : Fin acceptedState.slots.length := ⟨0, by simp [acceptedState, acceptedEdge, emptyState, Edge.target]⟩

theorem acceptedPresent :
    acceptedState.slots.get acceptedSlot = .live acceptedPayload.toObligation := rfl

def maintainEdge : P.Edge acceptedState :=
  .cross acceptedSlot acceptedPayload.toObligation acceptedPresent .maintain

def transferEdge : P.Edge acceptedState :=
  .cross acceptedSlot acceptedPayload.toObligation acceptedPresent .transfer

def progressTransferEdge : P.Edge acceptedState :=
  .cross acceptedSlot acceptedPayload.toObligation acceptedPresent
    .progressTransfer

def terminalEdge : P.Edge acceptedState :=
  .cross acceptedSlot acceptedPayload.toObligation acceptedPresent .terminal

def supersedeEdge : P.Edge acceptedState :=
  .cross acceptedSlot acceptedPayload.toObligation acceptedPresent .supersede

theorem review_generates_typed_carry :
    ∃ disposition : BoundaryDisposition V acceptedPayload.toObligation .review,
      disposition = P.boundaryDisposition
        (@BoundaryEvent.maintain acceptedPayload.toObligation) ∧
      maintainEdge.target.slots[0]? = some disposition.targetSlot := by
  exact cross_generates_native_disposition (P := P) acceptedSlot
    acceptedPayload.toObligation acceptedPresent .maintain

theorem accepted_transfer_changes_bearer_preserves_lineage :
    ∃ next : AdmittedObligation V,
      transferEdge.target.slots[0]? = some (.live next) ∧
      next.bearer = Bearer.successor ∧ next.lineage = acceptedPayload.lineage := by
  refine ⟨(ActiveCarryDisposition.transferred
    (V := V) (obligation := acceptedPayload.toObligation)
    (source := SourceEvent.review) Bearer.successor ()).target, ?_, rfl, rfl⟩
  exact cross_target_slot (P := P) acceptedSlot acceptedPayload.toObligation
    acceptedPresent .transfer

theorem accepted_progress_and_transfer_updates_one_exact_target :
    ∃ next : AdmittedObligation V,
      progressTransferEdge.target.slots[0]? = some (.live next) ∧
      next.residual = (2 : Nat) ∧
      next.bearer = Bearer.successor ∧
      next.lineage = acceptedPayload.lineage := by
  refine ⟨(ActiveCarryDisposition.progressedAndTransferred
    (V := V) (obligation := acceptedPayload.toObligation)
    (source := SourceEvent.review) (2 : Nat) Bearer.successor () ()).target,
    ?_, rfl, rfl, rfl⟩
  exact cross_target_slot (P := P) acceptedSlot acceptedPayload.toObligation
    acceptedPresent .progressTransfer

theorem terminal_exit_is_the_only_disappearance :
    terminalEdge.lifecycleEvent.kind = .obligationTerminal := by
  apply terminalEdge.disappears_implies_obligationTerminal (slot := 0)
  constructor
  · exact explicit_commitment_and_acceptance_admit
  · intro targetLive
    rcases targetLive with ⟨target, targetAt⟩
    cases targetAt

theorem terminalDisappears :
    ResponsibilityState.DisappearsAt acceptedState terminalEdge.target 0 := by
  constructor
  · exact explicit_commitment_and_acceptance_admit
  · intro targetLive
    rcases targetLive with ⟨target, targetAt⟩
    cases targetAt

def terminalReceiptWitness :
    P.FinalDisappearanceWitness terminalEdge 0 :=
  NativeResponsibilityProcess.Edge.disappears_generates_finalReceipt
    P terminalEdge 0 terminalDisappears

theorem supersession_keeps_live_successor :
    supersedeEdge.target.LiveAt 0 := by
  refine ⟨acceptedPayload.toObligation, ?_⟩
  exact cross_target_slot (P := P) acceptedSlot acceptedPayload.toObligation
    acceptedPresent .supersede

def terminalArchive : TerminalArchive V :=
  ⟨acceptedPayload.toObligation, .review, .fulfilled ()⟩

def terminalState : ResponsibilityState V := terminalEdge.target

def terminalSlot : Fin terminalState.slots.length :=
  ⟨0, by simp [terminalState, terminalEdge, acceptedState, acceptedEdge,
    emptyState, Edge.target]⟩

theorem terminalPresent :
    terminalState.slots.get terminalSlot = .terminal terminalArchive := rfl

def reopenEdge : P.Edge terminalState :=
  .reopen terminalSlot terminalArchive terminalPresent ()

theorem reopen_restores_live_same_lineage :
    ∃ reopened : AdmittedObligation V,
      reopenEdge.target.slots[0]? = some (.live reopened) ∧
      SameDebtLineage acceptedPayload.toObligation reopened := by
  refine ⟨(reopenPayload terminalArchive).admission.toObligation, ?_, ?_⟩
  · exact reopen_target_slot (P := P) terminalSlot terminalArchive terminalPresent ()
  · exact (reopenPayload terminalArchive).sameDebtLineage

def invisibleObserver : ScopeObserver V := ⟨fun _ => false⟩

theorem invisible_admission_is_hidden_not_safe :
    ¬ ConsumerSafe invisibleObserver.observe currentResponsibilityObserver := by
  exact (scopeObserver_invisibleAdmissionHiddenNull P invisibleObserver
    (source := emptyState) .accepted rfl).not_consumerSafe

theorem full_observer_sees_admission :
    currentResponsibilityObserver acceptedState ≠
      currentResponsibilityObserver emptyState :=
  admit_currentResponsibilityObserver_ne (P := P) .accepted

theorem full_observer_is_consumer_safe :
    ConsumerSafe
      (currentResponsibilityObserver (V := V))
      (currentResponsibilityObserver (V := V)) := by
  intro left right sameObservation
  exact sameObservation

def certifiedFullObserver : ConsumerKernelStatus
    (currentResponsibilityObserver (V := V))
    (currentResponsibilityObserver (V := V)) :=
  .certifiedSafe full_observer_is_consumer_safe

noncomputable def factoredFullObserver :
    Set.range (currentResponsibilityObserver (V := V)) →
      List (Option (AdmittedObligation V)) :=
  ConsumerSafe.factorOnImage
    (observe := currentResponsibilityObserver (V := V))
    (consumer := currentResponsibilityObserver (V := V))
    full_observer_is_consumer_safe

theorem factored_full_observer_commutes (state : ResponsibilityState V) :
    factoredFullObserver
      ⟨currentResponsibilityObserver state, ⟨state, rfl⟩⟩ =
        currentResponsibilityObserver state :=
  ConsumerSafe.factorOnImage_apply
    (observe := currentResponsibilityObserver (V := V))
    (consumer := currentResponsibilityObserver (V := V))
    full_observer_is_consumer_safe state

def unclassifiedFixture : ConsumerKernelStatus
    invisibleObserver.observe currentResponsibilityObserver :=
  .unclassified

theorem unclassified_does_not_default_safe :
    ¬ unclassifiedFixture.IsCertifiedSafe := by
  exact ConsumerKernelStatus.unclassified_not_certifiedSafe

inductive TriggerState
  | reachable
  | unreachable

def triggerObserver (_ : TriggerState) : Unit := ()

def triggerConsumer : TriggerState → Bool
  | .reachable => true
  | .unreachable => false

def unreachableTriggerHiddenNull :
    HiddenNullWitness triggerObserver triggerConsumer where
  left := .reachable
  right := .unreachable
  sameObservation := rfl
  differentDisposition := by decide

theorem unreachable_trigger_is_not_certified_safe :
    ¬ ConsumerSafe triggerObserver triggerConsumer :=
  unreachableTriggerHiddenNull.not_consumerSafe

/-- Dirty fixture: a string-like `later` signal has no typed defer receipt. -/
def noDeferVocabulary : Vocabulary :=
  { fixtureVocabulary with TypedDeferAt := fun _ _ _ => Empty }

theorem noDeferReceiptIsEmpty
    (source : noDeferVocabulary.SourceEvent)
    (content : noDeferVocabulary.Content)
    (scope : noDeferVocabulary.Scope) :
    IsEmpty (noDeferVocabulary.TypedDeferAt source content scope) where
  false receipt := nomatch receipt

theorem transfer_offer_is_not_acceptance :
    (transferOfferObservation acceptedPayload.toObligation ()).bearer = .agent ∧
      SameDebtLineage acceptedPayload.toObligation
        (transferOfferObservation acceptedPayload.toObligation ()) :=
  ⟨rfl, rfl⟩

def restructuringVocabulary : RestructuringVocabulary where
  base := V
  DescendantAt := fun _ _ _ _ _ => Unit
  SplitCoverageAt := fun _ _ _ => Unit
  MergeCoverageAt := fun _ _ _ => Unit
  LocalDischargePreservedAt := fun _ _ _ => Unit
  RenameAt := fun _ _ _ => Unit

def splitReceipt : SplitReceipt restructuringVocabulary acceptedPayload.toObligation where
  sourceEvent := .review
  sourceOwnership := ⟨rfl, rfl⟩
  children := [acceptedPayload.toObligation, acceptedPayload.toObligation]
  children_nonempty := by simp
  coverage := ()
  descendant := by intro child member; exact ()
  anchorTransport := by
    intro child member
    have child_eq : child = acceptedPayload.toObligation := mem_doubleton_eq member
    subst child
    exact SourceAnchorTransport.refl _
  lineage := by
    intro child member
    have child_eq : child = acceptedPayload.toObligation := mem_doubleton_eq member
    subst child
    rfl
  localDischarge := by intro child member; exact ()

theorem split_retains_children_and_local_criteria :
    ∃ child, child ∈ splitReceipt.children ∧
      Nonempty (restructuringVocabulary.LocalDischargePreservedAt
        splitReceipt.sourceEvent acceptedPayload.content child.content) := by
  rcases splitReceipt.exists_child with ⟨child, member⟩
  exact ⟨child, member, ⟨splitReceipt.localDischarge child member⟩⟩

def renameReceipt : RenameReceipt restructuringVocabulary
    acceptedPayload.toObligation acceptedPayload.toObligation where
  sourceEvent := .review
  sourceOwnership := ⟨rfl, rfl⟩
  renamedAt := ()
  anchorTransport := SourceAnchorTransport.refl _
  incidence_eq := rfl
  lineage_eq := rfl

theorem rename_does_not_reset_debt :
    SameDebtLineage acceptedPayload.toObligation acceptedPayload.toObligation :=
  renameReceipt.sameDebtLineage

def mergeReceipt : MergeReceipt restructuringVocabulary where
  sourceEvent := .review
  parents := [acceptedPayload.toObligation, acceptedPayload.toObligation]
  parents_nonempty := by simp
  target := acceptedPayload.toObligation
  sourceOwnership := ⟨rfl, rfl⟩
  coverage := ()
  ancestor := by intro parent member; exact ()
  anchorTransport := by
    intro parent member
    have parent_eq : parent = acceptedPayload.toObligation := mem_doubleton_eq member
    subst parent
    exact SourceAnchorTransport.refl _
  lineage := by
    intro parent member
    have parent_eq : parent = acceptedPayload.toObligation := mem_doubleton_eq member
    subst parent
    rfl
  localDischarge := by intro parent member; exact ()

theorem merge_retains_each_local_criterion
    {parent : AdmittedObligation V} (member : parent ∈ mergeReceipt.parents) :
    Nonempty (restructuringVocabulary.LocalDischargePreservedAt
      mergeReceipt.sourceEvent parent.content mergeReceipt.target.content) :=
  ⟨mergeReceipt.every_parent_retains_localDischarge member⟩

def incidenceLedger : IncidenceLedger restructuringVocabulary .review
    [acceptedPayload.toObligation] [acceptedPayload.toObligation] where
  oldDestination := by
    intro old member
    have old_eq : old = acceptedPayload.toObligation := mem_singleton_eq member
    subst old
    exact .descendants
      { descendants := [acceptedPayload.toObligation]
        sourceOwnership := ⟨rfl, rfl⟩
        nonempty := by simp
        target_member := by intro child childMember; simpa using childMember
        coverage := ()
        incidence := by intro child childMember; exact ()
        anchorTransport := by
          intro child childMember
          have child_eq : child = acceptedPayload.toObligation := mem_singleton_eq childMember
          subst child
          exact SourceAnchorTransport.refl _
        lineage := by
          intro child childMember
          have child_eq : child = acceptedPayload.toObligation := mem_singleton_eq childMember
          subst child
          rfl
        localDischarge := by intro child childMember; exact () }
  newOrigin := by
    intro next member
    have next_eq : next = acceptedPayload.toObligation := mem_singleton_eq member
    subst next
    exact .inherited acceptedPayload.toObligation (List.mem_singleton.2 rfl) ⟨rfl, rfl⟩ ()
      (SourceAnchorTransport.refl _) rfl ()
  compatible := by
    intro old oldMember next nextMember
    have old_eq : old = acceptedPayload.toObligation := mem_singleton_eq oldMember
    have next_eq : next = acceptedPayload.toObligation := mem_singleton_eq nextMember
    subst old
    subst next
    exact List.mem_singleton

theorem incidence_ledger_has_no_phantom_lineage :
    (match incidenceLedger.oldDestination acceptedPayload.toObligation
        (List.mem_singleton.2 rfl) with
      | .descendants family =>
          acceptedPayload.toObligation ∈ family.descendants
      | .terminal _ _ => False) ↔
    (match incidenceLedger.newOrigin acceptedPayload.toObligation
        (List.mem_singleton.2 rfl) with
      | .inherited ancestor _ _ _ _ _ _ =>
          ancestor = acceptedPayload.toObligation
      | .admitted .. => False) := by
  exact incidenceLedger.compatible acceptedPayload.toObligation (List.mem_singleton.2 rfl)
    acceptedPayload.toObligation (List.mem_singleton.2 rfl)

/-- Two genuinely different debt lineages used to reject restructuring
receipts that preserve only content-level incidence. -/
def boolLineageVocabulary : Vocabulary :=
  { fixtureVocabulary with
    Lineage := Bool
    sourceAnchor := fun source =>
      match source with
      | .mandate => MinimalRegistrableSourceAnchor.canonical .local true
      | _ => MinimalRegistrableSourceAnchor.canonical .local false }

abbrev BoolLineageV := boolLineageVocabulary

def lineageParentPayload : NativeAdmissionPayload BoolLineageV where
  sourceEvent := .promise
  content := .primary
  residual := (3 : Nat)
  bearer := .agent
  beneficiary := .user
  scope := .local
  lineage := false
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def lineageChildPayload : NativeAdmissionPayload BoolLineageV where
  sourceEvent := .mandate
  content := .replacement
  residual := (2 : Nat)
  bearer := .agent
  beneficiary := .user
  scope := .local
  lineage := true
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def boolLineageRestructuringVocabulary : RestructuringVocabulary where
  base := BoolLineageV
  DescendantAt := fun _ _ _ _ _ => Unit
  SplitCoverageAt := fun _ _ _ => Unit
  MergeCoverageAt := fun _ _ _ => Unit
  LocalDischargePreservedAt := fun _ _ _ => Unit
  RenameAt := fun _ _ _ => Unit

theorem split_cannot_change_debt_lineage
    (receipt : SplitReceipt boolLineageRestructuringVocabulary
      lineageParentPayload.toObligation)
    (member : lineageChildPayload.toObligation ∈ receipt.children) : False := by
  have lineage := receipt.child_preserves_lineage member
  change false = true at lineage
  cases lineage

theorem merge_cannot_change_debt_lineage
    (receipt : MergeReceipt boolLineageRestructuringVocabulary)
    (parentMember : lineageParentPayload.toObligation ∈ receipt.parents)
    (target_eq : receipt.target = lineageChildPayload.toObligation) : False := by
  have lineage := receipt.every_parent_preserves_lineage parentMember
  rw [target_eq] at lineage
  change false = true at lineage
  cases lineage

theorem descendant_family_cannot_change_debt_lineage
    (family : DescendantFamily boolLineageRestructuringVocabulary .review
      lineageParentPayload.toObligation [lineageChildPayload.toObligation])
    (member : lineageChildPayload.toObligation ∈ family.descendants) : False := by
  have lineage := family.lineage lineageChildPayload.toObligation member
  change false = true at lineage
  cases lineage

theorem inherited_origin_cannot_change_debt_lineage
    (origin : InheritedOrigin boolLineageRestructuringVocabulary .review
      [lineageParentPayload.toObligation] lineageChildPayload.toObligation) : False := by
  have lineage := origin.lineage
  have ancestor_eq : origin.ancestor = lineageParentPayload.toObligation := mem_singleton_eq origin.ancestor_member
  rw [ancestor_eq] at lineage
  change false = true at lineage
  cases lineage

theorem supersession_cannot_change_debt_lineage
    (receipt : SupersessionReceipt BoolLineageV
      lineageParentPayload.toObligation .review)
    (successor_eq : receipt.successor = lineageChildPayload.toObligation) : False := by
  have lineage := receipt.successor_lineage
  rw [successor_eq] at lineage
  change true = false at lineage
  cases lineage

/-! Same-lineage obligations may still belong to different source scopes.
The restructuring mouths therefore require an explicit whole-anchor
transport rather than accepting content and lineage coincidence alone. -/

def scopeAnchorVocabulary : Vocabulary :=
  { fixtureVocabulary with
    sourceAnchor := fun source =>
      match source with
      | .mandate => MinimalRegistrableSourceAnchor.canonical .upper .original
      | _ => MinimalRegistrableSourceAnchor.canonical .local .original }

abbrev ScopeAnchorV := scopeAnchorVocabulary

def scopeParentPayload : NativeAdmissionPayload ScopeAnchorV where
  sourceEvent := .promise
  content := .primary
  residual := (3 : Nat)
  bearer := .agent
  beneficiary := .user
  scope := .local
  lineage := .original
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def scopeChildPayload : NativeAdmissionPayload ScopeAnchorV where
  sourceEvent := .mandate
  content := .replacement
  residual := (2 : Nat)
  bearer := .agent
  beneficiary := .user
  scope := .upper
  lineage := .original
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def scopeParentState : ResponsibilityState ScopeAnchorV :=
  ⟨[.live scopeParentPayload.toObligation], []⟩

def scopeChildState : ResponsibilityState ScopeAnchorV :=
  ⟨[.live scopeChildPayload.toObligation], []⟩

theorem full_observer_does_not_erase_source_anchor_scope :
    currentResponsibilityObserver scopeParentState ≠
      currentResponsibilityObserver scopeChildState := by
  intro observerEq
  have obligationEq : scopeParentPayload.toObligation =
      scopeChildPayload.toObligation := by
    simpa [currentResponsibilityObserver, scopeParentState,
      scopeChildState] using observerEq
  have scopeEq := congrArg
    (fun obligation : AdmittedObligation ScopeAnchorV => obligation.scope)
    obligationEq
  change Scope.local = Scope.upper at scopeEq
  cases scopeEq

def scopeAnchorRestructuringVocabulary : RestructuringVocabulary where
  base := ScopeAnchorV
  DescendantAt := fun _ _ _ _ _ => Unit
  SplitCoverageAt := fun _ _ _ => Unit
  MergeCoverageAt := fun _ _ _ => Unit
  LocalDischargePreservedAt := fun _ _ _ => Unit
  RenameAt := fun _ _ _ => Unit

theorem split_cannot_launder_source_anchor_scope
    (receipt : SplitReceipt scopeAnchorRestructuringVocabulary
      scopeParentPayload.toObligation)
    (member : scopeChildPayload.toObligation ∈ receipt.children) : False := by
  have scopeEq :=
    (receipt.child_preserves_sourceAnchor member).scope_eq
  change Scope.local = Scope.upper at scopeEq
  cases scopeEq

theorem merge_cannot_launder_source_anchor_scope
    (receipt : MergeReceipt scopeAnchorRestructuringVocabulary)
    (parentMember : scopeParentPayload.toObligation ∈ receipt.parents)
    (target_eq : receipt.target = scopeChildPayload.toObligation) : False := by
  have scopeEq :=
    (receipt.every_parent_preserves_sourceAnchor parentMember).scope_eq
  rw [target_eq] at scopeEq
  change Scope.local = Scope.upper at scopeEq
  cases scopeEq

theorem descendant_family_cannot_launder_source_anchor_scope
    (family : DescendantFamily scopeAnchorRestructuringVocabulary .review
      scopeParentPayload.toObligation [scopeChildPayload.toObligation])
    (member : scopeChildPayload.toObligation ∈ family.descendants) : False := by
  have scopeEq :=
    (family.anchorTransport scopeChildPayload.toObligation member).scope_eq
  change Scope.local = Scope.upper at scopeEq
  cases scopeEq

theorem inherited_origin_cannot_launder_source_anchor_scope
    (origin : InheritedOrigin scopeAnchorRestructuringVocabulary .review
      [scopeParentPayload.toObligation] scopeChildPayload.toObligation) : False := by
  have ancestor_eq : origin.ancestor = scopeParentPayload.toObligation := mem_singleton_eq origin.ancestor_member
  have scopeEq := origin.anchorTransport.scope_eq
  rw [ancestor_eq] at scopeEq
  change Scope.local = Scope.upper at scopeEq
  cases scopeEq

def capacityVocabulary : CapacityVocabulary V where
  IncompatibleDemand := Unit
  AffectedDependency := Unit
  ProtectedBoundary := Unit

def shortageReadout : CapacityReadout V capacityVocabulary where
  sourceEvent := .capacity
  bearer := .agent
  admitted := [acceptedPayload.toObligation]
  demandedCapacity := 2
  availableCapacity := 1
  incompatibleDemands := [()]
  affectedDependencies := [()]
  protectedBoundaries := [()]

def sufficientReadout : CapacityReadout V capacityVocabulary :=
  { shortageReadout with demandedCapacity := 1, availableCapacity := 2 }

def capacityProcess : NativeCapacityProcess V capacityVocabulary where
  CapacityEvent := Unit
  readout := fun _ => shortageReadout

theorem shortage_generates_capacity_obstruction :
    ∃ obstruction, shortageReadout.obstruction? = some obstruction := by
  exact shortageReadout.obstruction?_eq_some_iff.mpr (by decide)

theorem actual_capacity_event_generates_obstruction :
    ∃ obstruction, capacityProcess.obstruction? () = some obstruction := by
  exact shortage_generates_capacity_obstruction

theorem sufficient_capacity_generates_no_obstruction :
    sufficientReadout.obstruction? = none := by
  exact sufficientReadout.obstruction?_eq_none_iff.mpr (by decide)

def zeroDebits : StrictBudgetRun 3 3 := .nil

def oneDebit : StrictBudgetRun 3 2 := .step zeroDebits (by decide)

def twoDebits : StrictBudgetRun 3 1 := .step oneDebit (by decide)

def threeDebits : StrictBudgetRun 3 0 := .step twoDebits (by decide)

theorem strictBudgetRun_arithmetic_bound :
    threeDebits.length = 3 ∧ threeDebits.length ≤ 3 := by
  exact ⟨rfl, threeDebits.length_le_start⟩

def lifecycleBudgetAt
    (state : ResponsibilityState V) (_lineage : V.Lineage) : Nat :=
  2 - state.history.length

def firstMaintenanceDebit :
    ActualMaintenanceDebit P lifecycleBudgetAt maintainEdge .original where
  slot := 0
  obligation := acceptedPayload.toObligation
  sourceEvent := .review
  receipt := ()
  event_eq := rfl
  source_live := rfl
  target_live := rfl
  lineage_eq := rfl
  strict_debit := by decide

def firstMaintenanceDebitOwnership :
    SourceOwnsResponsibilityIncidence V .review
      acceptedPayload.toObligation :=
  ActualMaintenanceDebit.sourceOwnership (V := V) firstMaintenanceDebit

theorem actual_maintenance_debit_preserves_anchor_and_incidence :
    V.sourceAnchor SourceEvent.review =
        acceptedPayload.toObligation.sourceAnchor ∧
      V.sourceIncidence SourceEvent.review =
        acceptedPayload.toObligation.sourceIncidence :=
  ⟨(ActualMaintenanceDebit.sourceOwnership (V := V)
      firstMaintenanceDebit).anchor_eq,
    (ActualMaintenanceDebit.sourceOwnership (V := V)
      firstMaintenanceDebit).incidence_eq⟩

/-- The fixture process recognizes only the exact first maintained edge. -/
inductive FixtureDebitEvent :
    {source : ResponsibilityState V} → P.Edge source → V.Lineage → Type
  | first : FixtureDebitEvent maintainEdge .original

def lifecycleBudgetProcess : NativeCarryDebitProcess P where
  budgetAt := lifecycleBudgetAt
  DebitEvent := FixtureDebitEvent
  debitReceipt := by
    intro source edge lineage event
    cases event
    exact firstMaintenanceDebit

def oneMaintenanceRun : P.Run acceptedState maintainEdge.target :=
  .step .nil maintainEdge

def oneMaintenanceDebited :
    NativeDebitedRun P lifecycleBudgetProcess .original oneMaintenanceRun :=
  .step (.nil acceptedState) maintainEdge .first

theorem actual_lifecycle_run_is_budget_bounded :
    oneMaintenanceRun.events.length = 1 ∧
      oneMaintenanceRun.events.length +
          lifecycleBudgetProcess.budgetAt maintainEdge.target .original ≤
        lifecycleBudgetProcess.budgetAt acceptedState .original := by
  exact ⟨rfl,
    oneMaintenanceDebited.events_length_add_targetBudget_le_sourceBudget⟩

def maintainedSlot : Fin maintainEdge.target.slots.length :=
  ⟨0, by
    simp [maintainEdge, acceptedState, acceptedEdge, emptyState, Edge.target]⟩

theorem maintainedPresent :
    maintainEdge.target.slots.get maintainedSlot =
      .live acceptedPayload.toObligation := rfl

def secondMaintainEdge : P.Edge maintainEdge.target :=
  .cross maintainedSlot acceptedPayload.toObligation maintainedPresent .maintain

theorem zero_budget_rejects_further_maintenance_debit :
    IsEmpty
      (lifecycleBudgetProcess.DebitEvent secondMaintainEdge .original) := by
  apply oneMaintenanceDebited.no_extension_of_sourceBudget_exhausted
    (edge := secondMaintainEdge)
  rfl

end Regression
end ResponsibilityLifecycle
end SaturationMonoid

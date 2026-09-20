import H0mework.Foundation.Responsibility.Observer

/-!
# Responsibility restructuring and anti-laundering laws

Ticket counts and aggregate residuals are not a conservation law.  Split,
merge, rename, transfer, and supersession must instead carry source-backed
lineage and local discharge coverage.

The records in this module are receipts/consumer mouths.  They do not claim
that an arbitrary domain has already generated the corresponding actual
event.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle

universe u

/-- Extra vocabulary needed only by restructuring events. -/
structure RestructuringVocabulary where
  base : Vocabulary.{u}
  DescendantAt : base.SourceEvent →
    base.Incidence → base.Content → base.Incidence → base.Content → Type u
  SplitCoverageAt : base.SourceEvent → base.Content → List base.Content → Type u
  MergeCoverageAt : base.SourceEvent → List base.Content → base.Content → Type u
  LocalDischargePreservedAt :
    base.SourceEvent → base.Content → base.Content → Type u
  RenameAt : base.SourceEvent → base.Content → base.Content → Type u

namespace RestructuringVocabulary

abbrev Obligation (R : RestructuringVocabulary) := AdmittedObligation R.base

end RestructuringVocabulary

/-- Exact same-debt lineage.  Bearer, scope, and presentation may change, but
the admission lineage key cannot be silently reset. -/
def SameDebtLineage
    {V : Vocabulary} (old next : AdmittedObligation V) : Prop :=
  old.lineage = next.lineage

theorem ActiveCarryDisposition.sameDebtLineage_target
    {V : Vocabulary} {obligation : AdmittedObligation V}
    {source : V.SourceEvent}
    (disposition : ActiveCarryDisposition V obligation source) :
    SameDebtLineage obligation disposition.target :=
  disposition.target_lineage.symm

theorem BearerReleaseReceipt.sameDebtLineage_target
    {V : Vocabulary} {obligation : AdmittedObligation V}
    {source : V.SourceEvent}
    (receipt : BearerReleaseReceipt V obligation source) :
    SameDebtLineage obligation receipt.target :=
  receipt.target_lineage.symm

theorem SupersessionReceipt.sameDebtLineage_successor
    {V : Vocabulary} {obligation : AdmittedObligation V}
    {source : V.SourceEvent}
    (receipt : SupersessionReceipt V obligation source) :
    SameDebtLineage obligation receipt.successor :=
  receipt.successor_lineage.symm

/-- Split receipt covers every child individually and also supplies a global
coverage receipt for the parent criteria. -/
structure SplitReceipt (R : RestructuringVocabulary)
    (parent : R.Obligation) : Type u where
  sourceEvent : R.base.SourceEvent
  sourceOwnership :
    SourceOwnsResponsibilityIncidence R.base sourceEvent parent
  children : List R.Obligation
  children_nonempty : children ≠ []
  coverage : R.SplitCoverageAt sourceEvent parent.content
    (children.map AdmittedObligation.content)
  descendant : ∀ child, child ∈ children →
    R.DescendantAt sourceEvent parent.sourceIncidence parent.content
      child.sourceIncidence child.content
  anchorTransport : ∀ child, child ∈ children →
    SourceAnchorTransport parent.sourceAnchor child.sourceAnchor
  lineage : ∀ child, child ∈ children → SameDebtLineage parent child
  localDischarge : ∀ child, child ∈ children →
    R.LocalDischargePreservedAt sourceEvent parent.content child.content

theorem SplitReceipt.exists_child
    {R : RestructuringVocabulary} {parent : R.Obligation}
    (receipt : SplitReceipt R parent) : ∃ child, child ∈ receipt.children := by
  cases children_eq : receipt.children with
  | nil => exact (receipt.children_nonempty children_eq).elim
  | cons child rest =>
      exact ⟨child, by simp⟩

def SplitReceipt.child_has_descendant_and_localDischarge
    {R : RestructuringVocabulary} {parent : R.Obligation}
    (receipt : SplitReceipt R parent)
    {child : R.Obligation} (member : child ∈ receipt.children) :
    R.DescendantAt receipt.sourceEvent parent.sourceIncidence parent.content
        child.sourceIncidence child.content ×
      R.LocalDischargePreservedAt receipt.sourceEvent parent.content
        child.content :=
  ⟨receipt.descendant child member, receipt.localDischarge child member⟩

theorem SplitReceipt.child_preserves_lineage
    {R : RestructuringVocabulary} {parent : R.Obligation}
    (receipt : SplitReceipt R parent)
    {child : R.Obligation} (member : child ∈ receipt.children) :
    SameDebtLineage parent child :=
  receipt.lineage child member

def SplitReceipt.child_preserves_sourceAnchor
    {R : RestructuringVocabulary} {parent : R.Obligation}
    (receipt : SplitReceipt R parent)
    {child : R.Obligation} (member : child ∈ receipt.children) :
    SourceAnchorTransport parent.sourceAnchor child.sourceAnchor :=
  receipt.anchorTransport child member

/-- Merge receipt retains one ancestor incidence and one local discharge
receipt for every component.  Aggregate cancellation cannot discharge a
component by itself. -/
structure MergeReceipt (R : RestructuringVocabulary) : Type u where
  sourceEvent : R.base.SourceEvent
  parents : List R.Obligation
  parents_nonempty : parents ≠ []
  target : R.Obligation
  sourceOwnership :
    SourceOwnsResponsibilityIncidence R.base sourceEvent target
  coverage : R.MergeCoverageAt sourceEvent
    (parents.map AdmittedObligation.content) target.content
  ancestor : ∀ parent, parent ∈ parents →
    R.DescendantAt sourceEvent parent.sourceIncidence parent.content
      target.sourceIncidence target.content
  anchorTransport : ∀ parent, parent ∈ parents →
    SourceAnchorTransport parent.sourceAnchor target.sourceAnchor
  lineage : ∀ parent, parent ∈ parents → SameDebtLineage parent target
  localDischarge : ∀ parent, parent ∈ parents →
    R.LocalDischargePreservedAt sourceEvent parent.content target.content

def MergeReceipt.every_parent_retains_localDischarge
    {R : RestructuringVocabulary} (receipt : MergeReceipt R)
    {parent : R.Obligation} (member : parent ∈ receipt.parents) :
    R.LocalDischargePreservedAt receipt.sourceEvent parent.content
      receipt.target.content :=
  receipt.localDischarge parent member

theorem MergeReceipt.every_parent_preserves_lineage
    {R : RestructuringVocabulary} (receipt : MergeReceipt R)
    {parent : R.Obligation} (member : parent ∈ receipt.parents) :
    SameDebtLineage parent receipt.target :=
  receipt.lineage parent member

def MergeReceipt.every_parent_preserves_sourceAnchor
    {R : RestructuringVocabulary} (receipt : MergeReceipt R)
    {parent : R.Obligation} (member : parent ∈ receipt.parents) :
    SourceAnchorTransport parent.sourceAnchor receipt.target.sourceAnchor :=
  receipt.anchorTransport parent member

/-- Rename is presentation change only when exact debt lineage is retained. -/
structure RenameReceipt (R : RestructuringVocabulary)
    (old renamed : R.Obligation) : Type u where
  sourceEvent : R.base.SourceEvent
  sourceOwnership :
    SourceOwnsResponsibilityIncidence R.base sourceEvent old
  renamedAt : R.RenameAt sourceEvent old.content renamed.content
  anchorTransport : SourceAnchorTransport old.sourceAnchor renamed.sourceAnchor
  incidence_eq : renamed.sourceIncidence = old.sourceIncidence
  lineage_eq : renamed.lineage = old.lineage

theorem RenameReceipt.sameDebtLineage
    {R : RestructuringVocabulary} {old renamed : R.Obligation}
    (receipt : RenameReceipt R old renamed) :
    SameDebtLineage old renamed :=
  receipt.lineage_eq.symm

/-- Reopen carries the archived lineage by construction; it is not a fresh
debt reset. -/
theorem NativeReopenPayload.sameDebtLineage
    {V : Vocabulary} {archive : TerminalArchive V}
    (payload : NativeReopenPayload V archive) :
    SameDebtLineage archive.obligation payload.admission.toObligation := by
  exact payload.lineage_eq.symm

/-- A transfer offer is navigation only.  Before acceptance it cannot rewrite
the bearer or discharge the obligation. -/
def transferOfferObservation
    {V : Vocabulary} (obligation : AdmittedObligation V)
    (_offer : V.TransferOfferSignal) : AdmittedObligation V :=
  obligation

theorem transferOffer_preserves_bearer
    {V : Vocabulary} (obligation : AdmittedObligation V)
    (offer : V.TransferOfferSignal) :
    (transferOfferObservation obligation offer).bearer = obligation.bearer := rfl

theorem transferOffer_preserves_lineage
    {V : Vocabulary} (obligation : AdmittedObligation V)
    (offer : V.TransferOfferSignal) :
    SameDebtLineage obligation (transferOfferObservation obligation offer) := rfl

/-- Accepted transfer changes the bearer but cannot terminate or reset the
obligation lineage. -/
theorem acceptedTransfer_preserves_lineage
    {V : Vocabulary} {obligation : AdmittedObligation V}
    {source : V.SourceEvent} {nextBearer : V.Bearer}
    (receipt : V.TransferAcceptedAt source obligation.bearer nextBearer
      obligation.scope) :
    SameDebtLineage obligation
      (ActiveCarryDisposition.transferred nextBearer receipt).target := rfl

/-- A family of descendants is the old-to-new half of the incidence ledger.
It is coverage-bearing and nonempty rather than a bare set membership. -/
structure DescendantFamily (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent) (parent : R.Obligation)
    (nextLive : List R.Obligation) : Type u where
  descendants : List R.Obligation
  sourceOwnership :
    SourceOwnsResponsibilityIncidence R.base sourceEvent parent
  nonempty : descendants ≠ []
  target_member : ∀ child, child ∈ descendants → child ∈ nextLive
  coverage : R.SplitCoverageAt sourceEvent parent.content
    (descendants.map AdmittedObligation.content)
  incidence : ∀ child, child ∈ descendants →
    R.DescendantAt sourceEvent parent.sourceIncidence parent.content
      child.sourceIncidence child.content
  anchorTransport : ∀ child, child ∈ descendants →
    SourceAnchorTransport parent.sourceAnchor child.sourceAnchor
  lineage : ∀ child, child ∈ descendants → SameDebtLineage parent child
  localDischarge : ∀ child, child ∈ descendants →
    R.LocalDischargePreservedAt sourceEvent parent.content child.content

/-- An old live obligation has exactly two legal destination shapes: a
coverage-bearing descendant family or an actual final receipt. -/
inductive OldObligationDestination (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent) (old : R.Obligation)
    (nextLive : List R.Obligation) : Type u
  | descendants (family : DescendantFamily R sourceEvent old nextLive)
  | terminal
      (ownership : SourceOwnsResponsibilityIncidence R.base sourceEvent old)
      (receipt : FinalReceipt R.base old sourceEvent)

/-- A new live obligation is either inherited through actual incidence or
generated by an actual admission payload. -/
inductive NewObligationOrigin (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent) (oldLive : List R.Obligation)
    (next : R.Obligation) : Type u
  | inherited
      (ancestor : R.Obligation)
      (ancestor_member : ancestor ∈ oldLive)
      (sourceOwnership :
        SourceOwnsResponsibilityIncidence R.base sourceEvent ancestor)
      (incidence : R.DescendantAt sourceEvent ancestor.sourceIncidence
        ancestor.content next.sourceIncidence next.content)
      (anchorTransport :
        SourceAnchorTransport ancestor.sourceAnchor next.sourceAnchor)
      (lineage : SameDebtLineage ancestor next)
      (localDischarge : R.LocalDischargePreservedAt sourceEvent
        ancestor.content next.content)
  | admitted
      (payload : NativeAdmissionPayload R.base)
      (source_eq : payload.sourceEvent = sourceEvent)
      (target_eq : payload.toObligation = next)

/-- Dependent two-sided ledger.  It is the structural consumer mouth for
no-silent-source and no-free-generation checks across split/merge networks. -/
structure IncidenceLedger (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent)
    (oldLive nextLive : List R.Obligation) : Type u where
  oldDestination : ∀ old, old ∈ oldLive →
    OldObligationDestination R sourceEvent old nextLive
  newOrigin : ∀ next, next ∈ nextLive →
    NewObligationOrigin R sourceEvent oldLive next
  compatible : ∀ old, (oldMember : old ∈ oldLive) →
    ∀ next, (nextMember : next ∈ nextLive) →
      (match oldDestination old oldMember with
        | .descendants family => next ∈ family.descendants
        | .terminal _ _ => False) ↔
      (match newOrigin next nextMember with
        | .inherited ancestor _ _ _ _ _ _ => ancestor = old
        | .admitted .. => False)

/-- A terminal sink is legal only when the exact lifecycle source event owns
the old responsibility incidence. -/
structure SourceOwnedFinalReceipt (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent) (old : R.Obligation) : Type u where
  ownership : SourceOwnsResponsibilityIncidence R.base sourceEvent old
  receipt : FinalReceipt R.base old sourceEvent

def IncidenceLedger.no_silent_old_sink
    {R : RestructuringVocabulary} {sourceEvent : R.base.SourceEvent}
    {oldLive nextLive : List R.Obligation}
    (ledger : IncidenceLedger R sourceEvent oldLive nextLive)
    {old : R.Obligation} (member : old ∈ oldLive) :
    (DescendantFamily R sourceEvent old nextLive) ⊕
      SourceOwnedFinalReceipt R sourceEvent old := by
  cases ledger.oldDestination old member with
  | descendants family => exact .inl family
  | terminal ownership receipt => exact .inr ⟨ownership, receipt⟩

/-- Type-valued inherited source, retaining local discharge incidence. -/
structure InheritedOrigin (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent) (oldLive : List R.Obligation)
    (next : R.Obligation) : Type u where
  ancestor : R.Obligation
  ancestor_member : ancestor ∈ oldLive
  sourceOwnership :
    SourceOwnsResponsibilityIncidence R.base sourceEvent ancestor
  incidence : R.DescendantAt sourceEvent ancestor.sourceIncidence
    ancestor.content next.sourceIncidence next.content
  anchorTransport :
    SourceAnchorTransport ancestor.sourceAnchor next.sourceAnchor
  lineage : SameDebtLineage ancestor next
  localDischarge : R.LocalDischargePreservedAt sourceEvent
    ancestor.content next.content

/-- Type-valued actual admission source for one exact target obligation. -/
structure ActualAdmissionOrigin (R : RestructuringVocabulary)
    (sourceEvent : R.base.SourceEvent) (next : R.Obligation) : Type u where
  payload : NativeAdmissionPayload R.base
  source_eq : payload.sourceEvent = sourceEvent
  target_eq : payload.toObligation = next

def IncidenceLedger.no_free_new_source
    {R : RestructuringVocabulary} {sourceEvent : R.base.SourceEvent}
    {oldLive nextLive : List R.Obligation}
    (ledger : IncidenceLedger R sourceEvent oldLive nextLive)
    {next : R.Obligation} (member : next ∈ nextLive) :
    InheritedOrigin R sourceEvent oldLive next ⊕
      ActualAdmissionOrigin R sourceEvent next := by
  cases ledger.newOrigin next member with
  | inherited ancestor ancestor_member sourceOwnership incidence
      anchorTransport lineage localDischarge =>
      exact .inl
        ⟨ancestor, ancestor_member, sourceOwnership, incidence,
          anchorTransport, lineage, localDischarge⟩
  | admitted payload source_eq target_eq =>
      exact .inr ⟨payload, source_eq, target_eq⟩

end ResponsibilityLifecycle
end SaturationMonoid

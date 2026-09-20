import H0mework.Foundation.Authority.CausalVisit
import H0mework.Foundation.Responsibility.Lineage

/-!
# Source-native ledger restructuring authority

Pairwise source/target certification does not by itself pay multiplicity.  A
one-to-many ledger can give every target an origin, and a many-to-one ledger
can give every source a destination, while neither direction carries the
coverage required by the responsibility-lineage kernel.

This module seals that seam without making ledger evolution bijective.  One
source-fixed restructuring law presents every world-ledger entry as an exact
lifecycle obligation.  The compiler then classifies every repeated origin or
destination as either literal identity or a source-generated split/merge
receipt.  Split receipts canonically induce the existing `DescendantFamily`;
each child also strictly spends the parent's progress budget, so lineage,
local discharge, complete child coverage, and finite-debit liveness travel
together.

The strong root below retains this certification as the image of the same
occurrence-local ledger compiler.  The generic ledger root remains a
pairwise compatibility/readout layer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle

universe u

/-- A split receipt already contains exactly the data required by the
old-to-new `DescendantFamily` ledger mouth. -/
def SplitReceipt.toDescendantFamily
    {R : RestructuringVocabulary.{u}} {parent : R.Obligation}
    (receipt : SplitReceipt R parent) :
    DescendantFamily R receipt.sourceEvent parent receipt.children where
  descendants := receipt.children
  sourceOwnership := receipt.sourceOwnership
  nonempty := receipt.children_nonempty
  target_member := fun _ member => member
  coverage := receipt.coverage
  incidence := receipt.descendant
  anchorTransport := receipt.anchorTransport
  lineage := receipt.lineage
  localDischarge := receipt.localDischarge

namespace LivingLawEvolution
namespace ConstructiveRoot

/-- Source-fixed presentation of world-ledger entries in one existing
responsibility restructuring vocabulary.

The key maps and commuting laws prevent a lifecycle receipt from describing
an unrelated obligation.  Injectivity prevents two distinct world entries
from being collapsed before split/merge coverage is checked. -/
structure SourceNativeLedgerRestructuringLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V) : Type (u + 1) where
  vocabulary : RestructuringVocabulary.{u}
  sourceEventAt :
    {current : V.Current} ->
      source.toRootSource.actual.OccurrenceAt current ->
      vocabulary.base.SourceEvent
  obligationAt :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      {support : N.Support} ->
      OpenResponsibilityAt N support -> vocabulary.Obligation
  responsibilityKey : vocabulary.Obligation -> N.Responsibility
  anchorKey : vocabulary.base.SourceObservation.Carrier -> N.Anchor
  incidenceKey : vocabulary.base.Incidence -> N.Incidence
  lineageKey : vocabulary.base.Lineage -> N.Lineage
  responsibility_commutes :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      {support : N.Support} ->
      (entry : OpenResponsibilityAt N support) ->
      responsibilityKey (obligationAt occurrence entry) = entry.1
  anchor_commutes :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      {support : N.Support} ->
      (entry : OpenResponsibilityAt N support) ->
      anchorKey (obligationAt occurrence entry).sourceAnchor.identity =
        N.anchorAt support
  incidence_commutes :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      {support : N.Support} ->
      (entry : OpenResponsibilityAt N support) ->
      incidenceKey (obligationAt occurrence entry).sourceIncidence =
        N.incidenceAt support
  lineage_commutes :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      {support : N.Support} ->
      (entry : OpenResponsibilityAt N support) ->
      lineageKey (obligationAt occurrence entry).lineage =
        N.lineageAt support
  obligationAt_injective :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      {support : N.Support} ->
      Function.Injective (obligationAt occurrence (support := support))

/-! ## Canonical identity-only world-ledger presentation -/

/-- The standard O0 carrier used to present a world anchor inside the
responsibility lifecycle.  The Boolean coordinate is only the compulsory
complement orbit; the world anchor remains the source identity. -/
private def worldLedgerComplementObservation
    {N : WorldRelationNetwork.{u}} (defaultAnchor : N.Anchor) :
    ComplementObservation.ComplementObservationCarrier.{u} where
  Carrier := N.Anchor × Bool
  null := (defaultAnchor, false)
  complement := fun point => (point.1, !point.2)
  complement_involutive := by
    rintro ⟨anchor, bit⟩
    cases bit <;> rfl
  null_ne_complement_null := by
    intro equality
    exact Bool.noConfusion (congrArg Prod.snd equality)

/-- Proof-relevant scope seal in the ambient universe.  It carries no choice:
the sole constructor exists only at the exact source support. -/
private inductive WorldLedgerScopeIdentityAt
    {N : WorldRelationNetwork.{u}} (source : N.Support) :
    N.Support -> Type u
  | exact : WorldLedgerScopeIdentityAt source source

/-- Canonical lifecycle vocabulary for a world ledger.  Split and merge
coverage are intentionally empty: this vocabulary authorizes only literal
identity classifications.  Admission is not a `PUnit` privilege: commitment
and discharge jurisdiction are the exact existing `OpenAt` witness, while
scope is the source support itself.  A non-injective compiler must install
its own source-generated restructuring vocabulary and receipts. -/
private def identityOnlyWorldLedgerRestructuringVocabulary
    (N : WorldRelationNetwork.{u}) (defaultAnchor : N.Anchor) :
    RestructuringVocabulary.{u} where
  base := {
    SourceEvent := N.Support
    Content := N.Responsibility
    Residual := PUnit
    Bearer := PUnit
    ProtectedInterest := PUnit
    Scope := N.Support
    Lineage := N.Lineage
    Incidence := N.Incidence
    SourceObservation := worldLedgerComplementObservation defaultAnchor
    sourceAnchor := fun support => {
      identity := (N.anchorAt support, false)
      identity_ne_complement_identity := by
        intro equality
        exact Bool.noConfusion (congrArg Prod.snd equality)
      scope := support
      lineage := N.lineageAt support }
    sourceIncidence := N.incidenceAt
    ObstructionAt := fun _ => PEmpty
    demandContent := fun {_} obstruction => nomatch obstruction
    demandResidual := fun {_} obstruction => nomatch obstruction
    CommitmentAt := fun support responsibility =>
      N.OpenAt support responsibility
    MandateOriginAt := fun _ _ => PEmpty
    AcceptedTaskAt := fun _ _ => PEmpty
    ActiveDependencyAt := fun _ _ => PEmpty
    ProtectedRiskAt := fun _ _ => PEmpty
    AdmissionAuthorityAt := WorldLedgerScopeIdentityAt
    AcceptedAt := fun _ => WorldLedgerScopeIdentityAt
    StandingMandateAt := fun _ _ _ => PEmpty
    DischargeJurisdiction := fun responsibility scope =>
      N.OpenAt scope responsibility
    ProgressAt := fun _ _ _ _ => PEmpty
    MaintenanceAt := fun _ _ _ => PEmpty
    TypedDeferAt := fun _ _ _ => PEmpty
    ScopeNarrowingAt := fun _ _ _ => PEmpty
    TransferAcceptedAt := fun _ _ _ _ => PEmpty
    FulfilledAt := fun _ _ _ => PEmpty
    WaivedAt := fun _ _ _ => PEmpty
    InvalidatedAt := fun _ _ _ => PEmpty
    AbandonedAt := fun _ _ _ => PEmpty
    ImpossibleResidueAcceptedAt := fun _ _ _ => PEmpty
    SupersessionAt := fun _ _ _ _ _ _ _ => PEmpty
    ReopenAt := fun _ _ _ _ _ _ _ => PEmpty
    JurisdictionEndedAt := fun _ _ _ => PEmpty
    ConsentRevokedAt := fun _ _ _ => PEmpty
    CapacityReleasedAt := fun _ _ _ => PEmpty
    UpperRouteAt := fun _ _ _ => PEmpty
    NextActorSignal := PEmpty
    AgeSignal := PEmpty
    TransferOfferSignal := PEmpty }
  DescendantAt := fun _ _ _ _ _ => PEmpty
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ _ _ => PEmpty
  RenameAt := fun _ _ _ => PEmpty

/-- Canonical admitted obligation corresponding to one open world-ledger
entry.  No restructuring receipt is minted here. -/
private def identityOnlyWorldLedgerObligationAt
    {N : WorldRelationNetwork.{u}} (defaultAnchor : N.Anchor)
    {support : N.Support} (entry : OpenResponsibilityAt N support) :
    (identityOnlyWorldLedgerRestructuringVocabulary N defaultAnchor).Obligation :=
  ({ sourceEvent := support
     content := entry.1
     residual := PUnit.unit
     bearer := PUnit.unit
     beneficiary := PUnit.unit
     scope := support
     lineage := N.lineageAt support
     anchor_scope_eq := rfl
     anchor_lineage_eq := rfl
     origin := .explicitCommitment entry.2
     authority := .exact
     assumption := .accepted .exact
     dischargeJurisdiction := entry.2 } :
    NativeAdmissionPayload
      (identityOnlyWorldLedgerRestructuringVocabulary N defaultAnchor).base).toObligation

/-- Source-fixed identity-only restructuring law.  Proof relevance in
`OpenAt` is retained: callers must show that one exact world responsibility
does not acquire multiple open-entry identities merely through proof data. -/
def identityOnlyWorldLedgerRestructuringLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (defaultAnchor : N.Anchor)
    (openAt_subsingleton :
      (support : N.Support) -> (responsibility : N.Responsibility) ->
        Subsingleton (N.OpenAt support responsibility)) :
    SourceNativeLedgerRestructuringLaw source where
  vocabulary := identityOnlyWorldLedgerRestructuringVocabulary N defaultAnchor
  sourceEventAt := fun occurrence => occurrence.1
  obligationAt := by
    intro current occurrence support entry
    exact identityOnlyWorldLedgerObligationAt defaultAnchor entry
  responsibilityKey := AdmittedObligation.content
  anchorKey := Prod.fst
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by
    intro current occurrence support entry
    rfl
  anchor_commutes := by
    intro current occurrence support entry
    rfl
  incidence_commutes := by
    intro current occurrence support entry
    rfl
  lineage_commutes := by
    intro current occurrence support entry
    rfl
  obligationAt_injective := by
    intro current occurrence support left right obligation_eq
    rcases left with ⟨left, leftOpen⟩
    rcases right with ⟨right, rightOpen⟩
    have responsibility_eq : left = right :=
      congrArg AdmittedObligation.content obligation_eq
    cases responsibility_eq
    have open_eq : leftOpen = rightOpen :=
      (openAt_subsingleton support left).elim _ _
    cases open_eq
    rfl

/-- The identity-only adapter's commitment fibre is exactly the existing
world-ledger `OpenAt` fibre.  Its remaining `PUnit` fields carry no admission
authority and cannot create a responsibility absent from the root ledger. -/
def identityOnlyWorldLedgerCommitmentPresentation
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (defaultAnchor : N.Anchor)
    (openAt_subsingleton :
      (support : N.Support) -> (responsibility : N.Responsibility) ->
        Subsingleton (N.OpenAt support responsibility))
    (support : N.Support) (responsibility : N.Responsibility) :
    ConstructivePresentation
      ((identityOnlyWorldLedgerRestructuringLaw source defaultAnchor
        openAt_subsingleton).vocabulary.base.CommitmentAt
          support responsibility)
      (N.OpenAt support responsibility) :=
  ConstructivePresentation.refl _

/-- Discharge jurisdiction in the identity-only adapter is likewise the
same exact open world row, not an inhabited lifecycle token. -/
def identityOnlyWorldLedgerDischargePresentation
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (defaultAnchor : N.Anchor)
    (openAt_subsingleton :
      (support : N.Support) -> (responsibility : N.Responsibility) ->
        Subsingleton (N.OpenAt support responsibility))
    (support : N.Support) (responsibility : N.Responsibility) :
    ConstructivePresentation
      ((identityOnlyWorldLedgerRestructuringLaw source defaultAnchor
        openAt_subsingleton).vocabulary.base.DischargeJurisdiction
          responsibility support)
      (N.OpenAt support responsibility) :=
  ConstructivePresentation.refl _

/-- Exact coverage of one repeated origin.  The split receipt's child list is
required to cover precisely the target entries carrying that origin; phantom
children and uncovered siblings are both excluded.  Every child strictly
spends the common parent's progress budget.  Otherwise one finite renewal
capacity could be cloned into arbitrarily many independently reusable rows. -/
structure SourceNativeSplitCoverageAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger)
    (left right : targetLedger.Entry)
    (origin_eq : (evolution.origin left).1 =
      (evolution.origin right).1) : Type u where
  private mk ::
  receipt : SplitReceipt law.vocabulary
    (law.obligationAt occurrence (evolution.origin left).1)
  sourceEvent_eq : receipt.sourceEvent = law.sourceEventAt occurrence
  left_member : law.obligationAt occurrence left ∈ receipt.children
  right_member : law.obligationAt occurrence right ∈ receipt.children
  covers_target : (targetEntry : targetLedger.Entry) ->
    (evolution.origin targetEntry).1 = (evolution.origin left).1 ->
    law.obligationAt occurrence targetEntry ∈ receipt.children
  childProgressBudget_strictlyDebited :
    (targetEntry : targetLedger.Entry) ->
    (evolution.origin targetEntry).1 = (evolution.origin left).1 ->
    targetEntry.progressBudget <
      (evolution.origin left).1.progressBudget
  no_phantom_child : (child : law.vocabulary.Obligation) ->
    child ∈ receipt.children ->
    { targetEntry : targetLedger.Entry //
      (law.obligationAt occurrence targetEntry = child) ∧
        ((evolution.origin targetEntry).1 =
          (evolution.origin left).1) }

/-- Install an occurrence-generated split receipt together with its exact
target-ledger coverage. -/
def SourceNativeSplitCoverageAt.ofReceipt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger}
    {left right : targetLedger.Entry}
    {origin_eq : (evolution.origin left).1 =
      (evolution.origin right).1}
    (receipt : SplitReceipt law.vocabulary
      (law.obligationAt occurrence (evolution.origin left).1))
    (sourceEvent_eq : receipt.sourceEvent = law.sourceEventAt occurrence)
    (left_member : law.obligationAt occurrence left ∈ receipt.children)
    (right_member : law.obligationAt occurrence right ∈ receipt.children)
    (covers_target : (targetEntry : targetLedger.Entry) ->
      (evolution.origin targetEntry).1 = (evolution.origin left).1 ->
      law.obligationAt occurrence targetEntry ∈ receipt.children)
    (childProgressBudget_strictlyDebited :
      (targetEntry : targetLedger.Entry) ->
      (evolution.origin targetEntry).1 = (evolution.origin left).1 ->
      targetEntry.progressBudget <
        (evolution.origin left).1.progressBudget)
    (no_phantom_child : (child : law.vocabulary.Obligation) ->
      child ∈ receipt.children ->
      { targetEntry : targetLedger.Entry //
        (law.obligationAt occurrence targetEntry = child) ∧
          ((evolution.origin targetEntry).1 =
            (evolution.origin left).1) }) :
    SourceNativeSplitCoverageAt law occurrence evolution
      left right origin_eq :=
  ⟨receipt, sourceEvent_eq, left_member, right_member, covers_target,
    childProgressBudget_strictlyDebited, no_phantom_child⟩

/-- A zero-budget parent cannot acquire split authority.  It must settle,
transfer, or obtain a new source-generated incidence instead. -/
theorem SourceNativeSplitCoverageAt.parentProgressBudget_positive
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger}
    {left right : targetLedger.Entry}
    {origin_eq : (evolution.origin left).1 =
      (evolution.origin right).1}
    (coverage : SourceNativeSplitCoverageAt law occurrence evolution
      left right origin_eq) :
    0 < (evolution.origin left).1.progressBudget :=
  Nat.lt_of_le_of_lt (Nat.zero_le left.progressBudget)
    (coverage.childProgressBudget_strictlyDebited left rfl)

/-- The exact split coverage exposes the lineage kernel's canonical
descendant family; callers do not submit a second family. -/
def SourceNativeSplitCoverageAt.descendantFamily
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger}
    {left right : targetLedger.Entry}
    {origin_eq : (evolution.origin left).1 =
      (evolution.origin right).1}
    (coverage : SourceNativeSplitCoverageAt law occurrence evolution
      left right origin_eq) :
    DescendantFamily law.vocabulary coverage.receipt.sourceEvent
      (law.obligationAt occurrence (evolution.origin left).1)
      coverage.receipt.children :=
  coverage.receipt.toDescendantFamily

/-- Exact coverage of one repeated destination.  The merge receipt's parent
list is required to cover precisely the source entries paying that target. -/
structure SourceNativeMergeCoverageAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger)
    (left right : sourceLedger.Entry)
    (destination_eq : (evolution.destination left).1 =
      (evolution.destination right).1) : Type u where
  private mk ::
  receipt : MergeReceipt law.vocabulary
  sourceEvent_eq : receipt.sourceEvent = law.sourceEventAt occurrence
  target_eq : receipt.target =
    law.obligationAt occurrence (evolution.destination left).1
  left_member : law.obligationAt occurrence left ∈ receipt.parents
  right_member : law.obligationAt occurrence right ∈ receipt.parents
  covers_source : (sourceEntry : sourceLedger.Entry) ->
    (evolution.destination sourceEntry).1 =
      (evolution.destination left).1 ->
    law.obligationAt occurrence sourceEntry ∈ receipt.parents
  no_phantom_parent : (parent : law.vocabulary.Obligation) ->
    parent ∈ receipt.parents ->
    { sourceEntry : sourceLedger.Entry //
      (law.obligationAt occurrence sourceEntry = parent) ∧
        ((evolution.destination sourceEntry).1 =
          (evolution.destination left).1) }

/-- Install an occurrence-generated merge receipt together with its exact
source-ledger coverage. -/
def SourceNativeMergeCoverageAt.ofReceipt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger}
    {left right : sourceLedger.Entry}
    {destination_eq : (evolution.destination left).1 =
      (evolution.destination right).1}
    (receipt : MergeReceipt law.vocabulary)
    (sourceEvent_eq : receipt.sourceEvent = law.sourceEventAt occurrence)
    (target_eq : receipt.target =
      law.obligationAt occurrence (evolution.destination left).1)
    (left_member : law.obligationAt occurrence left ∈ receipt.parents)
    (right_member : law.obligationAt occurrence right ∈ receipt.parents)
    (covers_source : (sourceEntry : sourceLedger.Entry) ->
      (evolution.destination sourceEntry).1 =
        (evolution.destination left).1 ->
      law.obligationAt occurrence sourceEntry ∈ receipt.parents)
    (no_phantom_parent : (parent : law.vocabulary.Obligation) ->
      parent ∈ receipt.parents ->
      { sourceEntry : sourceLedger.Entry //
        (law.obligationAt occurrence sourceEntry = parent) ∧
          ((evolution.destination sourceEntry).1 =
            (evolution.destination left).1) }) :
    SourceNativeMergeCoverageAt law occurrence evolution
      left right destination_eq :=
  ⟨receipt, sourceEvent_eq, target_eq, left_member, right_member,
    covers_source, no_phantom_parent⟩

/-- A repeated origin is either definitionally the same target entry or an
actual split with coverage. -/
inductive SourceNativeSplitClassificationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger)
    (left right : targetLedger.Entry)
    (origin_eq : (evolution.origin left).1 =
      (evolution.origin right).1) : Type u
  | identity (target_eq : left = right)
  | split
      (coverage : SourceNativeSplitCoverageAt law occurrence evolution
        left right origin_eq)

/-- A repeated destination is either definitionally the same source entry or
an actual merge with coverage. -/
inductive SourceNativeMergeClassificationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger)
    (left right : sourceLedger.Entry)
    (destination_eq : (evolution.destination left).1 =
      (evolution.destination right).1) : Type u
  | identity (source_eq : left = right)
  | merge
      (coverage : SourceNativeMergeCoverageAt law occurrence evolution
        left right destination_eq)

/-- The same whole-ledger evolution must classify every non-injective origin
and destination through the source-fixed restructuring law. -/
structure ExactLedgerRestructuringCertificationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    (evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger) : Type u where
  split : (left right : targetLedger.Entry) ->
    (origin_eq : (evolution.origin left).1 =
      (evolution.origin right).1) ->
    SourceNativeSplitClassificationAt law occurrence evolution
      left right origin_eq
  merge : (left right : sourceLedger.Entry) ->
    (destination_eq : (evolution.destination left).1 =
      (evolution.destination right).1) ->
    SourceNativeMergeClassificationAt law occurrence evolution
      left right destination_eq

namespace ExactLedgerRestructuringCertificationAt

/-- An exact ledger map which is injective in both directions requires no
split/merge receipt: every repeated origin or destination is literal entry
identity.  This is the only automatic constructor for the identity-only
restructuring vocabulary. -/
def ofInjective
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {sourceLedger targetLedger : CompleteLiveLedgerAt N}
    {evolution : LedgerWriteEvolutionAt N sourceLedger targetLedger}
    (origin_injective : Function.Injective
      (fun target : targetLedger.Entry => (evolution.origin target).1))
    (destination_injective : Function.Injective
      (fun source : sourceLedger.Entry => (evolution.destination source).1)) :
    ExactLedgerRestructuringCertificationAt law occurrence evolution where
  split := fun _left _right origin_eq =>
    .identity (origin_injective origin_eq)
  merge := fun _left _right destination_eq =>
    .identity (destination_injective destination_eq)

end ExactLedgerRestructuringCertificationAt

/-- Restructuring certification for the exact local compiler branch.
Terminal has no successor ledger and therefore no split/merge classification. -/
def SourceNativeLedgerRestructuringCertificationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) : Type u :=
  match generated with
  | .nativeWrite _ _ _ evolution =>
      ExactLedgerRestructuringCertificationAt law occurrence evolution
  | .relationWrite _ _ _ evolution =>
      ExactLedgerRestructuringCertificationAt law occurrence evolution
  | .continuedTransport _ _ _ evolution =>
      ExactLedgerRestructuringCertificationAt law occurrence evolution
  | .borromeanRedirect _ _ _ evolution =>
      ExactLedgerRestructuringCertificationAt law occurrence evolution
  | .faithfulTerminal .. => PUnit

/-- Source-owned compiler with pairwise incidence/lineage certification and
non-injective restructuring certification generated from the same occurrence. -/
structure SourceNativeRestructuringLedgerCompiler
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V) : Type (u + 1) where
  ledgerCompiler : SourceNativeLedgerCompiler source
  restructuringLaw : SourceNativeLedgerRestructuringLaw source
  certifyRestructuring :
    {current : V.Current} ->
      (occurrence : source.toRootSource.actual.OccurrenceAt current) ->
      SourceNativeLedgerRestructuringCertificationAt restructuringLaw
        (ledgerCompiler.compile occurrence)

/-- Complete source identity including the restructuring compiler. -/
structure SourceNativeRestructuringLedgerSource
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  source : SourceNativeSource N V
  compiler : SourceNativeRestructuringLedgerCompiler source

/-- Forget restructuring authority while retaining the exact pairwise ledger
compiler. -/
def SourceNativeRestructuringLedgerSource.toLedgerSource
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeRestructuringLedgerSource N V) :
    SourceNativeLedgerSource N V where
  source := source.source
  ledgerCompiler := source.compiler.ledgerCompiler

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

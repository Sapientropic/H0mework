import H0mework.Foundation.Authority.SourceProjectionInventory
import H0mework.Foundation.Runtime.AnswerHistory

/-!
# Source-native causal-entry authority

A complete authoritative or living root generates causal responsibility
authority from its exact initial/cofinal ledger row and preserves it through
canonical whole-ledger successors.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-! ## Causal representation of the fixed root compiler -/

/-- Causal responsibility authority retaining the complete authoritative root.

The root's native source, whole-ledger compiler, projection inventory, and
emitter remain in the type index.  Public producers derive its private token
from canonical initial/cofinal rows and whole-ledger successors. -/
structure SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) : Type (u + 1) where
  private mk ::
  private ledgerReadout : SourceNativeTemporalCausalEntryLedgerReadoutAt
    root.toLedgerRoot visit entry

namespace SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt

/-- One-way ledger-history readout. -/
def toLedgerReadout
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      root visit entry) :
    SourceNativeTemporalCausalEntryLedgerReadoutAt root.toLedgerRoot visit entry :=
  authority.ledgerReadout

/-- Generate authoritative-root identity from its own initial admission and
canonical finite history. -/
def generatedFromInitial?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)
    (initialEntry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted root.toRoot.source.initial))) :
    {current : V.Current} ->
    (history : root.toRoot.ReachableAt current) ->
      Option (Sigma fun entry : OpenResponsibilityAt N
          (root.toLedgerRoot.source.source.toRootSource.account.supportOf
            (root.emitted current)) =>
        SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt root
          (.finite ⟨current, history⟩) entry) := by
  intro current history
  match root.toLedgerRoot
      |>.generatedTemporalCausalEntryFromInitial? initialEntry history with
  | none => exact none
  | some ⟨entry, authority⟩ => exact some ⟨entry, ⟨authority⟩⟩

/-- Exact initial-row constructor for the fixed authoritative root. -/
def generatedFromInitialRow
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)
    (entry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted root.toRoot.source.initial)))
    (row : (root.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toRoot.initialVisit)).GeneratedEntryRowAt entry) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt root
      (.finite root.toRoot.initialVisit) entry :=
  ⟨.initialAdmission entry row⟩

/-- Generate authoritative-root identity from an exact cofinal admission row. -/
def generatedFromCofinal?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) :
    Option (SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt root
      (.cofinal visit) entry) :=
  match (root.toLedgerRoot.generatedAtTemporalVisit (.cofinal visit))
      |>.canonicalGeneratedEntryRow? entry with
  | none => none
  | some row => some ⟨.cofinalAdmission row⟩

/-- Exact cofinal row constructor.  The row is already indexed by this root's
emitted occurrence and temporal compiler image; no erased causal token enters
the authoritative mouth. -/
def generatedFromCofinalRow
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)
    (visit : SourceNativeCofinalVisitAt root.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (row : (root.toLedgerRoot.generatedAtTemporalVisit (.cofinal visit))
      |>.GeneratedEntryRowAt entry) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt root
      (.cofinal visit) entry :=
  ⟨.cofinalAdmission row⟩

/-- Preserve the complete authoritative-root identity through the canonical
whole-ledger successor. -/
def next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      root visit entry)
    {next : V.Current}
    (next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? = some next) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt root
      (visit.next next_eq)
      (root.toLedgerRoot.canonicalTargetEntryAtNext next_eq entry) :=
  ⟨authority.ledgerReadout.next next_eq⟩

end SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt

/-- Causal responsibility authority retaining the complete living source.

The underlying responsibility history is still generated by the sole ledger
root.  This wrapper prevents a subsystem from erasing the complete projection
inventory, reusing the same ledger token in a sibling source law, and then
claiming that the sibling projection was always part of the original world.
Its constructor is private; authority enters only through source-generated
initial/cofinal admission and remains sealed through canonical successors. -/
structure SourceNativeLivingTemporalCausalEntryAuthorityAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) : Type (u + 1) where
  private mk ::
  private authoritativeAuthority :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      root.toAuthoritativeRoot visit entry

namespace SourceNativeLivingTemporalCausalEntryAuthorityAt

/-- Ledger-history readout.  It may feed root-ledger consumers, but there is no
inverse public constructor from an erased ledger token back to full-source
authority. -/
def toLedgerReadout
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry) :
    SourceNativeTemporalCausalEntryLedgerReadoutAt
      root.toAuthoritativeRoot.toLedgerRoot visit entry :=
  authority.authoritativeAuthority.toLedgerReadout

/-- One-way authoritative-root readout.  There is no public inverse capable of
adding a terminal-handoff law after the causal event. -/
def toAuthoritativeAuthority
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      root.toAuthoritativeRoot visit entry :=
  authority.authoritativeAuthority

/-- Generate full-source authority from the fixed root's initial admission and
canonical finite history. -/
def generatedFromInitial?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (initialEntry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted root.toAuthoritativeRoot.toRoot.source.initial))) :
    {current : V.Current} →
    (history : root.toAuthoritativeRoot.toRoot.ReachableAt current) →
      Option (Sigma fun entry : OpenResponsibilityAt N
          (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
            (root.emitted current)) =>
        SourceNativeLivingTemporalCausalEntryAuthorityAt root
          (.finite ⟨current, history⟩) entry) := by
  intro current history
  match SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromInitial?
      root.toAuthoritativeRoot initialEntry history with
  | none => exact none
  | some ⟨entry, authority⟩ => exact some ⟨entry, ⟨authority⟩⟩

/-- Exact initial-row constructor retaining the terminal-handoff source law. -/
def generatedFromInitialRow
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted root.toAuthoritativeRoot.toRoot.source.initial)))
    (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit))
        |>.GeneratedEntryRowAt entry) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit) entry :=
  ⟨SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    root.toAuthoritativeRoot entry row⟩

/-- Generate full-source authority from an exact cofinal admission row. -/
def generatedFromCofinal?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) :
    Option (SourceNativeLivingTemporalCausalEntryAuthorityAt root
      (.cofinal visit) entry) :=
  match SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromCofinal?
      root.toAuthoritativeRoot visit entry with
  | none => none
  | some authority => some ⟨authority⟩

/-- Exact cofinal-row constructor retaining the terminal-handoff source law. -/
def generatedFromCofinalRow
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (row : (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal visit)).GeneratedEntryRowAt entry) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root
      (.cofinal visit) entry :=
  ⟨SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromCofinalRow
    root.toAuthoritativeRoot visit entry row⟩

/-- The canonical whole-ledger successor preserves the complete living source
identity together with the admitted responsibility. -/
def next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry)
    {next : V.Current}
    (next_eq :
      (root.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? =
        some next) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root (visit.next next_eq)
      (root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
        next_eq entry) :=
  ⟨authority.authoritativeAuthority.next next_eq⟩

end SourceNativeLivingTemporalCausalEntryAuthorityAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

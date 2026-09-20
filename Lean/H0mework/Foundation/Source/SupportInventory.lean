import H0mework.Foundation.Source.Root

/-!
# Source-native support and responsibility inventory for constructive roots

`CompleteLiveLedgerAt` is complete once a world support is fixed.  This module
closes the earlier registration seam: an exact lower event is indexed by its
support before it becomes a root occurrence, and the same source law presents
that event's affected-incidence inventory as the complete open-responsibility
fibre at that support.

The adapter derives `RootOccurrenceAccount.supportOf` from the sigma event's
support index.  A later account cannot route the same event payload to a
sibling support.  Changing the support-indexed event family or its inventory
presentation therefore changes the source law rather than presenting the same
source occurrence differently.

This is a constructive source-recognition kernel.  It does not manufacture a
domain event, decide which responsibilities are affected, or import Mathlib's
algebraic/path infrastructure.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- One source-owned event algebra whose primitive event is already indexed
by its exact world support.  `AffectedInventoryAt` is source-native data; its
presentation identifies the whole root ledger at that event, rather than one
caller-selected responsibility. -/
structure SourceNativeEventAlgebra
    (N : WorldRelationNetwork.{u})
    (V : Vocabulary.{u}) : Type (u + 1) where
  EventAt : (current : V.Current) → N.Support → Type u
  compile : {current : V.Current} → {support : N.Support} →
    EventAt current support → EvolutionAt V current
  AffectedInventoryAt : {current : V.Current} → {support : N.Support} →
    EventAt current support → Type u
  affectedInventoryPresentation :
    {current : V.Current} → {support : N.Support} →
      (event : EventAt current support) →
      ConstructivePresentation (AffectedInventoryAt event)
        (OpenResponsibilityAt N support)
  anchorKey : V.Anchor → N.Anchor
  incidenceKey : V.Incidence → N.Incidence
  lineageKey : V.Lineage → N.Lineage
  anchor_commutes :
    {current : V.Current} → {support : N.Support} →
      (event : EventAt current support) →
      anchorKey (V.anchorAt current) = N.anchorAt support
  incidence_commutes :
    {current : V.Current} → {support : N.Support} →
      (event : EventAt current support) →
      incidenceKey (V.incidenceAt current) = N.incidenceAt support
  lineage_commutes :
    {current : V.Current} → {support : N.Support} →
      (event : EventAt current support) →
      lineageKey (V.lineageAt current) = N.lineageAt support

/-- Exact root occurrence of a source-native event algebra.  Support is part
of event identity, not a later account projection. -/
abbrev SourceNativeEventAlgebra.OccurrenceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (law : SourceNativeEventAlgebra N V) (current : V.Current) : Type u :=
  Sigma fun support => law.EventAt current support

/-- Forget only the source-native support/inventory interface.  The generated
evolution still consumes the exact support-indexed event. -/
def SourceNativeEventAlgebra.toActual
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (law : SourceNativeEventAlgebra N V) : ActualEventAlgebra V where
  OccurrenceAt := law.OccurrenceAt
  compile := fun occurrence => law.compile occurrence.2

/-- Root account canonically derived from the support-indexed event.  There is
no `supportOf` argument at this adapter boundary. -/
def SourceNativeEventAlgebra.toRootAccount
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (law : SourceNativeEventAlgebra N V) :
    RootOccurrenceAccount N law.toActual where
  supportOf := Sigma.fst
  anchorKey := law.anchorKey
  incidenceKey := law.incidenceKey
  lineageKey := law.lineageKey
  anchor_commutes := fun occurrence => law.anchor_commutes occurrence.2
  incidence_commutes := fun occurrence => law.incidence_commutes occurrence.2
  lineage_commutes := fun occurrence => law.lineage_commutes occurrence.2

/-- All source-native occurrences across currents, retaining both the current
and the support-indexed event identity. -/
abbrev SourceNativeEventAlgebra.ChartOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (law : SourceNativeEventAlgebra N V) : Type u :=
  Sigma law.OccurrenceAt

/-- Canonical U6 occurrence chart of the source-native event law.  Existing
shared-support transport can therefore consume the exact affected inventory
without rebuilding or selecting another responsibility presentation. -/
def SourceNativeEventAlgebra.toOccurrenceChart
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (law : SourceNativeEventAlgebra N V) : OccurrenceChart N where
  Occurrence := law.ChartOccurrence
  LocalAnchor := V.Anchor
  LocalIncidence := V.Incidence
  LocalLineage := V.Lineage
  supportOf := fun occurrence => occurrence.2.1
  anchorAt := fun occurrence => V.anchorAt occurrence.1
  incidenceAt := fun occurrence => V.incidenceAt occurrence.1
  lineageAt := fun occurrence => V.lineageAt occurrence.1
  anchorKey := law.anchorKey
  incidenceKey := law.incidenceKey
  lineageKey := law.lineageKey
  ResponsibilityAt := fun occurrence =>
    law.AffectedInventoryAt occurrence.2.2
  responsibilityPresentation := fun occurrence =>
    law.affectedInventoryPresentation occurrence.2.2
  anchor_commutes := fun occurrence => law.anchor_commutes occurrence.2.2
  incidence_commutes := fun occurrence =>
    law.incidence_commutes occurrence.2.2
  lineage_commutes := fun occurrence => law.lineage_commutes occurrence.2.2

/-- Complete source identity for a source-native support/inventory law. -/
structure SourceNativeSource
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  initial : V.Current
  law : SourceNativeEventAlgebra N V

/-- Canonical embedding into the existing constructive root source. -/
def SourceNativeSource.toRootSource
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V) : Source N V where
  initial := source.initial
  actual := source.law.toActual
  account := source.law.toRootAccount

/-- A constructive root whose raw world emits only events of one fixed
source-native support/inventory law. -/
structure SourceNativeRootClosure
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  source : SourceNativeSource N V
  emitted : (current : V.Current) →
    source.toRootSource.actual.OccurrenceAt current

/-- Forget the additional source-native inventory interface. -/
def SourceNativeRootClosure.toRoot
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) : RootClosure N V where
  source := root.source.toRootSource
  emitted := root.emitted

/-- Root support is definitionally the support carried by the emitted lower
event.  No post-event account can choose another support. -/
@[simp] theorem SourceNativeRootClosure.supportAt_eq_emitted_support
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) (current : V.Current) :
    root.toRoot.supportAt current =
      (root.emitted current).1 :=
  rfl

/-- The source-native affected-incidence inventory presents the complete root
ledger at the same exact occurrence. -/
def SourceNativeRootClosure.affectedInventoryPresentation
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) (current : V.Current) :
    let occurrence := root.emitted current
    ConstructivePresentation
      (root.source.law.AffectedInventoryAt occurrence.2)
      (root.toRoot.ledgerAt current).Entry := by
  dsimp only
  exact root.source.law.affectedInventoryPresentation
    (root.emitted current).2

/-- Every complete-ledger entry is recovered after presenting it in the
source-native affected inventory and returning to the root ledger. -/
theorem SourceNativeRootClosure.affectedInventory_forward_backward
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) (current : V.Current)
    (entry : (root.toRoot.ledgerAt current).Entry) :
    (root.affectedInventoryPresentation current).forward
        ((root.affectedInventoryPresentation current).backward entry) =
      entry :=
  (root.affectedInventoryPresentation current).forward_backward entry

/-- Every source-native affected-incidence value is recovered after entering
the complete root ledger and returning to the source inventory. -/
theorem SourceNativeRootClosure.affectedInventory_backward_forward
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) (current : V.Current)
    (affected : root.source.law.AffectedInventoryAt
      (root.emitted current).2) :
    (root.affectedInventoryPresentation current).backward
        ((root.affectedInventoryPresentation current).forward affected) =
      affected :=
  (root.affectedInventoryPresentation current).backward_forward affected

/-- A source may use a subsingleton affected inventory only when the complete
root ledger at that exact event is itself subsingleton.  The presentation
cannot erase a sibling responsibility row and still claim completeness. -/
theorem SourceNativeRootClosure.completeLedger_subsingleton_of_affectedInventory
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) (current : V.Current)
    [Subsingleton (root.source.law.AffectedInventoryAt
      (root.emitted current).2)] :
    Subsingleton (root.toRoot.ledgerAt current).Entry :=
  (root.affectedInventoryPresentation current).subsingleton_target

/-- Conversely, a complete subsingleton root ledger cannot conceal multiple
source-native affected-incidence values behind its presentation. -/
theorem SourceNativeRootClosure.affectedInventory_subsingleton_of_completeLedger
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeRootClosure N V) (current : V.Current)
    [Subsingleton (root.toRoot.ledgerAt current).Entry] :
    Subsingleton (root.source.law.AffectedInventoryAt
      (root.emitted current).2) :=
  (root.affectedInventoryPresentation current).subsingleton_source

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

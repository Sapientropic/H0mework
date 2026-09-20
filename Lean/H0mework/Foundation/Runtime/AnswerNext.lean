import H0mework.Foundation.Cofinal.ProductiveHistory
import H0mework.Foundation.Authority.SourceProjectionInventory

/-!
# Root occurrences answer and generate the next current

The five constructors of `EvolutionAt` classify how one fixed root/law surface
pays for an occurrence.  They are not six terminal outcomes for the world.
This kernel fixes the complete living source identity and its pre-emitter
terminal-handoff law.  The sole execution interface lives in
`LivingLawRootTemporalAnswerNextKernel`:

```text
actual root occurrence -> canonical typed answer -> source-generated next current
```

For ordinary writes, transport, redirect, and law-surface extension, that
compiler uses the canonical target already emitted by the root.  A
`faithfulTerminal` closes the old root ledger locally; the source-fixed
terminal handoff generates a new root's initial occurrence.  Thus a caller
cannot inspect a terminal branch and then choose a continuation handler.

The kernel is constructive and stores no completed future table.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-! ## Exact temporal registration shared by every living authority mouth -/

/-- Causal histories which begin at one source-generated cofinal landing.
They cannot be constructed from a finite visit, so later successors retain
that boundary identity by construction. -/
inductive SourceNativePostCofinalReachableAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) : V.Current → Type (u + 1)
  | cofinal
      (visit : SourceNativeCofinalVisitAt root) :
      SourceNativePostCofinalReachableAt root visit.current
  | step {current next : V.Current}
      (prior : SourceNativePostCofinalReachableAt root current)
      (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next) :
      SourceNativePostCofinalReachableAt root next

/-- Unified temporal reachability has exactly two causal origins: one complete
finite root visit, or one cofinal landing with its later successors. -/
inductive SourceNativeTemporalReachableAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) : V.Current → Type (u + 1)
  | finite {current : V.Current}
      (history : root.toRoot.ReachableAt current) :
      SourceNativeTemporalReachableAt root current
  | postCofinal {current : V.Current}
      (history : SourceNativePostCofinalReachableAt root current) :
      SourceNativeTemporalReachableAt root current

/-- The unique temporal successor representation. -/
def SourceNativeTemporalReachableAt.next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {current : V.Current}
    (history : SourceNativeTemporalReachableAt root current)
    {next : V.Current}
    (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next) :
    SourceNativeTemporalReachableAt root next :=
  match history with
  | .finite finiteHistory => .finite (.step finiteHistory next_eq)
  | .postCofinal postCofinalHistory =>
      .postCofinal (.step postCofinalHistory next_eq)

/-- Exact registered finite, cofinal, or post-cofinal current of one root. -/
structure SourceNativeTemporalVisitAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) : Type (u + 1) where
  current : V.Current
  history : SourceNativeTemporalReachableAt root current

/-- Finite successors after a cofinal landing retain that landing. -/
def SourceNativeTemporalReachableAt.hasCofinalBoundary
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V} :
    {current : V.Current} → SourceNativeTemporalReachableAt root current → Bool
  | _, .finite _ => false
  | _, .postCofinal _ => true

namespace SourceNativeTemporalVisitAt

def finite
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (visit : RootVisit root.toRoot) : SourceNativeTemporalVisitAt root :=
  ⟨visit.current, .finite visit.history⟩

/-- Embedding a finite causal visit cannot erase its chronological identity. -/
theorem finite_injective
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V} :
    Function.Injective (@finite _ _ root) := by
  intro left right equality
  cases left with
  | mk leftCurrent leftHistory =>
      cases right with
      | mk rightCurrent rightHistory =>
          simp only [finite] at equality
          cases equality
          rfl

def cofinal
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (visit : SourceNativeCofinalVisitAt root) :
    SourceNativeTemporalVisitAt root :=
  ⟨visit.current, .postCofinal (.cofinal visit)⟩

def next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (visit : SourceNativeTemporalVisitAt root)
    {next : V.Current}
    (next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? = some next) :
    SourceNativeTemporalVisitAt root :=
  ⟨next, visit.history.next next_eq⟩

@[simp] theorem finite_next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    (visit : RootVisit root.toRoot)
    {next : V.Current}
    (next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? = some next) :
    (finite visit).next next_eq = finite (visit.next next_eq) :=
  rfl

end SourceNativeTemporalVisitAt

/-! ## Source-level causal history consumed by terminal handoff -/

/-- Finite causal history written only in terms of one fixed authority
source.  Each step stores the exact source occurrence whose compiler produced
the successor.  It can therefore be installed before a particular root
emitter while still distinguishing recurrent visits to the same current. -/
inductive SourceNativeAuthorityFiniteHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V) : V.Current -> Type u
  | initial : SourceNativeAuthorityFiniteHistoryAt source
      source.restructuringSource.source.initial
  | step {current next : V.Current}
      (prior : SourceNativeAuthorityFiniteHistoryAt source current)
      (occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt
          current)
      (next_eq :
        (source.restructuringSource.source.toRootSource.actual.compile
          occurrence).nextCurrent? = some next) :
      SourceNativeAuthorityFiniteHistoryAt source next

/-- Source-owned cofinal boundary history.  The exact emitted event, its
entire predecessor occurrence stream, and every successor equation are part
of the history; a boundary label alone is not a renewal receipt. -/
structure SourceNativeAuthorityCofinalHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V) : Type u where
  event : V.cofinal.Event
  emitted_eq : V.cofinal.emit? = some event
  occurrenceAt : (index : Nat) ->
    source.restructuringSource.source.toRootSource.actual.OccurrenceAt
      (V.cofinal.pathAt event index)
  initial_eq : V.cofinal.pathAt event 0 =
    source.restructuringSource.source.initial
  next_eq : (index : Nat) ->
    (source.restructuringSource.source.toRootSource.actual.compile
      (occurrenceAt index)).nextCurrent? =
        some (V.cofinal.pathAt event (index + 1))

/-- Causal history after a source-owned cofinal landing. -/
inductive SourceNativeAuthorityPostCofinalHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V) : V.Current -> Type u
  | cofinal (history : SourceNativeAuthorityCofinalHistoryAt source) :
      SourceNativeAuthorityPostCofinalHistoryAt source
        (V.cofinal.target history.event)
  | step {current next : V.Current}
      (prior : SourceNativeAuthorityPostCofinalHistoryAt source current)
      (occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt
          current)
      (next_eq :
        (source.restructuringSource.source.toRootSource.actual.compile
          occurrence).nextCurrent? = some next) :
      SourceNativeAuthorityPostCofinalHistoryAt source next

/-- Unified source-level history consumed by a terminal handoff.  It mirrors
the root temporal registry without depending on a later chosen emitter. -/
inductive SourceNativeAuthorityTemporalHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V) : V.Current -> Type u
  | finite {current : V.Current}
      (history : SourceNativeAuthorityFiniteHistoryAt source current) :
      SourceNativeAuthorityTemporalHistoryAt source current
  | postCofinal {current : V.Current}
      (history : SourceNativeAuthorityPostCofinalHistoryAt source current) :
      SourceNativeAuthorityTemporalHistoryAt source current

/-- Boundary-origin readout of source-level temporal history.  It contains no
branch choice; it is used to show that finite and post-cofinal renewals cannot
share one causal index merely because their current labels agree. -/
def SourceNativeAuthorityTemporalHistoryAt.hasCofinalBoundary
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V} :
    {current : V.Current} ->
      SourceNativeAuthorityTemporalHistoryAt source current -> Bool
  | _, .finite _ => false
  | _, .postCofinal _ => true

/-- Exact compiler-generated faithful-terminal occurrence before a root
emitter is installed. -/
structure SourceFaithfulTerminalOccurrenceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V)
    {current : V.Current}
    (occurrence : source.restructuringSource.source.toRootSource.actual.OccurrenceAt
      current) : Type u where
  terminal : V.FaithfulTerminalAt current
  structural_eq :
    source.restructuringSource.source.toRootSource.actual.compile occurrence =
      .faithfulTerminal terminal
  ledgerEvolution : LedgerTerminalEvolutionAt N
    ⟨source.restructuringSource.source.toRootSource.account.supportOf occurrence⟩
  generated_eq :
    source.restructuringSource.compiler.ledgerCompiler.compile occurrence =
      .faithfulTerminal terminal structural_eq ledgerEvolution

namespace SourceFaithfulTerminalOccurrenceAt

/-- Exact occurrence in the admitted concrete source which this terminal
authority represents. -/
def actualOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V}
    {current : V.Current}
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current}
    (_terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) :=
  source.eventInventoryAdmission.actualOccurrenceAt occurrence

/-- The lower concrete compiler itself emits a literal faithful terminal; it
is not merely reinterpreted as terminal by the authority vocabulary. -/
def actualTerminal
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V}
    {current : V.Current}
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current}
    (terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) :=
  source.eventInventoryAdmission.actualFaithfulTerminalAt occurrence
    terminal.terminal terminal.structural_eq

/-- Complete concrete whole-ledger write-back retained by this authority. -/
theorem wholeLedgerWriteBack_heq_actual
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V}
    {current : V.Current}
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current}
    (_terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) :
    HEq
      (source.restructuringSource.compiler.ledgerCompiler.compile occurrence)
      (source.eventInventoryAdmission.actualSource.ledgerCompiler.compile
        (source.eventInventoryAdmission.actualOccurrenceAt occurrence)) :=
  source.eventInventoryAdmission.wholeLedgerWriteBack_heq_actual occurrence

/-- Complete concrete finite patch retained by this authority. -/
theorem finitePatch_heq_actual
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V}
    {current : V.Current}
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current}
    (_terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) :
    HEq
      (source.restructuringSource.compiler.ledgerCompiler.compilePatch occurrence)
      (source.eventInventoryAdmission.actualSource.ledgerCompiler.compilePatch
        (source.eventInventoryAdmission.actualOccurrenceAt occurrence)) :=
  source.eventInventoryAdmission.finitePatch_heq_actual occurrence

/-- Public terminal authority includes constructive exhaustion of the concrete
actual-event inventory admitted beneath this authority source.  A sibling
source-native continuation therefore vetoes terminal authority even when a
thinner vocabulary omits that continuation. -/
theorem noOutgoingActual
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V}
    {current : V.Current}
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current}
    (terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) :
    IsEmpty
      (SourceNativeActualOutgoingEventAt
        source.eventInventoryAdmission.actualSource
        (source.eventInventoryAdmission.currentPresentation.backward current)) :=
  source.eventInventoryAdmission.noOutgoingActual_of_representedTerminal
    occurrence terminal.terminal terminal.structural_eq

end SourceFaithfulTerminalOccurrenceAt

/-- Source-native event generated by one exact local terminal occurrence. -/
structure SourceNativeTerminalHandoffLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V) : Type (u + 2) where
  private mk ::
  private EventAt : {current : V.Current} →
    (history : SourceNativeAuthorityTemporalHistoryAt source current) →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    SourceFaithfulTerminalOccurrenceAt source occurrence → Type u
  private emit : {current : V.Current} →
    (history : SourceNativeAuthorityTemporalHistoryAt source current) →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    (terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) →
      EventAt history terminal
  private NextVAt : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      EventAt history terminal → Vocabulary.{u}
  private nextRootAt : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
      SourceNativeAuthoritativeRootClosure N (NextVAt event)
  private occurrencePresentation : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
      ConstructivePresentation
        ((nextRootAt event).toRoot.actual.OccurrenceAt
          (nextRootAt event).toRoot.source.initial)
        (EventAt history terminal)
  private occurrence_commutes : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
      (occurrencePresentation event).forward
        ((nextRootAt event).emitted
          (nextRootAt event).toRoot.source.initial) = event
  /-- A local terminal may hand control to a different vocabulary/current,
  but it cannot revise the root law surface.  Theory revision is generated by
  the rooted U7/U8 path; a terminal handoff only transports the already fixed
  law epoch. -/
  private lawSurface_eq : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
      (nextRootAt event).source.lawSurface = source.lawSurface
  /-- Every target row is classified against the complete old ledger.  It is
  either a continuation of an exact old debt lineage or is constructively
  fresh relative to every old row.  Presence in the target root alone cannot
  mint a fresh identity. -/
  private targetDebtOrigin : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
    (targetEntry : OpenResponsibilityAt N
      ((nextRootAt event).toRoot.supportAt
        (nextRootAt event).toRoot.source.initial)) →
    (Sigma fun sourceEntry : OpenResponsibilityAt N
        (source.restructuringSource.source.toRootSource.account.supportOf
          occurrence) =>
      RootDebtLineageAt N sourceEntry targetEntry) ⊕
      RootDebtFreshAt N
        (source.restructuringSource.source.toRootSource.account.supportOf
          occurrence) targetEntry
  /-- Crossing a root boundary cannot reset the budget of the same debt even
  when anchor, incidence, carrier, responsibility presentation, or clock
  changes. -/
  private sameDebtBudget_not_refilled : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
    (sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf
        occurrence)) →
    (targetEntry : OpenResponsibilityAt N
      ((nextRootAt event).toRoot.supportAt
        (nextRootAt event).toRoot.source.initial)) →
    RootDebtLineageAt N sourceEntry targetEntry →
    targetEntry.progressBudget <= sourceEntry.progressBudget
  /-- A terminal handoff is not a second split compiler.  Two target rows
  carrying one old debt lineage must be the same dependent ledger entry;
  legitimate one-to-many evolution stays in the ordinary source-generated
  split/merge law. -/
  private sameDebtTarget_unique : {current : V.Current} →
    {history : SourceNativeAuthorityTemporalHistoryAt source current} →
    {occurrence :
      source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
    {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
    (event : EventAt history terminal) →
    (sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf
        occurrence)) →
    (left right : OpenResponsibilityAt N
      ((nextRootAt event).toRoot.supportAt
        (nextRootAt event).toRoot.source.initial)) →
    RootDebtLineageAt N sourceEntry left →
    RootDebtLineageAt N sourceEntry right →
    left = right

/-- Install a complete terminal-handoff source law before an emitter exists.
The callbacks are accepted only at source construction; the resulting law has
no public projection which can mint a next root outside temporal registration. -/
def SourceNativeTerminalHandoffLaw.create
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeAuthoritySource N V}
    (EventAt : {current : V.Current} →
      SourceNativeAuthorityTemporalHistoryAt source current →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      SourceFaithfulTerminalOccurrenceAt source occurrence → Type u)
    (emit : {current : V.Current} →
      (history : SourceNativeAuthorityTemporalHistoryAt source current) →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      (terminal : SourceFaithfulTerminalOccurrenceAt source occurrence) →
        EventAt history terminal)
    (NextVAt : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
        EventAt history terminal → Vocabulary.{u})
    (nextRootAt : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
        SourceNativeAuthoritativeRootClosure N (NextVAt event))
    (occurrencePresentation : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
        ConstructivePresentation
          ((nextRootAt event).toRoot.actual.OccurrenceAt
            (nextRootAt event).toRoot.source.initial)
          (EventAt history terminal))
    (occurrence_commutes : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
        (occurrencePresentation event).forward
          ((nextRootAt event).emitted
            (nextRootAt event).toRoot.source.initial) = event)
    (lawSurface_eq : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
        (nextRootAt event).source.lawSurface = source.lawSurface)
    (targetDebtOrigin : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
      (targetEntry : OpenResponsibilityAt N
        ((nextRootAt event).toRoot.supportAt
          (nextRootAt event).toRoot.source.initial)) →
      (Sigma fun sourceEntry : OpenResponsibilityAt N
          (source.restructuringSource.source.toRootSource.account.supportOf
            occurrence) =>
        RootDebtLineageAt N sourceEntry targetEntry) ⊕
        RootDebtFreshAt N
          (source.restructuringSource.source.toRootSource.account.supportOf
            occurrence) targetEntry)
    (sameDebtBudget_not_refilled : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
      (sourceEntry : OpenResponsibilityAt N
        (source.restructuringSource.source.toRootSource.account.supportOf
          occurrence)) →
      (targetEntry : OpenResponsibilityAt N
        ((nextRootAt event).toRoot.supportAt
          (nextRootAt event).toRoot.source.initial)) →
      RootDebtLineageAt N sourceEntry targetEntry →
      targetEntry.progressBudget <= sourceEntry.progressBudget)
    (sameDebtTarget_unique : {current : V.Current} →
      {history : SourceNativeAuthorityTemporalHistoryAt source current} →
      {occurrence :
        source.restructuringSource.source.toRootSource.actual.OccurrenceAt current} →
      {terminal : SourceFaithfulTerminalOccurrenceAt source occurrence} →
      (event : EventAt history terminal) →
      (sourceEntry : OpenResponsibilityAt N
        (source.restructuringSource.source.toRootSource.account.supportOf
          occurrence)) →
      (left right : OpenResponsibilityAt N
        ((nextRootAt event).toRoot.supportAt
          (nextRootAt event).toRoot.source.initial)) →
      RootDebtLineageAt N sourceEntry left →
      RootDebtLineageAt N sourceEntry right →
      left = right) :
    SourceNativeTerminalHandoffLaw source :=
  ⟨EventAt, emit, NextVAt, nextRootAt, occurrencePresentation,
    occurrence_commutes, lawSurface_eq, targetDebtOrigin, sameDebtBudget_not_refilled,
    sameDebtTarget_unique⟩

/-- Complete root source identity.  The terminal-handoff compiler is fixed
before the actual emitter reveals a branch. -/
structure SourceNativeLivingAuthoritySource
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 2) where
  base : SourceNativeAuthoritySource N V
  terminalHandoff : SourceNativeTerminalHandoffLaw base

/-- A living root installs an emitter for an already complete source law. -/
structure SourceNativeLivingRootClosure
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 2) where
  source : SourceNativeLivingAuthoritySource N V
  emitted : (current : V.Current) →
    source.base.restructuringSource.source.toRootSource.actual.OccurrenceAt current
  compiler_commutes : (current : V.Current) →
    (source.base.restructuringSource.compiler.ledgerCompiler.compile
      (emitted current)).CommutesWith emitted

/-- Forget only the living-world terminal handoff law. -/
def SourceNativeLivingRootClosure.toAuthoritativeRoot
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) :
    SourceNativeAuthoritativeRootClosure N V where
  source := root.source.base
  emitted := root.emitted
  compiler_commutes := root.compiler_commutes

/-- Canonical source-level finite history of one living-root visit.  The
conversion inserts the exact emitted occurrence at every predecessor, so the
handoff source cannot identify two visits merely because their current labels
coincide. -/
def SourceNativeLivingRootClosure.terminalFiniteHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) :
    {current : V.Current} ->
      root.toAuthoritativeRoot.toRoot.ReachableAt current ->
      SourceNativeAuthorityFiniteHistoryAt root.source.base current
  | _, .initial => .initial
  | _, @RootClosure.ReachableAt.step _ _ _ current _next prior next_eq =>
      .step (root.terminalFiniteHistoryAt prior) (root.emitted current) next_eq

/-- Canonical source-level history of one emitted cofinal occurrence. -/
def SourceNativeLivingRootClosure.terminalCofinalHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeCofinalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeAuthorityCofinalHistoryAt root.source.base where
  event := visit.event
  emitted_eq := visit.emitted_eq_event
  occurrenceAt := fun index =>
    root.emitted (V.cofinal.pathAt visit.event index)
  initial_eq := visit.history.initial_eq
  next_eq := visit.history.next_eq

/-- Canonical source-level history after a cofinal landing. -/
def SourceNativeLivingRootClosure.terminalPostCofinalHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) :
    {current : V.Current} ->
      SourceNativePostCofinalReachableAt
        root.toAuthoritativeRoot.toLedgerRoot current ->
      SourceNativeAuthorityPostCofinalHistoryAt root.source.base current
  | _, .cofinal visit => .cofinal (root.terminalCofinalHistoryAt visit)
  | _, @SourceNativePostCofinalReachableAt.step _ _ _ current _next prior next_eq =>
      .step (root.terminalPostCofinalHistoryAt prior)
        (root.emitted current) next_eq

/-- Full source-level history consumed by terminal handoff at one exact
temporal visit. -/
def SourceNativeLivingRootClosure.terminalHistoryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeAuthorityTemporalHistoryAt root.source.base visit.current :=
  match visit.history with
  | .finite history => .finite (root.terminalFiniteHistoryAt history)
  | .postCofinal history =>
      .postCofinal (root.terminalPostCofinalHistoryAt history)

/-- The source-level terminal history retains the finite/cofinal origin of
the registered temporal visit. -/
@[simp] theorem SourceNativeLivingRootClosure.terminalHistoryAt_hasCofinalBoundary
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    (root.terminalHistoryAt visit).hasCofinalBoundary =
      visit.history.hasCofinalBoundary := by
  rcases visit with ⟨current, history⟩
  cases history <;> rfl

/-- Heterogeneous authoritative root/current package. -/
structure SourceNativeAuthoritativeRootCurrentAt
    (N : WorldRelationNetwork.{u}) : Type (u + 3) where
  V : Vocabulary.{u}
  root : SourceNativeAuthoritativeRootClosure N V
  visit : SourceNativeTemporalVisitAt root.toLedgerRoot

/-- Execute the fixed terminal-handoff compiler only at an exact registered
finite, cofinal, or post-cofinal visit of this living root.

The handoff implementation is intentionally opaque outside this file: a raw
terminal payload cannot project a next authoritative root without first
entering the temporal root registry. -/
def SourceNativeLivingRootClosure.generatedTerminalHandoffAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current)) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  let history := root.terminalHistoryAt visit
  let event := root.source.terminalHandoff.emit history terminal
  let nextRoot := root.source.terminalHandoff.nextRootAt event
  ⟨root.source.terminalHandoff.NextVAt event,
    nextRoot, .finite nextRoot.toRoot.initialVisit⟩

/-- A registered local terminal handoff preserves the one root law epoch.
Changing the theory surface is therefore not a hidden terminal side effect;
it must enter the rooted U7/U8 revision path. -/
theorem SourceNativeLivingRootClosure.generatedTerminalHandoff_lawSurface_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current)) :
    (root.generatedTerminalHandoffAt visit terminal).root.source.lawSurface =
      root.source.base.lawSurface := by
  exact root.source.terminalHandoff.lawSurface_eq
    (root.source.terminalHandoff.emit (root.terminalHistoryAt visit) terminal)

/-- Every row admitted at the terminal handoff target is either attached to
an exact old debt lineage or constructively fresh relative to the complete old
ledger.  There is no unclassified carrier seam between the two roots. -/
def SourceNativeLivingRootClosure.generatedTerminalHandoff_targetDebtOrigin
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current))
    (targetEntry : OpenResponsibilityAt N
      ((root.generatedTerminalHandoffAt visit terminal).root.toRoot.supportAt
        (root.generatedTerminalHandoffAt visit terminal).visit.current)) :
    (Sigma fun sourceEntry : OpenResponsibilityAt N
        (root.toAuthoritativeRoot.toRoot.supportAt visit.current) =>
      RootDebtLineageAt N sourceEntry targetEntry) ⊕
      RootDebtFreshAt N
        (root.toAuthoritativeRoot.toRoot.supportAt visit.current) targetEntry :=
  root.source.terminalHandoff.targetDebtOrigin
    (root.source.terminalHandoff.emit (root.terminalHistoryAt visit) terminal)
    targetEntry

/-- A registered terminal handoff cannot refill one old debt lineage by
changing its anchor, incidence, carrier, responsibility label, or clock. -/
theorem SourceNativeLivingRootClosure.generatedTerminalHandoff_sameDebtBudget_not_refilled
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current))
    (sourceEntry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toRoot.supportAt visit.current))
    (targetEntry : OpenResponsibilityAt N
      ((root.generatedTerminalHandoffAt visit terminal).root.toRoot.supportAt
        (root.generatedTerminalHandoffAt visit terminal).visit.current))
    (sameDebt : RootDebtLineageAt N sourceEntry targetEntry) :
    targetEntry.progressBudget <= sourceEntry.progressBudget := by
  exact root.source.terminalHandoff.sameDebtBudget_not_refilled
    (root.source.terminalHandoff.emit (root.terminalHistoryAt visit) terminal)
    sourceEntry targetEntry sameDebt

/-- One old debt lineage cannot be cloned into two target rows at a terminal
handoff. -/
theorem SourceNativeLivingRootClosure.generatedTerminalHandoff_sameDebtTarget_unique
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current))
    (sourceEntry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toRoot.supportAt visit.current))
    (left right : OpenResponsibilityAt N
      ((root.generatedTerminalHandoffAt visit terminal).root.toRoot.supportAt
        (root.generatedTerminalHandoffAt visit terminal).visit.current))
    (leftIdentity : RootDebtLineageAt N sourceEntry left)
    (rightIdentity : RootDebtLineageAt N sourceEntry right) :
    left = right := by
  exact root.source.terminalHandoff.sameDebtTarget_unique
    (root.source.terminalHandoff.emit (root.terminalHistoryAt visit) terminal)
    sourceEntry left right leftIdentity rightIdentity

/-- A registered terminal handoff cannot reopen the same standing with fresh
progress credit.  This is the cross-root counterpart of
`LedgerEntryEvolutionAt.progressBudget_not_refilled`; new rows remain
possible, but identity-preserving recurrence must retain the old debt clock. -/
theorem SourceNativeLivingRootClosure.generatedTerminalHandoff_sameStandingBudget_not_refilled
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current))
    (sourceEntry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toRoot.supportAt visit.current))
    (targetEntry : OpenResponsibilityAt N
      ((root.generatedTerminalHandoffAt visit terminal).root.toRoot.supportAt
        (root.generatedTerminalHandoffAt visit terminal).visit.current))
    (sameStanding : RootStandingIdentityAt N sourceEntry targetEntry) :
    targetEntry.progressBudget <= sourceEntry.progressBudget := by
  exact root.generatedTerminalHandoff_sameDebtBudget_not_refilled
    visit terminal sourceEntry targetEntry sameStanding.toDebtLineage

/-- A registered terminal handoff cannot clone one old standing into two
target-ledger entries. -/
theorem SourceNativeLivingRootClosure.generatedTerminalHandoff_sameStandingTarget_unique
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (terminal : SourceFaithfulTerminalOccurrenceAt root.source.base
      (root.emitted visit.current))
    (sourceEntry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toRoot.supportAt visit.current))
    (left right : OpenResponsibilityAt N
      ((root.generatedTerminalHandoffAt visit terminal).root.toRoot.supportAt
        (root.generatedTerminalHandoffAt visit terminal).visit.current))
    (leftIdentity : RootStandingIdentityAt N sourceEntry left)
    (rightIdentity : RootStandingIdentityAt N sourceEntry right) :
    left = right := by
  exact root.generatedTerminalHandoff_sameDebtTarget_unique
    visit terminal sourceEntry left right
    leftIdentity.toDebtLineage rightIdentity.toDebtLineage

/-- Canonical empty terminal-handoff law when the source vocabulary proves
that no faithful-terminal payload exists at any current.

This is a derived adapter, not a second continuation court: the event fibre is
literally empty and every remaining field eliminates that empty event. -/
def SourceNativeAuthoritySource.emptyFaithfulTerminalHandoff
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeAuthoritySource N V)
    (terminalEmpty : (current : V.Current) →
      IsEmpty (V.FaithfulTerminalAt current)) :
    SourceNativeTerminalHandoffLaw source where
  EventAt := fun {_current} _history {_occurrence} _terminal => PEmpty
  emit := fun {current} _history {_occurrence} terminal =>
    False.elim ((terminalEmpty current).false terminal.terminal)
  NextVAt := fun {_current} {_history} {_occurrence} {_terminal} event =>
    nomatch event
  nextRootAt := fun {_current} {_history} {_occurrence} {_terminal} event =>
    nomatch event
  occurrencePresentation :=
    fun {_current} {_history} {_occurrence} {_terminal} event =>
    nomatch event
  occurrence_commutes :=
    fun {_current} {_history} {_occurrence} {_terminal} event =>
    nomatch event
  lawSurface_eq :=
    fun {_current} {_history} {_occurrence} {_terminal} event =>
    nomatch event
  targetDebtOrigin :=
    fun {_current} {_history} {_occurrence} {_terminal} event => nomatch event
  sameDebtBudget_not_refilled :=
    fun {_current} {_history} {_occurrence} {_terminal} event => nomatch event
  sameDebtTarget_unique :=
    fun {_current} {_history} {_occurrence} {_terminal} event => nomatch event

/-- Regard an authoritative root with an empty faithful-terminal fibre as a
living root.  No dummy terminal receipt or fallback root is introduced. -/
def SourceNativeAuthoritativeRootClosure.toLivingWithoutFaithfulTerminal
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeAuthoritativeRootClosure N V)
    (terminalEmpty : (current : V.Current) →
      IsEmpty (V.FaithfulTerminalAt current)) :
    SourceNativeLivingRootClosure N V where
  source :=
    { base := root.source
      terminalHandoff :=
        root.source.emptyFaithfulTerminalHandoff terminalEmpty }
  emitted := root.emitted
  compiler_commutes := root.compiler_commutes

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

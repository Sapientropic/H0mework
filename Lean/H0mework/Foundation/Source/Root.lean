import H0mework.Foundation.Source.RelationNetwork

/-!
# Axiom-free single-root living-law closure

This is the constructive root beneath every algebraic or path-library
presentation.  It mentions no field, module, quotient, linear map, or chosen
representative.  One source-owned actual-event algebra fixes the occurrence
family and canonical compiler for the law epoch; the root directly emits an
occurrence of that algebra.  Its exhaustive structural disposition and shared
support are read from that same dependent occurrence.  Source-native ledger
evolution authority lives in `LivingLawRootSourceNativeLedgerCompilerKernel`.

Domain presentations may restrict an exact causal root occurrence.  A domain
name is never a primitive coordinate: concrete source laws install the
coordinates they actually generate, and downstream recognitions retain the
source-native compiler and its occurrence-local image.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u v

/-- The complete world-level open-responsibility fibre at one support. -/
abbrev OpenResponsibilityAt
    (N : WorldRelationNetwork.{u}) (support : N.Support) : Type u :=
  Sigma fun responsibility : N.Responsibility =>
    N.OpenAt support responsibility

/-- Exact semantic claim carried by one live responsibility incidence.  This
is a readout of the proof-relevant `OpenAt` witness, not a freely supplied
claim at the same support. -/
def OpenResponsibilityAt.claim
    {N : WorldRelationNetwork.{u}}
    {support : N.Support}
    (entry : OpenResponsibilityAt N support) : N.Claim :=
  N.openClaimAt entry.2

/-- Source-owned remaining progress budget of the exact live incidence. -/
def OpenResponsibilityAt.progressBudget
    {N : WorldRelationNetwork.{u}}
    {support : N.Support}
    (entry : OpenResponsibilityAt N support) : Nat :=
  N.openProgressBudgetAt entry.2

/-- Exact world identity of one standing across two registered supports.

The supports may differ, but the source anchor, incidence, lineage,
responsibility and semantic claim must all survive.  This is the identity
tested at a root handoff before a later row may be treated as a genuinely new
obligation rather than a continuation of an old one. -/
structure RootStandingIdentityAt
    (N : WorldRelationNetwork.{u})
    {sourceSupport targetSupport : N.Support}
    (source : OpenResponsibilityAt N sourceSupport)
    (target : OpenResponsibilityAt N targetSupport) : Type u where
  anchor_eq : N.anchorAt sourceSupport = N.anchorAt targetSupport
  incidence_eq : N.incidenceAt sourceSupport = N.incidenceAt targetSupport
  lineage_eq : N.lineageAt sourceSupport = N.lineageAt targetSupport
  responsibility_eq : source.1 = target.1
  claim_eq : source.claim = target.claim

/-- Debt identity which survives a legitimate change of anchor, incidence,
carrier, or local clock.  Lineage and semantic claim are the invariant account;
the changed coordinates must be paid by the actual transition instead of
turning the old debt into a fresh row. -/
structure RootDebtLineageAt
    (N : WorldRelationNetwork.{u})
    {sourceSupport targetSupport : N.Support}
    (source : OpenResponsibilityAt N sourceSupport)
    (target : OpenResponsibilityAt N targetSupport) : Type u where
  lineage_eq : N.lineageAt sourceSupport = N.lineageAt targetSupport
  claim_eq : source.claim = target.claim

/-- Exact standing identity implies debt-lineage identity, but not conversely:
a transfer may legitimately change anchor, incidence, or responsibility while
remaining liable for the same semantic account. -/
def RootStandingIdentityAt.toDebtLineage
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (identity : RootStandingIdentityAt N source target) :
    RootDebtLineageAt N source target where
  lineage_eq := identity.lineage_eq
  claim_eq := identity.claim_eq

/-- Constructive certificate that one target row is a genuinely new debt
relative to the complete source ledger.  The target occurrence still supplies
the admission; this record only rules out laundering an old lineage as fresh. -/
structure RootDebtFreshAt
    (N : WorldRelationNetwork.{u})
    (sourceSupport : N.Support)
    {targetSupport : N.Support}
    (target : OpenResponsibilityAt N targetSupport) : Type u where
  noPrior : (source : OpenResponsibilityAt N sourceSupport) →
    RootDebtLineageAt N source target → PEmpty

/-- A purported fresh row is immediately refuted by any exact prior debt with
the same lineage and claim. -/
def RootDebtFreshAt.excludesPrior
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {target : OpenResponsibilityAt N targetSupport}
    (fresh : RootDebtFreshAt N sourceSupport target)
    (source : OpenResponsibilityAt N sourceSupport)
    (sameDebt : RootDebtLineageAt N source target) : PEmpty :=
  fresh.noPrior source sameDebt

/-- Identity of the complete live ledger.  The only stored datum is the
world support; its entries are the entire `OpenAt` fibre at that support.
There is no field in which a caller can select one convenient obligation. -/
structure CompleteLiveLedgerAt (N : WorldRelationNetwork.{u}) : Type u where
  support : N.Support

abbrev CompleteLiveLedgerAt.Entry
    {N : WorldRelationNetwork.{u}} (ledger : CompleteLiveLedgerAt N) : Type u :=
  OpenResponsibilityAt N ledger.support

/-- Exact disposition of one old live entry at one generated target face.

An ordinary carry is the same row read at definitionally identical root faces;
the debt does not move and its budget is equal.  A change of support, incidence
witness, or multiplicity must therefore be generated explicitly.  Maintenance
may change the open witness only while preserving its rooted identity and
strictly spending its source-owned budget.  Transfer changes the registered
bearer/anchor/incidence relation around the same debt; it does not move or
refresh the debt identity.  It preserves lineage and claim, cannot refill the
source-owned budget, and the new relation must be paid by the surrounding exact
root transition. -/
inductive LedgerEntryEvolutionAt
    (N : WorldRelationNetwork.{u})
    {sourceSupport targetSupport : N.Support}
    (source : OpenResponsibilityAt N sourceSupport)
    (target : OpenResponsibilityAt N targetSupport) : Type u
  | carried
      (support_eq : sourceSupport = targetSupport)
      (entry_eq : HEq source target)
  | maintained
      (anchor_eq : N.anchorAt sourceSupport = N.anchorAt targetSupport)
      (incidence_eq : N.incidenceAt sourceSupport = N.incidenceAt targetSupport)
      (lineage_eq : N.lineageAt sourceSupport = N.lineageAt targetSupport)
      (responsibility_eq : source.1 = target.1)
      (claim_eq : source.claim = target.claim)
      (strict_debit : target.progressBudget < source.progressBudget)
  | transferred
      (receipt : N.DispositionAt sourceSupport .transfer)
      (lineage_eq : N.lineageAt sourceSupport = N.lineageAt targetSupport)
      (claim_eq : source.claim = target.claim)
      (progressBudget_not_refilled :
        target.progressBudget <= source.progressBudget)

/-- Every legal row evolution preserves or spends the exact live-incidence
budget.  Carry is definitionally neutral, maintenance spends strictly, and
transfer cannot reset the clock. -/
theorem LedgerEntryEvolutionAt.progressBudget_not_refilled
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (evolution : LedgerEntryEvolutionAt N source target) :
    target.progressBudget <= source.progressBudget := by
  cases evolution with
  | carried support_eq entry_eq =>
      cases support_eq
      cases entry_eq
      exact Nat.le_refl _
  | maintained _ _ _ _ _ strict_debit => exact Nat.le_of_lt strict_debit
  | transferred _ _ _ budget => exact budget

namespace LedgerEntryEvolutionAt

/-- Every canonical whole-ledger row evolution preserves debt identity.

This belongs with the row evolution itself: downstream provenance and
Noetherian closure both consume it, but neither should recompile it. -/
def toDebtLineage
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (evolution : LedgerEntryEvolutionAt N source target) :
    RootDebtLineageAt N source target := by
  cases evolution with
  | carried support_eq entry_eq =>
      cases support_eq
      cases entry_eq
      exact ⟨rfl, rfl⟩
  | maintained _ _ lineage_eq _ claim_eq _ =>
      exact ⟨lineage_eq, claim_eq⟩
  | transferred _ lineage_eq claim_eq _ =>
      exact ⟨lineage_eq, claim_eq⟩

end LedgerEntryEvolutionAt

/-- Definitionally carried rows are two root-face reads of the same live
incidence, so their budget is equal rather than merely non-increasing. -/
theorem LedgerEntryEvolutionAt.carried_progressBudget_eq
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (support_eq : sourceSupport = targetSupport)
    (entry_eq : HEq source target) :
    target.progressBudget = source.progressBudget := by
  cases support_eq
  cases entry_eq
  rfl

/-- The transfer receipt is the data; the conservation and debit fields are
proofs and therefore cannot create a second transfer outcome. -/
@[simp] theorem LedgerEntryEvolutionAt.transferred_proof_irrel
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (receipt : N.DispositionAt sourceSupport .transfer)
    (lineage₁ lineage₂ : N.lineageAt sourceSupport = N.lineageAt targetSupport)
    (claim₁ claim₂ : source.claim = target.claim)
    (budget₁ budget₂ : target.progressBudget <= source.progressBudget) :
    LedgerEntryEvolutionAt.transferred receipt lineage₁ claim₁ budget₁ =
      LedgerEntryEvolutionAt.transferred receipt lineage₂ claim₂ budget₂ := by
  rfl

/-- One exact live entry is discharged by the source-owned support-settlement
receipt.  The entry remains in the type index, so a whole-ledger terminal
cannot silently omit a live incidence. -/
structure LedgerEntryTerminalAt
    (N : WorldRelationNetwork.{u})
    {support : N.Support}
    (entry : OpenResponsibilityAt N support) : Type u where
  receipt : N.DispositionAt support .supportSettlement

/-- Exhaustive actual disposition of one live ledger entry.

The source either presents the exact debt at a generated target row (possibly
with an accepted bearer reassignment) or discharges it with its exact terminal
receipt.  U7, effect, and operational faces use this common carrier to expose
the compiler's whole-ledger disposition. -/
inductive LedgerEntryDispositionAt
    (N : WorldRelationNetwork.{u})
    {sourceSupport : N.Support}
    (source : OpenResponsibilityAt N sourceSupport) : Type u
  | evolved {targetSupport : N.Support}
      {target : OpenResponsibilityAt N targetSupport}
      (evolution : LedgerEntryEvolutionAt N source target)
  | terminal (terminal : LedgerEntryTerminalAt N source)

/-- A faithful terminal accounts for every entry in the complete source
ledger.  An empty ledger closes vacuously; a nonempty ledger needs one exact
entry-indexed discharge for each live incidence. -/
structure LedgerTerminalEvolutionAt
    (N : WorldRelationNetwork.{u})
    (source : CompleteLiveLedgerAt N) : Type u where
  discharge : (entry : source.Entry) → LedgerEntryTerminalAt N entry

/-- A continuing root event accounts for the complete old and new live
inventories.  Every old entry has an actual destination and every new entry
has an actual origin.  The relation may be many-to-one or one-to-many, so
legitimate merge and split are not collapsed to a false bijection. -/
structure LedgerWriteEvolutionAt
    (N : WorldRelationNetwork.{u})
    (source target : CompleteLiveLedgerAt N) : Type u where
  destination : (sourceEntry : source.Entry) →
    Sigma fun targetEntry : target.Entry =>
      LedgerEntryEvolutionAt N sourceEntry targetEntry
  origin : (targetEntry : target.Entry) →
    Sigma fun sourceEntry : source.Entry =>
      LedgerEntryEvolutionAt N sourceEntry targetEntry

namespace LedgerWriteEvolutionAt

/-- Identity evolution of a complete ledger. -/
def identity
    {N : WorldRelationNetwork.{u}} (ledger : CompleteLiveLedgerAt N) :
    LedgerWriteEvolutionAt N ledger ledger where
  destination := fun entry => ⟨entry, .carried rfl (HEq.rfl)⟩
  origin := fun entry => ⟨entry, .carried rfl (HEq.rfl)⟩

end LedgerWriteEvolutionAt

/-- Source-owned event algebra for a cofinal root occurrence.  `emit?` fixes
whether this source has a boundary event and, when it does, which event
occurred.  The event fixes both its finite predecessor path and target before
any root history is presented; a caller can only recognize that canonical
path, never submit a path to the emitter. -/
structure SourceNativeCofinalTransitionLaw (Current : Type u) : Type (u + 1) where
  Event : Type u
  emit? : Option Event
  pathAt : Event → Nat → Current
  target : Event → Current

/-- Discrete vocabularies have no cofinal transition events. -/
def SourceNativeCofinalTransitionLaw.empty (Current : Type u) :
    SourceNativeCofinalTransitionLaw Current where
  Event := PEmpty
  emit? := none
  pathAt := PEmpty.elim
  target := PEmpty.elim

/-- The root evolution grammar.  Payload families and their exact targets
belong to the source-owned law surface; the kernel supplies no free target. -/
structure Vocabulary where
  Current : Type u
  Anchor : Type u
  Incidence : Type u
  Lineage : Type u
  anchorAt : Current → Anchor
  incidenceAt : Current → Incidence
  lineageAt : Current → Lineage
  NativeWriteAt : Current → Type u
  RelationWriteAt : Current → Type u
  ContinuedTransportAt : Current → Type u
  BorromeanRedirectAt : Current → Type u
  FaithfulTerminalAt : Current → Type u
  nativeTarget : {current : Current} → NativeWriteAt current → Current
  relationTarget : {current : Current} → RelationWriteAt current → Current
  continuedTarget : {current : Current} →
    ContinuedTransportAt current → Current
  redirectTarget : {current : Current} → BorromeanRedirectAt current → Current
  /-- Source-owned limit event for one concretely generated finite path.

  This does not add a seventh structural disposition.  It is the event whose
  target becomes the next root current at the cofinal boundary.  Keeping the
  event separate from its target prevents a caller from choosing a current
  and then attaching a proof that it is cofinal. -/
  cofinal : SourceNativeCofinalTransitionLaw Current :=
    SourceNativeCofinalTransitionLaw.empty Current

/-- Every root occurrence has exactly one source-native structural evolution.

Law-surface revision is deliberately absent.  It is not a primitive action a
domain compiler may select: an exact obstruction must first generate a U7
semantic-change incidence, from which U8 produces the revised first write. -/
inductive EvolutionAt (V : Vocabulary.{u}) (current : V.Current) : Type u
  | nativeWrite (write : V.NativeWriteAt current)
  | relationWrite (write : V.RelationWriteAt current)
  | continuedTransport (write : V.ContinuedTransportAt current)
  | borromeanRedirect (write : V.BorromeanRedirectAt current)
  | faithfulTerminal (terminal : V.FaithfulTerminalAt current)

/-- Presentation-independent structural branch of one root evolution. -/
inductive RootEvolutionKind
  | nativeWrite
  | relationWrite
  | continuedTransport
  | borromeanRedirect
  | faithfulTerminal
  deriving DecidableEq

/-- Structural branch readout.  Payload coordinates may be recharted, but a
complete event-inventory presentation must preserve this value. -/
def EvolutionAt.kind
    {V : Vocabulary.{u}} {current : V.Current} :
    EvolutionAt V current -> RootEvolutionKind
  | .nativeWrite _ => .nativeWrite
  | .relationWrite _ => .relationWrite
  | .continuedTransport _ => .continuedTransport
  | .borromeanRedirect _ => .borromeanRedirect
  | .faithfulTerminal _ => .faithfulTerminal

/-- The next current is structural: all continuing constructors use the
target function owned by the exact payload; only terminal has no successor. -/
def EvolutionAt.nextCurrent?
    {V : Vocabulary.{u}} {current : V.Current} :
    EvolutionAt V current → Option V.Current
  | .nativeWrite write => some (V.nativeTarget write)
  | .relationWrite write => some (V.relationTarget write)
  | .continuedTransport write => some (V.continuedTarget write)
  | .borromeanRedirect write => some (V.redirectTarget write)
  | .faithfulTerminal _ => none

/-- One source-owned primitive event algebra.  The canonical compiler belongs
to the law epoch itself; it is not a presentation or world-level choice. -/
structure ActualEventAlgebra (V : Vocabulary.{u}) : Type (u + 1) where
  OccurrenceAt : V.Current → Type u
  compile : {current : V.Current} →
    OccurrenceAt current → EvolutionAt V current

/-- Support and the running responsibility account are projections of the
same primitive occurrence which is realized into the whole evolution. -/
structure RootOccurrenceAccount
    (N : WorldRelationNetwork.{u})
    {V : Vocabulary.{u}}
    (actual : ActualEventAlgebra V) : Type (u + 1) where
  supportOf : {current : V.Current} → actual.OccurrenceAt current → N.Support
  anchorKey : V.Anchor → N.Anchor
  incidenceKey : V.Incidence → N.Incidence
  lineageKey : V.Lineage → N.Lineage
  anchor_commutes : {current : V.Current} →
    (occurrence : actual.OccurrenceAt current) →
      anchorKey (V.anchorAt current) = N.anchorAt (supportOf occurrence)
  incidence_commutes : {current : V.Current} →
    (occurrence : actual.OccurrenceAt current) →
      incidenceKey (V.incidenceAt current) = N.incidenceAt (supportOf occurrence)
  lineage_commutes : {current : V.Current} →
    (occurrence : actual.OccurrenceAt current) →
      lineageKey (V.lineageAt current) = N.lineageAt (supportOf occurrence)

/-- The complete source law for one root epoch.  Event compilation and the
support/ledger account are one identity: changing either means changing the
source, not selecting another presentation of the same source. -/
structure Source
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  /-- The primitive source owns the first registered current.  Reachability is
  generated from this current and the source's own compiler; an adapter cannot
  choose a second starting frame. -/
  initial : V.Current
  actual : ActualEventAlgebra V
  account : RootOccurrenceAccount N actual

/-- Root view of one primitive structural law and its emitted occurrences.
Ledger authority is not part of this structural carrier. -/
structure RootClosure
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  source : Source N V
  emitted : (current : V.Current) → source.actual.OccurrenceAt current

abbrev RootClosure.actual
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) : ActualEventAlgebra V :=
  R.source.actual

abbrev RootClosure.account
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) : RootOccurrenceAccount N R.actual :=
  R.source.account

def RootClosure.supportAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) : N.Support :=
  R.account.supportOf (R.emitted current)

def RootClosure.ledgerAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) :
    CompleteLiveLedgerAt N :=
  ⟨R.supportAt current⟩

/-- Structural evolution at a raw current.  This is a source-law readout, not
by itself authority that the current actually occurred. -/
def RootClosure.evolutionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) : EvolutionAt V current :=
  R.actual.compile (R.emitted current)

/-- Reachability is generated only from the source-owned initial current and
the exact successor of a previously reachable root evolution.  Merely
constructing a value of `V.Current` does not put it in the actual world. -/
inductive RootClosure.ReachableAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) : V.Current → Type u
  | initial : ReachableAt R R.source.initial
  | step {current next : V.Current}
      (prior : ReachableAt R current)
      (next_eq : (R.evolutionAt current).nextCurrent? = some next) :
      ReachableAt R next

/-- The source-owned first reachable current. -/
def RootClosure.initialReachable
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) : R.ReachableAt R.source.initial :=
  .initial

/-- The exact generated successor of a reachable current is reachable. -/
def RootClosure.nextReachable
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) {current next : V.Current}
    (prior : R.ReachableAt current)
    (next_eq : (R.evolutionAt current).nextCurrent? = some next) :
    R.ReachableAt next :=
  .step prior next_eq

/-- One exact chronological visit of a root current.  The current label alone
is not an occurrence identity: a lawful recurrence may revisit the same state
after a different causal history. -/
structure RootVisit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) : Type u where
  current : V.Current
  history : R.ReachableAt current

/-- The source-owned first visit. -/
def RootClosure.initialVisit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) : RootVisit R :=
  ⟨R.source.initial, R.initialReachable⟩

/-- A generated successor is a new visit even when its current label was seen
before.  Recurrence preserves state equality without reusing event identity. -/
def RootVisit.next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {R : RootClosure N V} (visit : RootVisit R)
    {next : V.Current}
    (next_eq : (R.evolutionAt visit.current).nextCurrent? = some next) :
    RootVisit R :=
  ⟨next, R.nextReachable visit.history next_eq⟩

@[simp] theorem RootClosure.supportAt_eq_emitted_account
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) :
    R.supportAt current =
      R.account.supportOf (R.emitted current) :=
  rfl

@[simp] theorem RootClosure.ledgerAt_eq_emitted_account
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) :
    R.ledgerAt current =
      ⟨R.account.supportOf (R.emitted current)⟩ :=
  rfl

theorem RootClosure.anchor_commutes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) :
    R.account.anchorKey (V.anchorAt current) =
      N.anchorAt (R.supportAt current) :=
  R.account.anchor_commutes (R.emitted current)

theorem RootClosure.incidence_commutes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) :
    R.account.incidenceKey (V.incidenceAt current) =
      N.incidenceAt (R.supportAt current) :=
  R.account.incidence_commutes (R.emitted current)

theorem RootClosure.lineage_commutes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (R : RootClosure N V) (current : V.Current) :
    R.account.lineageKey (V.lineageAt current) =
      N.lineageAt (R.supportAt current) :=
  R.account.lineage_commutes (R.emitted current)

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LedgerEntryEvolutionAt.toDebtLineage

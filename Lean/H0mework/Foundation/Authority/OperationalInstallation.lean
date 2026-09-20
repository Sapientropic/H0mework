import H0mework.Foundation.Runtime.OperationalSeparation
import H0mework.Foundation.Inquiry.ObstructionLineage
import H0mework.Foundation.Runtime.AnswerNext
import H0mework.Foundation.Authority.EntryDisposition
import H0mework.Foundation.Authority.SourceProjectionInventory
import H0mework.Foundation.Authority.Representation

/-!
# Fixed-root operational-search recognition

An operational search law cannot be attached after a root occurrence has
already exposed its result.  The fixed-root recognition therefore proves that
the root's complete projection inventory was formed with this exact law.

Finite, source-owned cofinal, and post-cofinal visits all read the operational
payload directly from the exact temporal root occurrence.  No domain authority
record is interposed.  A different consumer or search process remains legal
presentation data, but cannot be recognized at this root unless it pays a
full dependent, occurrence-wise commuting installation into the fixed source
inventory.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- One generated search position selected by an exact root occurrence.

The position contains only an admitted query and a prefix already generated
by the fixed search process.  It does not contain the next delivery, cut, or
continuation outcome. -/
structure SourceNativeOperationalSearchPositionAt
    {N : WorldRelationNetwork.{u}}
    {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    (communication : ActualCommunicationNetwork N)
    (sources : ActualOperationalSeparationSources communication)
    {U7 : U7ProducerCalculus N}
    (calculus : U7ObstructionEvolutionCalculus N U7)
    (process : ActualOperationalSearchProcess communication sources calculus)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    Type u where
  source : N.Support
  target : N.Support
  query : process.QueryEventAt source target
  searchCurrent : OperationalSearchCurrentAt communication source target
  rootSupport_eq_frontier :
    ledgerSource.source.toRootSource.account.supportOf occurrence =
      searchCurrent.frontier
  steps : Nat
  history : GeneratedOperationalSearchPrefixAt
    process query searchCurrent steps

/-- Exact root-ledger entry consumed by a cut emitted at this registered
search position.  The only transport is the already proved equality between
the root occurrence support and the search frontier. -/
def SourceNativeOperationalSearchPositionAt.rootDemandEntryAtCut
    {N : WorldRelationNetwork.{u}}
    {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {communication : ActualCommunicationNetwork N}
    {sources : ActualOperationalSeparationSources communication}
    {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {process : ActualOperationalSearchProcess communication sources calculus}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (position : SourceNativeOperationalSearchPositionAt
      communication sources calculus process occurrence)
    (cutEvent : sources.CutEventAt position.searchCurrent.frontier
      position.target) :
    OpenResponsibilityAt N
      (ledgerSource.source.toRootSource.account.supportOf occurrence) :=
  cast
    (congrArg (fun support => OpenResponsibilityAt N support)
      position.rootSupport_eq_frontier.symm)
    (U7ActualSuccessorSource.demandEntry
      (calculus.source.emit (sources.cutObstruction cutEvent)))

/-- Reindexing the cut demand into the root support changes no entry
identity. -/
theorem SourceNativeOperationalSearchPositionAt.rootDemandEntryAtCut_heq
    {N : WorldRelationNetwork.{u}}
    {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {communication : ActualCommunicationNetwork N}
    {sources : ActualOperationalSeparationSources communication}
    {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {process : ActualOperationalSearchProcess communication sources calculus}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (position : SourceNativeOperationalSearchPositionAt
      communication sources calculus process occurrence)
    (cutEvent : sources.CutEventAt position.searchCurrent.frontier
      position.target) :
    HEq (position.rootDemandEntryAtCut cutEvent)
      (U7ActualSuccessorSource.demandEntry
        (calculus.source.emit (sources.cutObstruction cutEvent))) := by
  unfold rootDemandEntryAtCut
  exact cast_heq _ _

/-- Canonical next search position produced by one paid continuation and the
same source-ledger successor occurrence. -/
def SourceNativeOperationalSearchPositionAt.afterContinuation
    {N : WorldRelationNetwork.{u}}
    {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {communication : ActualCommunicationNetwork N}
    {sources : ActualOperationalSeparationSources communication}
    {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {process : ActualOperationalSearchProcess communication sources calculus}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (position : SourceNativeOperationalSearchPositionAt
      communication sources calculus process occurrence)
    (continuation : GeneratedOperationalSearchContinuationAt
      (current := position.searchCurrent) process position.query position.steps)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence
      (ledgerSource.ledgerCompiler.compile occurrence))
    (rootSupport_eq_frontier :
      ledgerSource.source.toRootSource.account.supportOf
          successor.targetOccurrence =
        continuation.continuation.next.frontier) :
    SourceNativeOperationalSearchPositionAt
      communication sources calculus process successor.targetOccurrence where
  source := position.source
  target := position.target
  query := position.query
  searchCurrent := continuation.continuation.next
  rootSupport_eq_frontier := rootSupport_eq_frontier
  steps := position.steps + 1
  history := continuation.nextHistory

/-- Complete operational-search law owned by one source-native ledger source.

All fields precede the emitter.  In particular, a downstream caller cannot
replace the consumer, cut compiler, U7 calculus, process, or query position
after observing a root outcome. -/
structure SourceNativeOperationalSearchLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (ledgerSource : SourceNativeLedgerSource N V) : Type (u + 1) where
  communication : ActualCommunicationNetwork N
  sources : ActualOperationalSeparationSources communication
  U7 : U7ProducerCalculus N
  calculus : U7ObstructionEvolutionCalculus N U7
  process : ActualOperationalSearchProcess communication sources calculus
  positionAt : {current : V.Current} ->
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) ->
      SourceNativeOperationalSearchPositionAt
        communication sources calculus process occurrence
  /-- Every emitted continuation is the next position of the same admitted
  query at the source-ledger compiler's exact target occurrence. -/
  continuation_commutes : {current : V.Current} ->
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) ->
    (continuation : GeneratedOperationalSearchContinuationAt
      (current := (positionAt occurrence).searchCurrent)
      process (positionAt occurrence).query (positionAt occurrence).steps) ->
    ∃ successor : SourceNativeLedgerGeneratedSuccessorAt occurrence
        (ledgerSource.ledgerCompiler.compile occurrence),
      ∃ rootSupport_eq_frontier :
        ledgerSource.source.toRootSource.account.supportOf
            successor.targetOccurrence =
          continuation.continuation.next.frontier,
      positionAt successor.targetOccurrence =
        (positionAt occurrence).afterContinuation continuation successor
          rootSupport_eq_frontier
  /-- A cut's U7 face and the whole-ledger compiler expose the same exact
  entry disposition. -/
  cut_disposition_commutes : {current : V.Current} ->
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) ->
    (cutEvent : sources.CutEventAt
      (positionAt occurrence).searchCurrent.frontier
      (positionAt occurrence).target) ->
    process.emit (positionAt occurrence).query
        (positionAt occurrence).searchCurrent = .cut cutEvent ->
    U7DemandEntryRootDispositionCommutesAt calculus
      (calculus.source.emit (sources.cutObstruction cutEvent))
      ((positionAt occurrence).rootDemandEntryAtCut cutEvent)
      ((ledgerSource.ledgerCompiler.compile occurrence).entryDisposition
        ((positionAt occurrence).rootDemandEntryAtCut cutEvent))

namespace SourceNativeOperationalSearchLaw

variable
  {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {ledgerSource : SourceNativeLedgerSource N V}

/-- A paid continuation cannot remain a detached search certificate.  The
same source-ledger compiler generates an exact successor occurrence whose
registered search position has consumed precisely that continuation. -/
theorem continuation_target_steps_eq_succ
    (law : SourceNativeOperationalSearchLaw ledgerSource)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current)
    (continuation : GeneratedOperationalSearchContinuationAt
      (current := (law.positionAt occurrence).searchCurrent)
      law.process (law.positionAt occurrence).query
        (law.positionAt occurrence).steps) :
    ∃ successor : SourceNativeLedgerGeneratedSuccessorAt occurrence
        (ledgerSource.ledgerCompiler.compile occurrence),
      (law.positionAt successor.targetOccurrence).steps =
        (law.positionAt occurrence).steps + 1 := by
  rcases law.continuation_commutes occurrence continuation with
    ⟨successor, rootSupport_eq_frontier, commutes⟩
  refine ⟨successor, ?_⟩
  have steps_eq := congrArg
    (fun position : SourceNativeOperationalSearchPositionAt
        law.communication law.sources law.calculus law.process
          successor.targetOccurrence => position.steps)
    commutes
  exact steps_eq

/-- In particular, an exact target occurrence cannot reset a paid search to
the source step count. -/
theorem no_continuation_target_step_reset
    (law : SourceNativeOperationalSearchLaw ledgerSource)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current)
    (continuation : GeneratedOperationalSearchContinuationAt
      (current := (law.positionAt occurrence).searchCurrent)
      law.process (law.positionAt occurrence).query
        (law.positionAt occurrence).steps)
    (resets : ∀ successor : SourceNativeLedgerGeneratedSuccessorAt occurrence
        (ledgerSource.ledgerCompiler.compile occurrence),
      (law.positionAt successor.targetOccurrence).steps =
        (law.positionAt occurrence).steps) : False := by
  rcases law.continuation_target_steps_eq_succ occurrence continuation with
    ⟨successor, target_steps_eq⟩
  have impossible : (law.positionAt occurrence).steps =
      (law.positionAt occurrence).steps + 1 :=
    (resets successor).symm.trans target_steps_eq
  have no_self_succ : ∀ steps : Nat, steps ≠ Nat.succ steps := by
    intro steps
    induction steps with
    | zero => exact fun equality => Nat.noConfusion equality
    | succ steps inductionHypothesis =>
        exact fun equality => inductionHypothesis (Nat.succ.inj equality)
  exact no_self_succ _ impossible

end SourceNativeOperationalSearchLaw

/-- Cut branch emitted by the fixed operational law at one exact root
occurrence.  The private constructor stores only the actual cut payload and
emitter equation; prefix chronology is always rebuilt from `positionAt`. -/
structure SourceNativeOperationalObstructionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    (law : SourceNativeOperationalSearchLaw ledgerSource)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) : Type u where
  private mk ::
  cutEvent : law.sources.CutEventAt
    (law.positionAt occurrence).searchCurrent.frontier
    (law.positionAt occurrence).target
  emitted_eq : law.process.emit (law.positionAt occurrence).query
      (law.positionAt occurrence).searchCurrent = .cut cutEvent

/-- Delivery branch emitted at the fixed root search position.  A sibling
prefix which revisits the same current cannot be supplied to this private
constructor. -/
structure SourceNativeOperationalDeliveryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    (law : SourceNativeOperationalSearchLaw ledgerSource)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) : Type u where
  private mk ::
  target_eq : (law.positionAt occurrence).searchCurrent.frontier =
    (law.positionAt occurrence).target
  emitted_eq : law.process.emit (law.positionAt occurrence).query
      (law.positionAt occurrence).searchCurrent = .reached target_eq

namespace SourceNativeOperationalDeliveryAt

variable
  {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {ledgerSource : SourceNativeLedgerSource N V}
  {law : SourceNativeOperationalSearchLaw ledgerSource}
  {current : V.Current}
  {occurrence :
    ledgerSource.source.toRootSource.actual.OccurrenceAt current}

/-- Exact delivery prefix reconstructed from the fixed source position. -/
def generated
    (delivery : SourceNativeOperationalDeliveryAt law occurrence) :
    GeneratedOperationalDeliveryAt law.process
      (law.positionAt occurrence).query where
  steps := (law.positionAt occurrence).steps
  current := (law.positionAt occurrence).searchCurrent
  history := (law.positionAt occurrence).history
  target_eq := delivery.target_eq
  emitted_eq := delivery.emitted_eq

@[simp] theorem current_eq
    (delivery : SourceNativeOperationalDeliveryAt law occurrence) :
    delivery.generated.current = (law.positionAt occurrence).searchCurrent :=
  rfl

@[simp] theorem steps_eq
    (delivery : SourceNativeOperationalDeliveryAt law occurrence) :
    delivery.generated.steps = (law.positionAt occurrence).steps :=
  rfl

theorem history_heq
    (delivery : SourceNativeOperationalDeliveryAt law occurrence) :
    HEq delivery.generated.history (law.positionAt occurrence).history :=
  HEq.rfl

end SourceNativeOperationalDeliveryAt

namespace SourceNativeOperationalObstructionAt

variable
  {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {ledgerSource : SourceNativeLedgerSource N V}
  {law : SourceNativeOperationalSearchLaw ledgerSource}
  {current : V.Current}
  {occurrence :
    ledgerSource.source.toRootSource.actual.OccurrenceAt current}

/-- At one exact occurrence the deterministic search emitter can produce at
most one cut receipt.  Distinct cuts require distinct source occurrences. -/
instance instSubsingleton :
    Subsingleton (SourceNativeOperationalObstructionAt law occurrence) where
  allEq left right := by
    cases left
    rename_i leftCut leftEmitted
    cases right
    rename_i rightCut rightEmitted
    have event_eq := leftEmitted.symm.trans rightEmitted
    have cut_eq : leftCut = rightCut := by
      injection event_eq
    cases cut_eq
    rfl

/-- Exact cut prefix reconstructed from the fixed source position. -/
def generated
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    GeneratedOperationalObstructionAt law.process
      (law.positionAt occurrence).query where
  steps := (law.positionAt occurrence).steps
  current := (law.positionAt occurrence).searchCurrent
  history := (law.positionAt occurrence).history
  cutEvent := obstruction.cutEvent
  emitted_eq := obstruction.emitted_eq

@[simp] theorem current_eq
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    obstruction.generated.current =
      (law.positionAt occurrence).searchCurrent :=
  rfl

@[simp] theorem steps_eq
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    obstruction.generated.steps = (law.positionAt occurrence).steps :=
  rfl

theorem history_heq
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    HEq obstruction.generated.history (law.positionAt occurrence).history :=
  HEq.rfl

end SourceNativeOperationalObstructionAt

namespace SourceNativeOperationalSearchLaw

/-- Existing operational search exhausts the exact generated prefix into
delivery, obstruction, or one paid continuation.

This executor is private: a bare source occurrence is not yet a registered
temporal occurrence.  Public operational authority is exposed only through
`SourceNativeOperationalSearchRecognitionAt.generatedTemporalOutcomeAt`. -/
private def exhaustiveAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    (law : SourceNativeOperationalSearchLaw ledgerSource)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    let position := law.positionAt occurrence
    SourceNativeOperationalDeliveryAt law occurrence ⊕
      (SourceNativeOperationalObstructionAt law occurrence ⊕
        GeneratedOperationalSearchContinuationAt
          (current := position.searchCurrent)
          law.process position.query position.steps) := by
  dsimp only
  match emitted : law.process.emit (law.positionAt occurrence).query
      (law.positionAt occurrence).searchCurrent with
  | .reached target_eq =>
      exact .inl ⟨target_eq, emitted⟩
  | .cut cutEvent =>
      exact .inr (.inl ⟨cutEvent, emitted⟩)
  | .continued continuation =>
      exact .inr (.inr
        { history := (law.positionAt occurrence).history
          continuation := continuation
          emitted_eq := emitted })

end SourceNativeOperationalSearchLaw

namespace SourceNativeOperationalDeliveryAt

/-- Every delivery receipt is definitionally the reached branch emitted by
the fixed source-owned operational law at that exact occurrence. -/
theorem rootOutcome_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {law : SourceNativeOperationalSearchLaw ledgerSource}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (delivery : SourceNativeOperationalDeliveryAt law occurrence) :
    law.exhaustiveAt occurrence = .inl delivery := by
  unfold SourceNativeOperationalSearchLaw.exhaustiveAt
  split
  · rename_i target_eq emitted
    apply congrArg Sum.inl
    rcases delivery with ⟨deliveryTargetEq, deliveryEmittedEq⟩
    have emitted_eq := emitted.symm.trans deliveryEmittedEq
    cases emitted_eq
    rfl
  · rename_i cutEvent emitted
    have impossible := emitted.symm.trans delivery.emitted_eq
    cases impossible
  · rename_i continuation emitted
    have impossible := emitted.symm.trans delivery.emitted_eq
    cases impossible

end SourceNativeOperationalDeliveryAt

namespace SourceNativeOperationalObstructionAt

/-- Every cut receipt is definitionally the cut branch emitted by the fixed
source-owned operational law at that exact occurrence. -/
theorem rootOutcome_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {law : SourceNativeOperationalSearchLaw ledgerSource}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    law.exhaustiveAt occurrence = .inr (.inl obstruction) := by
  unfold SourceNativeOperationalSearchLaw.exhaustiveAt
  split
  · rename_i target_eq emitted
    have impossible := emitted.symm.trans obstruction.emitted_eq
    cases impossible
  · rename_i cutEvent emitted
    apply congrArg Sum.inr
    apply congrArg Sum.inl
    exact Subsingleton.elim _ _
  · rename_i continuation emitted
    have impossible := emitted.symm.trans obstruction.emitted_eq
    cases impossible

/-- The cut obstruction's exact U7 compiler output. -/
def u7Evolution
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {law : SourceNativeOperationalSearchLaw ledgerSource}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :=
  law.calculus.generated obstruction.generated.cutEvolution.cut.obstruction

/-- The installed operational cut and the canonical whole-ledger compiler
give the same disposition to its demand entry. -/
theorem dispositionCommutes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {law : SourceNativeOperationalSearchLaw ledgerSource}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    U7DemandEntryRootDispositionCommutesAt law.calculus
      obstruction.u7Evolution.1
      ((law.positionAt occurrence).rootDemandEntryAtCut
        obstruction.cutEvent)
      ((ledgerSource.ledgerCompiler.compile occurrence).entryDisposition
        ((law.positionAt occurrence).rootDemandEntryAtCut
          obstruction.cutEvent)) :=
  law.cut_disposition_commutes occurrence obstruction.cutEvent
    obstruction.emitted_eq

/-- The emitted cut frontier is the exact support of the root occurrence's
complete live ledger. -/
theorem frontier_eq_rootSupport
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {law : SourceNativeOperationalSearchLaw ledgerSource}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    obstruction.generated.current.frontier =
      ledgerSource.source.toRootSource.account.supportOf occurrence :=
  (congrArg OperationalSearchCurrentAt.frontier obstruction.current_eq).trans
    (law.positionAt occurrence).rootSupport_eq_frontier.symm

/-- The demand consumed by the exact U7 successor event is an existing entry
of the same root ledger.  It is generated by the U7 actual-event source and
only reindexed along the already proved frontier/root support equality. -/
def rootDemandEntry
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    {law : SourceNativeOperationalSearchLaw ledgerSource}
    {current : V.Current}
    {occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current}
    (obstruction : SourceNativeOperationalObstructionAt law occurrence) :
    OpenResponsibilityAt N
      (ledgerSource.source.toRootSource.account.supportOf occurrence) :=
  (law.positionAt occurrence).rootDemandEntryAtCut obstruction.cutEvent

/-- Exact root-ledger authority of the generated U7 demand.  The obstruction
already fixes the entry, so incidence is the existing living causal authority
itself rather than a second wrapper. -/
abbrev SourceNativeRootU7DemandIncidenceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {law : SourceNativeOperationalSearchLaw
      root.toAuthoritativeRoot.toLedgerRoot.source}
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (obstruction : SourceNativeOperationalObstructionAt law
      (root.emitted visit.current)) :
    Type (u + 2) :=
  ULift.{u + 2, u + 1}
    (SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
      obstruction.rootDemandEntry)

namespace SourceNativeRootU7DemandIncidenceAt

/-- Field-style readout retained for existing consumers. -/
def causalEntryAuthority
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {law : SourceNativeOperationalSearchLaw
      root.toAuthoritativeRoot.toLedgerRoot.source}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {obstruction : SourceNativeOperationalObstructionAt law
      (root.emitted visit.current)}
    (incidence : SourceNativeRootU7DemandIncidenceAt visit obstruction) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
      obstruction.rootDemandEntry :=
  incidence.down

end SourceNativeRootU7DemandIncidenceAt

/-- The exact U7 event and the already generated causal entry lineage produce
the live root incidence.  No bare entry, occurrence-local late row, parallel
obligation, or empty ledger is accepted here. -/
private def generatedRootDemandIncidence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {law : SourceNativeOperationalSearchLaw
      root.toAuthoritativeRoot.toLedgerRoot.source}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (obstruction : SourceNativeOperationalObstructionAt law
      (root.emitted visit.current))
    (causalEntryAuthority :
      SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
        obstruction.rootDemandEntry) :
    SourceNativeRootU7DemandIncidenceAt visit obstruction :=
  ULift.up causalEntryAuthority

end SourceNativeOperationalObstructionAt

/-- Exact operational coordinate generated at one source-native occurrence.

This is the coface coordinate itself, not a second authority record wrapping
that coordinate. -/
abbrev SourceNativeOperationalSearchOutcomeAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    (law : SourceNativeOperationalSearchLaw ledgerSource)
    {current : V.Current}
    (occurrence :
      ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    Type u :=
  let position := law.positionAt occurrence
  SourceNativeOperationalDeliveryAt law occurrence ⊕
    (SourceNativeOperationalObstructionAt law occurrence ⊕
      GeneratedOperationalSearchContinuationAt
        (current := position.searchCurrent)
        law.process position.query position.steps)

/-- The source-native search as a singleton projection component.  The token
selects one coordinate; delivery, cut, continuation and their exact root
provenance remain in the dependent payload. -/
def SourceNativeOperationalSearchLaw.toProjectionLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {ledgerSource : SourceNativeLedgerSource N V}
    (law : SourceNativeOperationalSearchLaw ledgerSource) :
    SourceNativeProjectionLaw ledgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ =>
    SourceNativeOperationalSearchOutcomeAt law occurrence
  project := fun _ {_current} occurrence _ => law.exhaustiveAt occurrence

/-- Operational search extends the existing projection inventory instead of
living beside it.  The distinguished constructor seals the exact source-owned
law into the root identity; inherited constructors preserve every pre-existing
chart. -/
inductive SourceNativeOperationalProjection (Base : Type u) : Type u
  | operational
  | inherited (projection : Base)

/-- Extend one authority source with an operational projection whose payload
is definitionally generated by `law`.  Two different operational laws can no
longer erase to the same `SourceNativeAuthoritySource`. -/
def SourceNativeAuthoritySource.withOperationalSearch
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeOperationalSearchLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeAuthoritySource N V where
  restructuringSource := base.restructuringSource
  eventInventoryAdmission := base.eventInventoryAdmission
  lawSurface := base.lawSurface
  projectionLaw :=
    { Projection := SourceNativeOperationalProjection
        base.projectionLaw.Projection
      ActiveAt := fun projection {_current} occurrence =>
        match projection with
        | .operational => PUnit
        | .inherited inherited =>
            base.projectionLaw.ActiveAt inherited occurrence
      InactiveAt := fun projection {_current} occurrence =>
        match projection with
        | .operational => PEmpty
        | .inherited inherited =>
            base.projectionLaw.InactiveAt inherited occurrence
      classify := by
        intro projection current occurrence
        cases projection with
        | operational => exact .inl PUnit.unit
        | inherited inherited =>
            exact base.projectionLaw.classify inherited occurrence
      PayloadAt := fun projection {_current} occurrence active =>
        match projection with
        | .operational =>
            SourceNativeOperationalSearchOutcomeAt law occurrence
        | .inherited inherited =>
            base.projectionLaw.PayloadAt inherited occurrence active
      project := by
        intro projection current occurrence active
        cases projection with
        | operational =>
            exact law.exhaustiveAt occurrence
        | inherited inherited =>
            exact base.projectionLaw.project inherited occurrence active }

/-- Installing an operational coordinate preserves every coordinate already
present in the source inventory.  This is the canonical coface inclusion;
the inherited outcome is not reconstructed from an observer shadow. -/
def SourceNativeProjectionLaw.InstallationAt.inheritedByOperational
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeOperationalSearchLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeProjectionLaw.InstallationAt base.projectionLaw
      (base.withOperationalSearch law).projectionLaw where
  embed := SourceNativeOperationalProjection.inherited
  embed_injective := by
    intro left right equality
    injection equality
  outcome_heq := by
    intro current occurrence projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      SourceNativeAuthoritySource.withOperationalSearch]
    cases base.projectionLaw.classify projection occurrence <;> rfl

/-- Compatibility installation for sources constructed with
`withOperationalSearch`.  Recognition consumes this singleton component and
cannot reconstruct or replace the base source. -/
def SourceNativeProjectionLaw.InstallationAt.operationalComponent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeOperationalSearchLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
      (base.withOperationalSearch law).projectionLaw where
  embed := fun _ => SourceNativeOperationalProjection.operational
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    rfl

/-- Recognition that one already fixed living root sealed this operational
law into its source projection inventory.

The record owns no emitter and cannot create a root.  `installation` is the
mechanism-faithfulness gate: the operational inventory must be a complete,
occurrence-wise commuting coface of the fixed pre-emitter source inventory.
Later visibility uplifts may retain it through canonical inherited
coordinates. -/
structure SourceNativeOperationalSearchRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  operationalLaw :
    SourceNativeOperationalSearchLaw
      root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
      operationalLaw.toProjectionLaw
      root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeOperationalSearchRecognitionAt

/-- Distinguished operational coordinate embedded into the complete
pre-emitter inventory.  No global domain-name table chooses it. -/
def rootOperationalProjection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeOperationalSearchRecognitionAt root) :
    root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  recognition.installation.embed PUnit.unit

/-- Generate one live U7 demand incidence from the exact root entry lineage.

The operational obstruction contributes the demand identity; the root ledger
contributes its causal authority.  No parallel disposition compiler is
interposed between them. -/
def generatedRootDemandIncidence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeOperationalSearchRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (obstruction : SourceNativeOperationalObstructionAt
      recognition.operationalLaw (root.emitted visit.current))
    (causalEntryAuthority :
      SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
        obstruction.rootDemandEntry) :
    SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt
      (root := root)
      visit obstruction :=
  SourceNativeOperationalObstructionAt.generatedRootDemandIncidence
    obstruction causalEntryAuthority

/-- Exact operational coordinate at one finite, cofinal, or post-cofinal
visit.  It is read directly from the fixed root occurrence. -/
def generatedTemporalOutcomeAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeOperationalSearchRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeOperationalSearchOutcomeAt recognition.operationalLaw
      (root.emitted visit.current) :=
  recognition.operationalLaw.exhaustiveAt (root.emitted visit.current)

/-- The source-level operational payload is heterogeneously identical to the
operational coordinate of the fixed root occurrence.  This is the coface
identity: the domain value is not reconstructed from a quotient shadow and
cannot be replaced after emission. -/
theorem rootOperationalFace_heq_outcome
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeOperationalSearchRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        recognition.rootOperationalProjection (root.emitted visit.current))
      (recognition.operationalLaw.toProjectionLaw.outcomeAt
        PUnit.unit (root.emitted visit.current)) := by
  unfold rootOperationalProjection
  exact recognition.installation.outcome_heq
    (root.emitted visit.current) PUnit.unit

/-- The public operational outcome is a dependent face of the canonical
answer-and-next compiler at the same temporal visit.  The outer `PUnit` is
only the fixed projection law's active token; search payload and living next
remain generated by the root. -/
theorem installedAuthority_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeOperationalSearchRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootOperationalProjection)
        (Sum.inl ⟨PUnit.unit,
          recognition.generatedTemporalOutcomeAt visit⟩ :
            SourceNativeProjectionFiberAt
              recognition.operationalLaw.toProjectionLaw PUnit.unit
              (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  exact
    (root.canonicalCausalAnswerAndNext
      (ULift.up visit)).installedSubsystemAuthority_factorizes
        recognition.installation PUnit.unit

/-- The exact search frontier is the support whose complete live ledger was
compiled for this temporal root occurrence. -/
theorem operationalFrontier_eq_rootSupport
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeOperationalSearchRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :
    (recognition.operationalLaw.positionAt
      (root.emitted visit.current)).searchCurrent.frontier =
      root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current) :=
  (recognition.operationalLaw.positionAt
    (root.emitted visit.current)).rootSupport_eq_frontier.symm

end SourceNativeOperationalSearchRecognitionAt

namespace SourceNativeOperationalDeliveryAt

/-- The delivery is already the exact registered root branch; no second
target-consumer registration token is needed. -/
theorem temporalOutcome_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (delivery : SourceNativeOperationalDeliveryAt recognition.operationalLaw
      (root.emitted visit.current)) :
    recognition.generatedTemporalOutcomeAt visit = .inl delivery :=
  delivery.rootOutcome_eq

/-- The reached target is the support of the same exact root occurrence. -/
theorem target_eq_rootSupport
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (delivery : SourceNativeOperationalDeliveryAt recognition.operationalLaw
      (root.emitted visit.current)) :
    (recognition.operationalLaw.positionAt
        (root.emitted visit.current)).target =
      root.toAuthoritativeRoot.toRoot.supportAt visit.current :=
  delivery.target_eq.symm.trans
    (recognition.operationalLaw.positionAt
      (root.emitted visit.current)).rootSupport_eq_frontier.symm

/-- Exact target-consumer entry readout reindexed to the root support.

The consumer event, observation and effect are definitionally inside
`generated`.  Responsibility settlement consumes its source-generated
temporal causal-entry authority separately. -/
def rootConsumerEntry
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (delivery : SourceNativeOperationalDeliveryAt recognition.operationalLaw
      (root.emitted visit.current)) :
    OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toRoot.supportAt visit.current) := by
  rw [← delivery.target_eq_rootSupport]
  exact recognition.operationalLaw.sources.consumerSource.entryAt
    delivery.generated.delivery.consumerEvent

/-- A delivery effect, its exact temporal compiler image and living successor
are the same installed operational face. -/
theorem rootEffect_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (delivery : SourceNativeOperationalDeliveryAt recognition.operationalLaw
      (root.emitted visit.current)) :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootOperationalProjection)
        (Sum.inl ⟨PUnit.unit, Sum.inl delivery⟩ :
          SourceNativeProjectionFiberAt
            recognition.operationalLaw.toProjectionLaw PUnit.unit
            (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  have factorization := recognition.installedAuthority_factorizes visit
  rw [delivery.temporalOutcome_eq] at factorization
  exact factorization

/-- The delivery effect and the consumer entry's own causal authority jointly
generate target answer-and-next at this exact root visit. -/
def targetAnswerAndNext
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (delivery : SourceNativeOperationalDeliveryAt recognition.operationalLaw
      (root.emitted visit.current))
    (causalEntryAuthority :
      SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
        (delivery.rootConsumerEntry (root := root)
          (recognition := recognition) (visit := visit))) :
    SourceNativeLivingCausalEntryAnswerAndNextAt root visit
      (delivery.rootConsumerEntry (root := root)
        (recognition := recognition) (visit := visit))
      causalEntryAuthority :=
  root.generatedCausalEntryAnswerAndNextAt visit
    (delivery.rootConsumerEntry (root := root)
      (recognition := recognition) (visit := visit))
    causalEntryAuthority

end SourceNativeOperationalDeliveryAt

namespace SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt

/-- A cut whose demand already has exact root-ledger causal authority enters
the sole living answer-and-next compiler at that same temporal visit. -/
def answerAndNext
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {obstruction : SourceNativeOperationalObstructionAt
      recognition.operationalLaw (root.emitted visit.current)}
    (incidence :
      SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt
        (root := root) visit obstruction) :
    SourceNativeLivingCausalEntryAnswerAndNextAt root visit
      obstruction.rootDemandEntry incidence.causalEntryAuthority :=
  root.generatedCausalEntryAnswerAndNextAt visit obstruction.rootDemandEntry
    incidence.causalEntryAuthority

/-- A live U7 demand incidence is the cut branch of the same installed
operational face, exact temporal compiler image, and living successor.  Its
causal-entry authority remains the sole root-ledger admission witness. -/
theorem installedAuthority_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeOperationalSearchRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {obstruction : SourceNativeOperationalObstructionAt
      recognition.operationalLaw (root.emitted visit.current)}
    (_incidence :
      SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt
        (root := root) visit obstruction) :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootOperationalProjection)
        (Sum.inl ⟨PUnit.unit, Sum.inr (Sum.inl obstruction)⟩ :
          SourceNativeProjectionFiberAt
            recognition.operationalLaw.toProjectionLaw PUnit.unit
            (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit := by
  dsimp only
  have factorization := recognition.installedAuthority_factorizes visit
  have outcome_eq : recognition.generatedTemporalOutcomeAt visit =
      .inr (.inl obstruction) :=
    obstruction.rootOutcome_eq
  rw [outcome_eq] at factorization
  exact factorization

end SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

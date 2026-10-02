import H0mework.Foundation.Responsibility.JointSource.Successor.Step
import H0mework.Foundation.Ledger.BranchAuthority
/-! Compile a packet-valued source programme with one finite mathematical row
and the original complete ledger as a source-generated remainder. This adapter
consumes that programme; one packet does not generate a reader at all currents. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw
open SourceOperationEffects DebtActivationWorld DebtActivationLedger
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)
-- This source programme is supplied by the original law's actual compiler, not by a future-target certificate.
variable (packetAt : (current : V.Current) → Packet lower current)
abbrev Current := Sigma (EventAt registered)
abbrev World := ExtendedNetwork N (Idle.law registered.input.environment registered.input.expression)
abbrev scope := Idle.law registered.input.environment registered.input.expression
abbrev supportAt (current : Current registered) : (World registered).Support :=
  ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted current.1), some current.2.state⟩
structure WriteAt (current : Current registered) : Type u where
  packet : Packet lower current.1
  joined : JoinedAt packet current.2

def write (current : Current registered) : WriteAt registered current :=
  ⟨packetAt current.1, join (packetAt current.1) current.2⟩

def nextEvent {current : Current registered} (actual : WriteAt registered current) :
    EventAt registered actual.packet.targetCurrent :=
  successorEvent current.2 actual.packet.successor

def nextCurrent {current : Current registered} (actual : WriteAt registered current) : Current registered :=
  ⟨actual.packet.targetCurrent, nextEvent registered actual⟩

def originalTarget {current : Current registered} (target : V.Current)
    (sourceNext : (lower.source.source.toRootSource.actual.compile (lower.emitted current.1)).nextCurrent? = some target) :
    Current registered := by
  let actual := write registered packetAt current
  have same : actual.packet.targetCurrent = target :=
    Option.some.inj (actual.packet.actual_next.symm.trans sourceNext)
  exact ⟨target, same ▸ nextEvent registered actual⟩

def vocabulary : Vocabulary where
  Current := Current registered
  Anchor := V.Anchor
  Incidence := V.Incidence
  Lineage := V.Lineage
  anchorAt := fun current => V.anchorAt current.1
  incidenceAt := fun current => V.incidenceAt current.1
  lineageAt := fun current => V.lineageAt current.1
  NativeWriteAt := WriteAt registered
  RelationWriteAt := fun current => {payload : V.RelationWriteAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .relationWrite payload}
  ContinuedTransportAt := fun current => {payload : V.ContinuedTransportAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .continuedTransport payload}
  BorromeanRedirectAt := fun current => {payload : V.BorromeanRedirectAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .borromeanRedirect payload}
  FaithfulTerminalAt := fun current => {payload : V.FaithfulTerminalAt current.1 //
    lower.source.source.toRootSource.actual.compile (lower.emitted current.1) = .faithfulTerminal payload}
  nativeTarget := nextCurrent registered
  relationTarget := fun payload => originalTarget registered packetAt _ (by rw [payload.2]; rfl)
  continuedTarget := fun payload => originalTarget registered packetAt _ (by rw [payload.2]; rfl)
  redirectTarget := fun payload => originalTarget registered packetAt _ (by rw [payload.2]; rfl)

abbrev JointV := vocabulary registered packetAt
inductive SourceEventAt : (current : Current registered) → (World registered).Support → Type u
  | generated (current : Current registered) : SourceEventAt current (supportAt registered current)

def eventAlgebra : SourceNativeEventAlgebra (World registered) (JointV registered packetAt) where
  EventAt := SourceEventAt registered
  compile := by
    intro current support event
    cases event
    exact .nativeWrite (write registered packetAt current)
  AffectedInventoryAt := fun {current} {_support} _ =>
    Option (lower.source.source.law.AffectedInventoryAt (lower.emitted current.1).2)
  affectedInventoryPresentation := by
    intro current support event
    cases event
    exact activeInventoryPresentation (law := scope registered) current.2.state
      (lower.source.source.law.affectedInventoryPresentation (lower.emitted current.1).2)
  anchorKey := lower.source.source.law.anchorKey
  incidenceKey := lower.source.source.law.incidenceKey
  lineageKey := lower.source.source.law.lineageKey
  anchor_commutes := by
    intro current support event
    cases event
    exact lower.source.source.law.anchor_commutes (lower.emitted current.1).2
  incidence_commutes := by
    intro current support event
    cases event
    exact lower.source.source.law.incidence_commutes (lower.emitted current.1).2
  lineage_commutes := by
    intro current support event
    cases event
    exact lower.source.source.law.lineage_commutes (lower.emitted current.1).2

def source : SourceNativeSource (World registered) (JointV registered packetAt) where
  initial := ⟨origin, initialEvent registered⟩
  law := eventAlgebra registered packetAt

def emitted (current : Current registered) : (source registered packetAt).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt registered current, .generated current⟩
def originalOccurrence {current : Current registered}
    (_occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current) :
    lower.source.source.toRootSource.actual.OccurrenceAt current.1 := lower.emitted current.1

def targetCurrent (current : Current registered) : Current registered :=
  nextCurrent registered (write registered packetAt current)
def targetOccurrence (current : Current registered) :
    (source registered packetAt).toRootSource.actual.OccurrenceAt (targetCurrent registered packetAt current) :=
  emitted registered packetAt (targetCurrent registered packetAt current)
def whole (current : Current registered) :
    LedgerWriteEvolutionAt (World registered) ⟨supportAt registered current⟩
      ⟨supportAt registered (targetCurrent registered packetAt current)⟩ :=
  (write registered packetAt current).joined.wholeEvolution

def mathEntry (current : Current registered) : OpenResponsibilityAt (World registered) (supportAt registered current) :=
  debtEntry (N := N) (law := scope registered)
    (lower.source.source.toRootSource.account.supportOf (lower.emitted current.1)) current.2.state

inductive RawRowAt :
    {current : Current registered} →
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (World registered).Support} →
    OpenResponsibilityAt (World registered) ((source registered packetAt).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt (World registered) targetSupport → Type u
  | destination (current : Current registered)
      (entry : OpenResponsibilityAt (World registered) (supportAt registered current)) :
      RawRowAt (emitted registered packetAt current) entry
        ((whole registered packetAt current).destination entry).1
  | origin (current : Current registered)
      (entry : OpenResponsibilityAt (World registered) (supportAt registered (targetCurrent registered packetAt current))) :
      RawRowAt (emitted registered packetAt current)
        ((whole registered packetAt current).origin entry).1 entry

inductive RemainderAt :
    {current : Current registered} →
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current) →
    (World registered).Support → Type u
  | generated (current : Current registered) : RemainderAt (emitted registered packetAt current)
      (supportAt registered (targetCurrent registered packetAt current))

noncomputable def remainderSource :
    LedgerTransportedRemainderSourceAt (source registered packetAt) (RawRowAt registered packetAt) where
  OccurrenceAt := RemainderAt registered packetAt
  emit? := by
    classical
    intro current occurrence targetSupport
    rcases occurrence with ⟨support, event⟩
    cases event
    exact if same : supportAt registered (targetCurrent registered packetAt current) = targetSupport
      then some (same ▸ RemainderAt.generated current) else none
  compileEvolution := by
    intro current occurrence targetSupport event
    cases event
    exact whole registered packetAt current
  compileExact := by
    intro current occurrence targetSupport event
    cases event
    exact { destination := fun entry => .destination current entry
            origin := fun entry => .origin current entry }

def rowSource : LedgerWriteRowSourceAt (source registered packetAt) (RawRowAt registered packetAt) where
  IncidenceOccurrenceAt := RawRowAt registered packetAt
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    cases event with
    | destination entry => exact ((whole registered packetAt current).destination entry).2
    | origin entry => exact ((whole registered packetAt current).origin entry).2
  compileExact := fun event => event
  transportedRemainderSource := remainderSource registered packetAt

def rows (current : Current registered) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource registered packetAt) (emitted registered packetAt current)
      ⟨supportAt registered (targetCurrent registered packetAt current)⟩ where
  size := 1
  sourceEntryAt := fun _ => mathEntry registered current
  targetEntryAt := fun _ => ((whole registered packetAt current).destination (mathEntry registered current)).1
  rowAt := fun _ => (rowSource registered packetAt).generate (.destination current (mathEntry registered current))

def coverage (current : Current registered) : LedgerTransportedRemainderCoverageAt (rows registered packetAt current) where
  destinationIndex := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => exact none
    | inr debt =>
        rcases opened with ⟨⟨same⟩⟩
        cases same
        exact some ⟨⟨0, by change 0 < 1; decide⟩, rfl⟩
  originIndex := fun _ => none

noncomputable def remainder (current : Current registered) :
    GeneratedLedgerTransportedRemainderAt (rowSource registered packetAt) (emitted registered packetAt current)
      ⟨supportAt registered (targetCurrent registered packetAt current)⟩ :=
  (rowSource registered packetAt).generateTransportedRemainder
    (emitted registered packetAt current) ⟨supportAt registered (targetCurrent registered packetAt current)⟩
    (.generated current) (by simp [rowSource, remainderSource, emitted])

noncomputable def patch (current : Current registered) :
    FiniteGeneratedLedgerWritePatchAt (rowSource registered packetAt) (emitted registered packetAt current)
      ⟨supportAt registered (targetCurrent registered packetAt current)⟩ :=
  .transportedRemainder (rows registered packetAt current) (coverage registered packetAt current)
    (remainder registered packetAt current)

private theorem ledger_ext {W : WorldRelationNetwork.{u}} {source target : CompleteLiveLedgerAt W}
    (first second : LedgerWriteEvolutionAt W source target)
    (destination : first.destination = second.destination) (origin : first.origin = second.origin) : first = second := by
  cases first
  cases second
  cases destination
  cases origin
  rfl

theorem patch_fold (current : Current registered) :
    (patch registered packetAt current).toLedgerWriteEvolution = whole registered packetAt current := by
  apply ledger_ext
  · funext entry
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr debt =>
        rcases opened with ⟨⟨same⟩⟩
        cases same
        rfl
  · rfl

inductive IncidenceAt :
    {current : Current registered} →
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current) →
    (World registered).Incidence → (World registered).Incidence → Type u
  | generated (current : Current registered) : IncidenceAt (emitted registered packetAt current)
      ((World registered).incidenceAt (supportAt registered current))
      ((World registered).incidenceAt (supportAt registered (targetCurrent registered packetAt current)))

noncomputable def compiler : SourceNativeLedgerCompiler (source registered packetAt) where
  IncidenceTransitionAt := IncidenceAt registered packetAt
  ExactTransitionAt := RawRowAt registered packetAt
  exact_incidence := by
    intro current occurrence targetSupport sourceEntry targetEntry row
    cases row <;> exact .generated _
  exact_lineage := fun row =>
    ((rowSource registered packetAt).compileEvolution row).toDebtLineage.lineage_eq
  writeRowSource := rowSource registered packetAt
  terminalRowSource := LedgerTerminalRowSourceAt.empty (source registered packetAt)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact .nativeWrite (write registered packetAt current) rfl
      (targetOccurrence registered packetAt current)
      (patch registered packetAt current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨patch registered packetAt current, rfl⟩

theorem compile_emitted (current : Current registered) :
    (compiler registered packetAt).compile (emitted registered packetAt current) =
      .nativeWrite (write registered packetAt current) rfl
        (targetOccurrence registered packetAt current) (whole registered packetAt current) := by
  exact congrArg (fun ledger =>
    (SourceNativeLedgerEvolutionAt.nativeWrite (write registered packetAt current) rfl
      (targetOccurrence registered packetAt current) ledger :
      SourceNativeLedgerEvolutionAt (source registered packetAt) (emitted registered packetAt current)))
    (patch_fold registered packetAt current)

noncomputable def ledgerRoot : SourceNativeLedgerRootClosure (World registered) (JointV registered packetAt) where
  source := { source := source registered packetAt, ledgerCompiler := compiler registered packetAt }
  emitted := emitted registered packetAt
  compiler_commutes := fun _ => rfl

theorem original_next (current : Current registered) :
    (lower.source.source.toRootSource.actual.compile (lower.emitted current.1)).nextCurrent? =
      some (targetCurrent registered packetAt current).1 := (packetAt current.1).actual_next

theorem math_next (current : Current registered) :
    (targetCurrent registered packetAt current).2.state = mathTarget current.2 := rfl

end RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection

/-!
# M10 occurrence-capacity root-source fixture

This file is regression scaffolding, not a production root, ledger abstraction,
or registry.  It instantiates existing living-law constructors with one root
support, one open row of progress budget `2`, one canonical complete patch,
and one native self-loop successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10OccurrenceCapacityRootSourceFixture

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def network : WorldRelationNetwork where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Unit
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => PUnit
  openClaimAt := fun _ => ()
  openProgressBudgetAt := fun _ => 2
  HoldsAt := fun _ _ => PUnit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := fun obstruction => nomatch obstruction
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev N := network

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

def entry : OpenResponsibilityAt N () := ⟨(), PUnit.unit⟩

@[simp] theorem entry_progressBudget : entry.progressBudget = 2 := rfl

theorem entry_unique (candidate : OpenResponsibilityAt N ()) :
    candidate = entry := by
  rcases candidate with ⟨responsibility, openAt⟩
  cases responsibility
  cases openAt
  rfl

def openPresentation :
    ConstructivePresentation Unit (OpenResponsibilityAt N ()) where
  forward := fun _ => entry
  backward := fun _ => ()
  backward_forward := fun _ => rfl
  forward_backward := entry_unique

def eventLaw : SourceNativeEventAlgebra N V where
  EventAt := fun _ _ => PUnit
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := fun _ => openPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := fun _ => ()
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl

def nativeSource : SourceNativeSource N V where
  initial := ()
  law := eventLaw

def emitted (_current : V.Current) :
    nativeSource.toRootSource.actual.OccurrenceAt () :=
  ⟨(), PUnit.unit⟩

abbrev liveLedger : CompleteLiveLedgerAt N := ⟨()⟩

abbrev ExactTransitionAt
    {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (_sourceEntry : OpenResponsibilityAt N
      (nativeSource.toRootSource.account.supportOf occurrence))
    (_targetEntry : OpenResponsibilityAt N targetSupport) :=
  PUnit

abbrev IncidenceOccurrenceAt
    {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt N
      (nativeSource.toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt N targetSupport) :=
  LedgerEntryEvolutionAt N sourceEntry targetEntry

def writeRowSource : LedgerWriteRowSourceAt nativeSource
    ExactTransitionAt where
  IncidenceOccurrenceAt := IncidenceOccurrenceAt
  compileEvolution := fun event => event
  compileExact := fun _ => PUnit.unit

def generatedPatch
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ()) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence liveLedger := by
  rcases occurrence with ⟨support, event⟩
  cases support
  cases event
  exact .complete
    { size := 1
      sourceEntryAt := fun _ => entry
      targetEntryAt := fun _ => entry
      rowAt := fun _ =>
        writeRowSource.generate (.carried rfl HEq.rfl) }
    { destinationIndex := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
      originIndex := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
      destination_sound := fun candidate => (entry_unique candidate).symm
      origin_sound := fun candidate => (entry_unique candidate).symm }

def ledgerCompiler : SourceNativeLedgerCompiler nativeSource where
  IncidenceTransitionAt := fun _occurrence _source _target => PUnit
  ExactTransitionAt := ExactTransitionAt
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty nativeSource
  compile := by
    intro current occurrence
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support
    cases event
    exact .nativeWrite PUnit.unit rfl (emitted ())
      (generatedPatch (emitted ())).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support
    cases event
    exact ⟨generatedPatch (emitted ()), rfl⟩

def ledgerSource : SourceNativeLedgerSource N V where
  source := nativeSource
  ledgerCompiler := ledgerCompiler

def restructuringLaw : SourceNativeLedgerRestructuringLaw nativeSource :=
  identityOnlyWorldLedgerRestructuringLaw nativeSource PUnit.unit
    (fun _support _responsibility => by
      change Subsingleton PUnit
      infer_instance)

def restructuringCertification
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ()) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases support
  cases event
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ =>
      (entry_unique left).trans (entry_unique right).symm)
    (fun left right _ =>
      (entry_unique left).trans (entry_unique right).symm)

def restructuringCompiler :
    SourceNativeRestructuringLedgerCompiler nativeSource where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := nativeSource
  compiler := restructuringCompiler

def baseProjectionLaw :
    SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} _occurrence _active => PUnit
  project := fun _projection {_current} _occurrence _active => PUnit.unit

def baseAuthoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := baseProjectionLaw

def sourceRow : SourceNativeFiniteLedgerPatchGeneratedEntryAt nativeSource
    ledgerCompiler.ExactTransitionAt ledgerCompiler.writeRowSource
    ledgerCompiler.terminalRowSource
    (ledgerCompiler.compile (emitted ()))
    (ledgerCompiler.compilePatch (emitted ())) entry :=
  (sourceNativeFiniteLedgerPatchGeneratedEntry? nativeSource
      ledgerCompiler.ExactTransitionAt ledgerCompiler.writeRowSource
      ledgerCompiler.terminalRowSource
      (ledgerCompiler.compile (emitted ()))
      (ledgerCompiler.compilePatch (emitted ())) entry).get (by rfl)

def successor : SourceNativeLedgerGeneratedSuccessorAt (emitted ())
    (ledgerCompiler.compile (emitted ())) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (ledgerCompiler.compile (emitted ()))).get (by rfl)

@[simp] theorem successor_targetOccurrence_eq :
    successor.targetOccurrence = emitted () :=
  rfl

end M10OccurrenceCapacityRootSourceFixture
end Society
end ProcessGame
end SaturationMonoid

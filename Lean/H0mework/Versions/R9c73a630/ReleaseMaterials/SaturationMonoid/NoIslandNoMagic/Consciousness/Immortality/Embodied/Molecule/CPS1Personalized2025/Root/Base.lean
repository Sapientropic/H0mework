import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root.NativeCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Registration
import H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection

/-! Source-owned ledger for the fixed coding/independent-assay comparison. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace CPS1Personalized2025.Root

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame.Society.Renewal

noncomputable section

def network : WorldRelationNetwork where
  Support := Unit
  Anchor := String
  Incidence := String
  Lineage := String
  Responsibility := Responsibility
  Claim := Claim
  anchorAt := fun _ => captureKey
  incidenceAt := fun _ => incidenceKey
  lineageAt := fun _ => comparisonLineage
  OpenAt := fun _ _ => PUnit
  openClaimAt := fun _ => .registeredCPS1ProgramAndClinicalResponse
  openProgressBudgetAt := fun _ => 0
  HoldsAt := fun _ _ => PLift OriginalProgramClosure
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := fun obstruction => nomatch obstruction
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev N := network

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := Native.Current
  Anchor := String
  Incidence := String
  Lineage := String
  anchorAt := fun _ => captureKey
  incidenceAt := fun _ => incidenceKey
  lineageAt := fun _ => comparisonLineage
  NativeWriteAt := Native.Write
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := Native.nativeTarget
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

def entry : OpenResponsibilityAt N () := ⟨.originalProgramResponse, PUnit.unit⟩

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
  EventAt := fun current _ => Native.EventAt current
  compile := fun operation => .nativeWrite operation
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := fun _ => openPresentation
  anchorKey := fun _ => captureKey
  incidenceKey := fun _ => incidenceKey
  lineageKey := fun _ => comparisonLineage
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl

def nativeSource : SourceNativeSource N V where
  initial := Native.initial Source.NativeRegistration.registeredNativeInput
  law := eventLaw

def emitted (current : V.Current) :
    nativeSource.toRootSource.actual.OccurrenceAt current :=
  ⟨(), Native.sourceEvent current⟩

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

def writeRowSource : LedgerWriteRowSourceAt nativeSource ExactTransitionAt where
  IncidenceOccurrenceAt := IncidenceOccurrenceAt
  compileEvolution := fun evolution => evolution
  compileExact := fun _ => PUnit.unit

def generatedPatch {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence liveLedger :=
  .complete
    { size := 1
      sourceEntryAt := fun _ => entry
      targetEntryAt := fun _ => entry
      rowAt := fun _ => writeRowSource.generate (.carried rfl HEq.rfl) }
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
    exact .nativeWrite occurrence.2 rfl (emitted (Native.nativeTarget occurrence.2))
      (generatedPatch occurrence).toLedgerWriteEvolution
  compilePatch := by
    intro _current occurrence
    exact ⟨generatedPatch occurrence, rfl⟩

def ledgerSource : SourceNativeLedgerSource N V where
  source := nativeSource
  ledgerCompiler := ledgerCompiler

def restructuringLaw : SourceNativeLedgerRestructuringLaw nativeSource :=
  identityOnlyWorldLedgerRestructuringLaw nativeSource captureKey
    (fun _support _responsibility => by
      change Subsingleton PUnit
      infer_instance)

def restructuringCertification {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) :=
  ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (entry_unique left).trans (entry_unique right).symm)
    (fun left right _ => (entry_unique left).trans (entry_unique right).symm)

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

theorem occurrence_unique {current : V.Current}
    (left right : nativeSource.toRootSource.actual.OccurrenceAt current) :
    left = right := by
  rcases left with ⟨leftSupport, leftEvent⟩
  rcases right with ⟨rightSupport, rightEvent⟩
  cases leftSupport
  cases rightSupport
  rcases leftEvent with ⟨leftBody,leftActual,leftOperation⟩
  rcases rightEvent with ⟨rightBody,rightActual,rightOperation⟩
  cases leftActual
  cases rightActual
  rfl

end
end CPS1Personalized2025.Root
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

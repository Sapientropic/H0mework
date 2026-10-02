import H0mework.Versions.R2.Physics.SpinRuntime.Native
import H0mework.Versions.R2.Physics.Actual.WeakCandidate
import H0mework.Versions.R2.Physics.QuantumState.SourceRestriction

/-! Whole-ledger compilation and authority faces of the original native source. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineFormNativeGaugeAuxiliaryVariation
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite

noncomputable section

structure ExactTransitionAt (current : Current) (targetSupport : MaterialSupport) : Type where
  target_eq : targetSupport = support (next current)

def writeRowSource : LedgerWriteRowSourceAt source (by
    intro current _ targetSupport _ _
    exact ExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := fun {current} _ targetSupport _ _ => ExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨oldSupport, sourceEvent⟩
    change EventAt current oldSupport at sourceEvent
    cases sourceEvent.support_eq
    cases event.target_eq
    cases materialEntry_unique _ sourceEntry
    cases materialEntry_unique _ targetEntry
    exact .transferred (.transfer (materialActionAt (underlying current)))
      rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def occurrenceEntry {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt MaterialN occurrence.1 :=
  (source.law.affectedInventoryPresentation occurrence.2).forward PUnit.unit

def generatedRows {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt writeRowSource occurrence
      (⟨support (next current)⟩ : CompleteLiveLedgerAt MaterialN) where
  size := 1
  sourceEntryAt := fun _ => occurrenceEntry occurrence
  targetEntryAt := fun _ => materialEntry (support (next current))
  rowAt := fun _ => writeRowSource.generate ⟨rfl⟩

def generatedCoverage {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (generatedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change occurrenceEntry occurrence = entry
    exact (source.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (materialEntry_unique _ entry).symm

def generatedPatch {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      (⟨support (next current)⟩ : CompleteLiveLedgerAt MaterialN) :=
  .complete (generatedRows occurrence) (generatedCoverage occurrence)

def generatedEvolution {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt source occurrence :=
  .nativeWrite (materialActionAt (underlying current)) rfl (emitted (next current))
    (generatedPatch occurrence).toLedgerWriteEvolution

def ledgerCompiler : SourceNativeLedgerCompiler source where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := fun {current} _ targetSupport _ _ => ExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := generatedEvolution
  compilePatch := fun occurrence => ⟨generatedPatch occurrence, rfl⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  identityOnlyWorldLedgerRestructuringLaw source positiveSmoothUnifiedSource <| by
    intro targetSupport responsibility
    constructor
    rintro ⟨left⟩ ⟨right⟩
    rfl

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (materialEntry_unique _ left).trans (materialEntry_unique _ right).symm)
    (fun left right _ => (materialEntry_unique _ left).trans (materialEntry_unique _ right).symm)

private def restructuringSource : SourceNativeRestructuringLedgerSource MaterialN V where
  source := source
  compiler := restructuringCompiler

/-- Weak-history and occupied quantum restrictions share the original native law. -/
inductive Projection
  | inherited (coordinate : MaterialProjection)
  | weakActual
  | weakCompilation
  | weakConsumer
  | quantumField
  | quantumCompilation
  | quantumConsumer

private def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .inherited .source => SmoothUnifiedSource
    | .inherited .configuration => StageNineHolonomicConfiguration
    | .inherited .ledger => SourceNativeLedgerEvolutionAt source occurrence
    | .inherited .residual => RootResidualPayload
    | .inherited .inquiryCompilation => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (support current)) PUnit.unit (ULift.up.{1, 0} occurrence)
        .answered StageNineHolonomicConfiguration
    | .inherited .spinPairAction => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (support current)) PUnit.unit (ULift.up.{1, 0} occurrence)
        .answered StageNineHolonomicConfiguration
    | .inherited .inquiryConsumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
        (ULift.up.{1, 0} occurrence) (materialEntry (support current))
        (materialConfiguration (support current))
    | .weakActual => Stage9CU.Weak.Candidate
    | .weakCompilation => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (support current)) PUnit.unit (ULift.up.{1, 0} occurrence)
        .answered Stage9CU.Weak.Candidate
    | .weakConsumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
        (ULift.up.{1, 0} occurrence) (materialEntry (support current))
        Stage9CU.Weak.canonical
    | .quantumField => Stage9DEF.Source.OccupiedField
    | .quantumCompilation => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (support current)) PUnit.unit (ULift.up.{1, 0} occurrence)
        .answered Stage9DEF.Source.OccupiedField
    | .quantumConsumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
        (ULift.up.{1, 0} occurrence) (materialEntry (support current))
        (Stage9DEF.Source.restrict (materialConfiguration (support current)))
  project := fun projection {current} occurrence _ =>
    match projection with
    | .inherited .source => positiveSmoothUnifiedSource
    | .inherited .configuration => materialConfiguration (support current)
    | .inherited .ledger => ledgerCompiler.compile occurrence
    | .inherited .residual => materialResidual (support current)
    | .inherited .inquiryCompilation => .canonical (materialConfiguration (support current))
    | .inherited .spinPairAction => .canonical Material.SpinPair.actual
    | .inherited .inquiryConsumer => .canonical
    | .weakActual => Stage9CU.Weak.canonical
    | .weakCompilation => .canonical Stage9CU.Weak.canonical
    | .weakConsumer => .canonical
    | .quantumField => Stage9DEF.Source.restrict (materialConfiguration (support current))
    | .quantumCompilation =>
        .canonical (Stage9DEF.Source.restrict (materialConfiguration (support current)))
    | .quantumConsumer => .canonical

private def authoritySource : SourceNativeAuthoritySource MaterialN V where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic MaterialN
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure MaterialN V where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure MaterialN V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def initialVisit : SourceNativeTemporalVisitAt livingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite livingRoot.toAuthoritativeRoot.toRoot.initialVisit

def initialGenerated := livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit initialVisit

def initialEntryRow : initialGenerated.GeneratedEntryRowAt sourceEntry :=
  (initialGenerated.canonicalGeneratedEntryRow? sourceEntry).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    initialGenerated.occurrence initialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? initialGenerated.wholeLedgerWriteBack).get (by rfl)

@[simp] theorem firstSuccessor_configuration :
    materialConfiguration (support firstSuccessor.targetCurrent) = Material.SpinPair.actual := rfl

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair

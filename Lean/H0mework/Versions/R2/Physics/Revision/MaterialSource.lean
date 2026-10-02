import H0mework.Versions.R2.Physics.Revision.MaterialWorld
import H0mework.Physics.CartanReduction.P286Descent
import H0mework.Versions.R2.Physics.SpinPair.Actual

/-! The material action is compiled as one whole-ledger native write. The
target configuration and target residual are computed by the fixed physical
operation; neither is supplied to the ledger compiler. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

/-- The spacetime center is fixed by the source occurrence's origin. -/
def materialStateNext : MaterialState → MaterialState :=
  Reduction.p286CartanStateNext 0

def materialNext : MaterialCurrent → MaterialCurrent
  | .ingress => .running materialInitialState
  | .running state => .running (materialStateNext state)

def materialVocabulary : Vocabulary where
  Current := MaterialCurrent
  Anchor := MaterialN.Anchor
  Incidence := MaterialSupport
  Lineage := MaterialN.Lineage
  anchorAt := fun _ => positiveSmoothUnifiedSource
  incidenceAt := materialCurrentSupport
  lineageAt := fun _ => positiveSmoothUnifiedSource
  NativeWriteAt := MaterialActionAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => materialNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev MaterialV := materialVocabulary

structure MaterialEventAt (current : MaterialCurrent)
    (support : MaterialSupport) : Type where
  support_eq : support = materialCurrentSupport current

def materialEventAlgebra : SourceNativeEventAlgebra MaterialN MaterialV where
  EventAt := MaterialEventAt
  compile := fun {current} {_support} _ => .nativeWrite (materialActionAt current)
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.support_eq
    exact materialInventoryPresentation _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := by
    intro current support event
    exact event.support_eq.symm
  lineage_commutes := fun _ => rfl

def materialSource : SourceNativeSource MaterialN MaterialV where
  initial := .ingress
  law := materialEventAlgebra

def materialEmitted (current : MaterialCurrent) :
    materialSource.toRootSource.actual.OccurrenceAt current :=
  ⟨materialCurrentSupport current, ⟨rfl⟩⟩

structure MaterialExactTransitionAt (current : MaterialCurrent)
    (targetSupport : MaterialSupport) : Type where
  target_eq : targetSupport = materialCurrentSupport (materialNext current)

def materialWriteRowSource :
    LedgerWriteRowSourceAt materialSource (by
      intro current _occurrence targetSupport _sourceEntry _targetEntry
      exact MaterialExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact MaterialExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change MaterialEventAt current support at sourceEvent
    cases sourceEvent.support_eq
    cases event.target_eq
    cases materialEntry_unique _ sourceEntry
    cases materialEntry_unique _ targetEntry
    exact .transferred (.transfer (materialActionAt current))
      rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def materialOccurrenceEntry {current : MaterialCurrent}
    (occurrence : materialSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt MaterialN occurrence.1 :=
  materialSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def materialGeneratedRows {current : MaterialCurrent}
    (occurrence : materialSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt materialWriteRowSource occurrence
      (⟨materialCurrentSupport (materialNext current)⟩ : CompleteLiveLedgerAt MaterialN) where
  size := 1
  sourceEntryAt := fun _ => materialOccurrenceEntry occurrence
  targetEntryAt := fun _ => materialEntry (materialCurrentSupport (materialNext current))
  rowAt := fun _ => materialWriteRowSource.generate ⟨rfl⟩

def materialGeneratedCoverage {current : MaterialCurrent}
    (occurrence : materialSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (materialGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change materialOccurrenceEntry occurrence = entry
    exact (materialSource.law.affectedInventoryPresentation occurrence.2
      ).forward_backward entry
  origin_sound := fun entry => (materialEntry_unique _ entry).symm

def materialGeneratedPatch {current : MaterialCurrent}
    (occurrence : materialSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt materialWriteRowSource occurrence
      (⟨materialCurrentSupport (materialNext current)⟩ : CompleteLiveLedgerAt MaterialN) :=
  .complete (materialGeneratedRows occurrence) (materialGeneratedCoverage occurrence)

def materialGeneratedEvolution {current : MaterialCurrent}
    (occurrence : materialSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt materialSource occurrence :=
  .nativeWrite (materialActionAt current) rfl
    (materialEmitted (materialNext current))
    (materialGeneratedPatch occurrence).toLedgerWriteEvolution

def materialLedgerCompiler : SourceNativeLedgerCompiler materialSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact MaterialExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := materialWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := materialGeneratedEvolution
  compilePatch := fun occurrence => ⟨materialGeneratedPatch occurrence, rfl⟩

def materialLedgerSource : SourceNativeLedgerSource MaterialN MaterialV where
  source := materialSource
  ledgerCompiler := materialLedgerCompiler

def materialLedgerRoot : SourceNativeLedgerRootClosure MaterialN MaterialV where
  source := materialLedgerSource
  emitted := materialEmitted
  compiler_commutes := fun _ => rfl

private def materialRestructuringLaw :
    SourceNativeLedgerRestructuringLaw materialSource :=
  identityOnlyWorldLedgerRestructuringLaw materialSource positiveSmoothUnifiedSource <| by
    intro support responsibility
    constructor
    rintro ⟨left⟩ ⟨right⟩
    rfl

private def materialRestructuringCompiler :
    SourceNativeRestructuringLedgerCompiler materialSource where
  ledgerCompiler := materialLedgerCompiler
  restructuringLaw := materialRestructuringLaw
  certifyRestructuring := fun _ =>
    ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (materialEntry_unique _ left).trans
        (materialEntry_unique _ right).symm)
      (fun left right _ => (materialEntry_unique _ left).trans
        (materialEntry_unique _ right).symm)

private def materialRestructuringSource :
    SourceNativeRestructuringLedgerSource MaterialN MaterialV where
  source := materialSource
  compiler := materialRestructuringCompiler

def materialU7 : U7ProducerCalculus MaterialN where
  DemandAt := fun {support} _ => OpenResponsibilityAt MaterialN support
  generateDemand := fun {support} _ => materialEntry support

private def materialInquirySuccessorSource : U7ActualSuccessorSource MaterialN materialU7 where
  EventAt := fun obstruction demand => SourceGeneratedU7DemandAt materialU7 obstruction demand
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _ => materialEntry support

private def materialNeutralTransfer :
    (support : MaterialSupport) → MaterialN.DispositionAt support .transfer
  | .inl current => .inherited (.transfer (rootActionAt current))
  | .inr state => .transfer (materialActionAt (.running state))

def materialInquiryCalculus : U7ObstructionEvolutionCalculus MaterialN materialU7 where
  source := materialInquirySuccessorSource
  compile := fun {support} {obstruction} {_demand} _event =>
    { disposition := .redirected (successor := obstruction)
        ⟨materialNeutralTransfer support, rfl⟩
      demandEntryDisposition :=
        ⟨.transferred (materialNeutralTransfer support) rfl rfl (Nat.le_refl _), rfl⟩ }

theorem materialInquiryCalculus_has_no_strict_answer {support : MaterialN.Support}
    (obstruction : MaterialN.ObstructionAt support) :
    IsEmpty (SourceNativeU7AnswersAt materialInquiryCalculus obstruction) :=
  ⟨fun answer => Nat.lt_irrefl _ answer.down.down⟩

inductive MaterialProjection
  | source
  | configuration
  | ledger
  | residual
  | inquiryCompilation
  | inquiryConsumer
  | spinPairAction

private def materialProjectionLaw :
    SourceNativeProjectionLaw materialRestructuringSource.toLedgerSource where
  Projection := MaterialProjection
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _active =>
    match projection with
    | .source => SmoothUnifiedSource
    | .configuration => StageNineHolonomicConfiguration
    | .ledger => SourceNativeLedgerEvolutionAt materialSource occurrence
    | .residual => RootResidualPayload
    | .inquiryCompilation => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (materialCurrentSupport current)) PUnit.unit
        (ULift.up.{1, 0} occurrence) .answered StageNineHolonomicConfiguration
    | .spinPairAction => SourceNativeInquiryCompilationTokenAt
        (U7 := materialU7) (calculus := materialInquiryCalculus)
        (oldTheory := TheoryState.rootSemantic MaterialN)
        (materialEntry (materialCurrentSupport current)) PUnit.unit
        (ULift.up.{1, 0} occurrence) .answered StageNineHolonomicConfiguration
    | .inquiryConsumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit
        (ULift.up.{1, 0} occurrence) (materialEntry (materialCurrentSupport current))
        (materialConfiguration (materialCurrentSupport current))
  project := fun projection {current} occurrence _active =>
    match projection with
    | .source => positiveSmoothUnifiedSource
    | .configuration => materialConfiguration (materialCurrentSupport current)
    | .ledger => materialLedgerCompiler.compile occurrence
    | .residual => materialResidual (materialCurrentSupport current)
    | .inquiryCompilation => .canonical (materialConfiguration (materialCurrentSupport current))
    | .spinPairAction => .canonical Material.SpinPair.actual
    | .inquiryConsumer => .canonical

private def materialAuthoritySource : SourceNativeAuthoritySource MaterialN MaterialV where
  restructuringSource := materialRestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal materialRestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic MaterialN
  projectionLaw := materialProjectionLaw

def materialAuthoritativeRoot : SourceNativeAuthoritativeRootClosure MaterialN MaterialV where
  source := materialAuthoritySource
  emitted := materialEmitted
  compiler_commutes := fun _ => rfl

def materialLivingRoot : SourceNativeLivingRootClosure MaterialN MaterialV :=
  materialAuthoritativeRoot.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

def materialInitialVisit :
    SourceNativeTemporalVisitAt materialLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite materialLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def materialInitialGenerated :=
  materialLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit materialInitialVisit

def materialInitialEntry := materialEntry (materialCurrentSupport .ingress)

def materialInitialEntryRow :
    materialInitialGenerated.GeneratedEntryRowAt materialInitialEntry :=
  (materialInitialGenerated.canonicalGeneratedEntryRow? materialInitialEntry).get (by rfl)

def materialFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    materialInitialGenerated.occurrence materialInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    materialInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision

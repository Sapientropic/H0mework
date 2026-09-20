import H0mework.Realization.Completion.HistorySettlement
import H0mework.Realization.Completion.HistoryResidual
import H0mework.Foundation.Authority.Representation

/-!
# Source-native cofinal-history settlement face

This adapter admits a cofinal relation history as one installed projection
of an already complete source.  The source contributes only occurrence-
indexed seed and continuation occurrences.  `RootGeneratedCofinalHistoryAt`
then constructs the presented carrier and its total compact/perfect or
persistent-residual disposition.  Whole-ledger write-back and the next
current are read from the same temporal compiler image; neither is a field
of the history material or settlement token.

The adapter intentionally stops at the formal presented carrier.  A faithful
map to a separate actual carrier remains the independent
`RootGeneratedCofinalFaithfulRealizationAt` face, where its kernel/cokernel
residuals must be settled before any equivalence is claimed.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistorySettlementFace

open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistoryResidualCoordinate

noncomputable section

universe u

/-! ## Source-installed material -/

/-- Source-native material needed to expose one cofinal relation history.

The constructor is private so a source can enter only through `create`; no
settlement branch, finite envelope, determinant, or next target can be
smuggled into the material face. -/
structure SourceNativeCofinalHistoryMaterialLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  private mk ::
  Generator : Type u
  /-- Source-owned outer occurrence exposure.  The root payload is the exact
  emitted source occurrence; the exposure may retain additional branches. -/
  rootExposureAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current →
      RootedAccountedUnfolding
        (source.source.toRootSource.actual.OccurrenceAt current)
  rootExposure_root : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      (rootExposureAt occurrence).root = occurrence
  seedAt : {current : V.Current} ->
    source.source.toRootSource.actual.OccurrenceAt current ->
      RootedAccountedUnfolding (PresentedRelationEventAt Generator)
  continuationAt : {current : V.Current} ->
    source.source.toRootSource.actual.OccurrenceAt current ->
      RootedAccountedUnfolding
        (PresentedRelationEventAt Generator ->
          RootedAccountedUnfolding (PresentedRelationEventAt Generator))

namespace SourceNativeCofinalHistoryMaterialLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}
}
variable {source : SourceNativeLedgerSource N V}

/-- Public source-facing constructor. -/
def create
    (Generator : Type u)
    (rootExposureAt : {current : V.Current} ->
      source.source.toRootSource.actual.OccurrenceAt current ->
        RootedAccountedUnfolding
          (source.source.toRootSource.actual.OccurrenceAt current))
    (rootExposure_root : {current : V.Current} ->
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current) ->
        (rootExposureAt occurrence).root = occurrence)
    (seedAt : {current : V.Current} ->
      source.source.toRootSource.actual.OccurrenceAt current ->
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))
    (continuationAt : {current : V.Current} ->
      source.source.toRootSource.actual.OccurrenceAt current ->
        RootedAccountedUnfolding
          (PresentedRelationEventAt Generator ->
            RootedAccountedUnfolding (PresentedRelationEventAt Generator))) :
    SourceNativeCofinalHistoryMaterialLaw source :=
  ⟨Generator, rootExposureAt, rootExposure_root, seedAt, continuationAt⟩

/-- The generic-history root is the exact emitted source occurrence. -/
def rootOccurrenceAt
    (law : SourceNativeCofinalHistoryMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    RootedAccountedUnfolding
      (source.source.toRootSource.actual.OccurrenceAt current) :=
  law.rootExposureAt occurrence

theorem rootOccurrenceAt_root
    (law : SourceNativeCofinalHistoryMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    (law.rootOccurrenceAt occurrence).root = occurrence :=
  law.rootExposure_root occurrence

/-- Construct the complete presented history from the source occurrence. -/
def historyAt
    (law : SourceNativeCofinalHistoryMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedCofinalHistoryAt (law.rootOccurrenceAt occurrence)
      (law.seedAt occurrence) (law.continuationAt occurrence) :=
  RootGeneratedCofinalHistoryAt.generate

/-- Install the history chart as a source projection.  The payload is the
history itself; all compactness/perfectness/determinant facts are generated
later by the neutral history kernel. -/
def toProjectionLaw
    (law : SourceNativeCofinalHistoryMaterialLaw source) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} occurrence _active =>
    ULift.{u, 0} (RootGeneratedCofinalHistoryAt
      (law.rootOccurrenceAt occurrence)
      (law.seedAt occurrence) (law.continuationAt occurrence))
  project := fun _projection {_current} occurrence _active =>
    ULift.up (law.historyAt occurrence)

@[simp] theorem outcomeAt_eq
    (law : SourceNativeCofinalHistoryMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    law.toProjectionLaw.outcomeAt PUnit.unit occurrence =
      .inl ⟨PUnit.unit, ULift.up (law.historyAt occurrence)⟩ :=
  rfl

end SourceNativeCofinalHistoryMaterialLaw

/-! ## Root admission and one exact temporal step -/

/-- Recognition is the same source-projection installation boundary used by
other root faces (arithmetic, action, and U8). -/
structure SourceNativeCofinalHistoryRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  materialLaw : SourceNativeCofinalHistoryMaterialLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

/-- Zero-field authority token at one exact root temporal visit. -/
structure RootGeneratedCofinalHistorySettlementStepAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeCofinalHistoryRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type where
  private mk ::

namespace RootGeneratedCofinalHistorySettlementStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate : RootGeneratedCofinalHistorySettlementStepAt recognition visit :=
  ⟨⟩

def generated
    (_step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot visit :=
  root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit

def sourceOccurrence
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :=
  step.generated.occurrence

def history
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :=
  recognition.materialLaw.historyAt step.sourceOccurrence

abbrev CompletionCarrier
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :=
  step.history.CompletionCarrier

/-- Total generic compact/perfect or persistent-residual disposition. -/
def settlement
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    step.history.SettlementOutcome :=
  step.history.settle

/-! A residual coordinate is generated only after the total settlement chooses
the persistent branch.  The sum below keeps the positive determinant face
and the negative coordinate in one source-indexed result. -/
abbrev TotalDisposition
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :=
  Sum
    (Σ trace : GeneratedHistoricalCompactnessAt step.history,
      GeneratedCompactPerfectReadoutAt step.history trace)
    (GeneratedPresentedResidualCoordinateAt step.history)

noncomputable def totalDispositionOf
    {Root : Type u} {Generator : Type u}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {seedOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator)}
    {continuationOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator ->
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (outcome : history.SettlementOutcome) :
    Sum
      (Σ trace : GeneratedHistoricalCompactnessAt history,
        GeneratedCompactPerfectReadoutAt history trace)
      (GeneratedPresentedResidualCoordinateAt history) :=
  match outcome with
  | .inl compact => Sum.inl compact
  | .inr obstruction => Sum.inr (persistentCoordinate obstruction)

noncomputable def totalDisposition
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    step.TotalDisposition :=
  totalDispositionOf step.history step.settlement

def residualCoordinate
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    Option (GeneratedPresentedResidualCoordinateAt step.history) :=
  match step.totalDisposition with
  | .inl _ => none
  | .inr coordinate => some coordinate

theorem totalDisposition_positive_or_residual
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    (∃ trace : GeneratedHistoricalCompactnessAt step.history,
      ∃ readout : GeneratedCompactPerfectReadoutAt step.history trace,
        step.totalDisposition = .inl ⟨trace, readout⟩) ∨
    (∃ coordinate : GeneratedPresentedResidualCoordinateAt step.history,
      step.totalDisposition = .inr coordinate ∧
        coordinate.coordinate ≠ 0 ∧
        coordinate.representative ∉
          LinearMap.range
            (step.history.stagePresentedToCompletion coordinate.stage)) := by
  cases h : step.history.settle with
  | inl positive =>
      rcases positive with ⟨trace, readout⟩
      refine Or.inl ⟨trace, readout, ?_⟩
      change totalDispositionOf step.history step.history.settle = _
      rw [h]
      rfl
  | inr obstruction =>
      let coordinate := persistentCoordinate obstruction
      refine Or.inr ⟨coordinate, ?_,
        coordinate.coordinate_ne_zero,
        coordinate.representative_outside_source_range⟩
      change totalDispositionOf step.history step.history.settle = _
      rw [h]
      rfl

/-- Whole-ledger evolution from the same source temporal compiler image. -/
def wholeLedgerWriteBack
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :=
  step.generated.wholeLedgerWriteBack

/-- The history face cannot choose a successor. -/
def nextCurrent
    (_step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

@[simp] theorem sourceOccurrence_eq_generated
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    step.sourceOccurrence = step.generated.occurrence :=
  rfl

theorem history_root_exposure_eq
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    step.history.root =
      recognition.materialLaw.rootOccurrenceAt step.sourceOccurrence :=
  rfl

@[simp] theorem history_root_payload_eq_sourceOccurrence
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    step.history.root.root = step.sourceOccurrence := by
  change (recognition.materialLaw.rootOccurrenceAt step.sourceOccurrence).root =
    step.sourceOccurrence
  exact recognition.materialLaw.rootOccurrenceAt_root step.sourceOccurrence

theorem wholeLedgerWriteBack_eq_root
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  HEq.rfl

@[simp] theorem nextCurrent_eq_root
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  rfl

/-- The source projection and the history chart are the same dependent face. -/
theorem installedHistory_factorizes
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit)
        step.sourceOccurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.sourceOccurrence) :=
  recognition.installation.outcome_heq step.sourceOccurrence PUnit.unit

theorem settlement_exhaustive
    (step : RootGeneratedCofinalHistorySettlementStepAt recognition visit) :
    (∃ stage, step.history.CompactAt stage) ∨
      (∀ stage, ¬ step.history.CompactAt stage) :=
  step.history.settlement_exhaustive

end RootGeneratedCofinalHistorySettlementStepAt

namespace SourceNativeCofinalHistoryRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def generateStepAt
    (recognition : SourceNativeCofinalHistoryRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootGeneratedCofinalHistorySettlementStepAt recognition visit :=
  RootGeneratedCofinalHistorySettlementStepAt.generate

end SourceNativeCofinalHistoryRecognitionAt

end
end CofinalHistorySettlementFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

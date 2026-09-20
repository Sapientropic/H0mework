import H0mework.Realization.Completion.PresentedComplex
import H0mework.Foundation.Relations.CochainPresentation
import H0mework.Realization.Completion.HistoryInstallation

/-!
# Source-installed cofinal cochain/complex settlement face

The neutral cofinal-presented-complex kernel already generates relation
closures, differential naturality, completion laws, and the derived residual
disposition.  This face installs that calculus on one exact source
occurrence.  The same occurrence supplies the actual integral cochain complex
and its degreewise cofinal histories; the source projection therefore cannot
pair a history with an unrelated complex after the fact.

The companion cochain relation face exposes the differential square before
any global settlement.  Its `d² = 0` and generator-relation factorization are
readouts of the actual complex, not caller-supplied chain data.  The cofinal
settlement remains a total five-way disposition: closure/law/relation or
derived residual obstruction, or a settled presentation.  No perfectness,
quasi-isomorphism, determinant, inverse, or residual-zero receipt is an
entry premise.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPresentedComplexSettlementFace

open CofinalHistorySettlement
open CofinalHistorySettlementFace
open CofinalPresentedComplex
open CofinalPresentedComplex.RootGeneratedCofinalPresentedComplexDiagramAt
open CochainRelationPresentation
open FiniteAdditiveRelationPresentation
open DerivedAdicCofiber
open SourceNativeProjectionLaw

noncomputable section

universe u

/-! ## Source-owned material -/

/-- One source occurrence carries the actual integral cochain complex and the
degreewise cofinal event histories used to present it.  The histories may be
incomplete; the generic settlement then returns the exact obstruction rather
than silently installing a finite model. -/
structure SourceNativeCofinalPresentedComplexMaterialLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  private mk ::
  rootExposureAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current →
      RootedAccountedUnfolding
        (source.source.toRootSource.actual.OccurrenceAt current)
  rootExposure_root : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      (rootExposureAt occurrence).root = occurrence
  complexAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current →
      RootedAccountedUnfolding (IntegralCochainComplex ℤ)
  seedAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    ∀ degree, RootedAccountedUnfolding
      (PresentedRelationEventAt ((complexAt occurrence).root.X degree))
  continuationAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    ∀ degree, RootedAccountedUnfolding
      (PresentedRelationEventAt ((complexAt occurrence).root.X degree) →
        RootedAccountedUnfolding
          (PresentedRelationEventAt ((complexAt occurrence).root.X degree)))

namespace SourceNativeCofinalPresentedComplexMaterialLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {source : SourceNativeLedgerSource N V}

def create
    (rootExposureAt : {current : V.Current} →
      source.source.toRootSource.actual.OccurrenceAt current →
        RootedAccountedUnfolding
          (source.source.toRootSource.actual.OccurrenceAt current))
    (rootExposure_root : {current : V.Current} →
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
        (rootExposureAt occurrence).root = occurrence)
    (complexAt : {current : V.Current} →
      source.source.toRootSource.actual.OccurrenceAt current →
        RootedAccountedUnfolding (IntegralCochainComplex ℤ))
    (seedAt : {current : V.Current} →
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      ∀ degree, RootedAccountedUnfolding
        (PresentedRelationEventAt ((complexAt occurrence).root.X degree)))
    (continuationAt : {current : V.Current} →
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      ∀ degree, RootedAccountedUnfolding
        (PresentedRelationEventAt ((complexAt occurrence).root.X degree) →
          RootedAccountedUnfolding
            (PresentedRelationEventAt ((complexAt occurrence).root.X degree)))) :
    SourceNativeCofinalPresentedComplexMaterialLaw source :=
  ⟨rootExposureAt, rootExposure_root, complexAt, seedAt, continuationAt⟩

def rootOccurrenceAt
    (law : SourceNativeCofinalPresentedComplexMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :=
  law.rootExposureAt occurrence

theorem rootOccurrenceAt_root
    (law : SourceNativeCofinalPresentedComplexMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    (law.rootOccurrenceAt occurrence).root = occurrence :=
  law.rootExposure_root occurrence

def diagramAt
    (law : SourceNativeCofinalPresentedComplexMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      (law.rootOccurrenceAt occurrence) (law.complexAt occurrence) :=
  RootGeneratedCofinalPresentedComplexDiagramAt.generate
    (law.seedAt occurrence) (law.continuationAt occurrence)

/-- Install the complete cochain chart as one source projection. -/
def toProjectionLaw
    (law : SourceNativeCofinalPresentedComplexMaterialLaw source) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} occurrence _active =>
    RootGeneratedIntegralCofinalPresentedComplexDiagramAt
      (law.rootOccurrenceAt occurrence) (law.complexAt occurrence)
  project := fun _projection {_current} occurrence _active =>
    law.diagramAt occurrence

@[simp] theorem outcomeAt_eq
    (law : SourceNativeCofinalPresentedComplexMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    law.toProjectionLaw.outcomeAt PUnit.unit occurrence =
      .inl ⟨PUnit.unit, law.diagramAt occurrence⟩ :=
  rfl

end SourceNativeCofinalPresentedComplexMaterialLaw

/-! ## Root admission and one exact temporal step -/

structure SourceNativeCofinalPresentedComplexRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  private mk ::
  materialLaw : SourceNativeCofinalPresentedComplexMaterialLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeCofinalPresentedComplexRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def create
    (materialLaw : SourceNativeCofinalPresentedComplexMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      materialLaw.toProjectionLaw
      root.toAuthoritativeRoot.source.projectionLaw) :
    SourceNativeCofinalPresentedComplexRecognitionAt root :=
  ⟨materialLaw, installation⟩

end SourceNativeCofinalPresentedComplexRecognitionAt

structure RootGeneratedCofinalPresentedComplexSettlementStepAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeCofinalPresentedComplexRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 2) where
  private mk ::

namespace RootGeneratedCofinalPresentedComplexSettlementStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalPresentedComplexRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate : RootGeneratedCofinalPresentedComplexSettlementStepAt
    recognition visit :=
  ⟨⟩

def generated
    (_step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot visit :=
  root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit

def sourceOccurrence
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :=
  step.generated.occurrence

def diagram
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :=
  recognition.materialLaw.diagramAt step.sourceOccurrence

def cochainFace
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    RootGeneratedCochainRelationPresentationAt
      step.diagram.root
      (recognition.materialLaw.complexAt step.sourceOccurrence) :=
  RootGeneratedCochainRelationPresentationAt.generate

abbrev SettlementOutcome
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :=
  RootGeneratedCofinalPresentedComplexDiagramAt.SettlementOutcome
    step.diagram

def settlement
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    step.SettlementOutcome :=
  step.diagram.settle

def wholeLedgerWriteBack
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :=
  step.generated.wholeLedgerWriteBack

def nextCurrent
    (_step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

@[simp] theorem sourceOccurrence_eq_generated
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    step.sourceOccurrence = step.generated.occurrence :=
  rfl

theorem diagram_root_eq_exposure
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    step.diagram.root =
      recognition.materialLaw.rootOccurrenceAt step.sourceOccurrence :=
  rfl

@[simp] theorem diagram_root_payload_eq_sourceOccurrence
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    step.diagram.root.root = step.sourceOccurrence := by
  change (recognition.materialLaw.rootOccurrenceAt step.sourceOccurrence).root =
    step.sourceOccurrence
  exact recognition.materialLaw.rootOccurrenceAt_root step.sourceOccurrence

theorem diagram_actualComplex_eq
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    step.diagram.actualComplex =
      (recognition.materialLaw.complexAt step.sourceOccurrence).root :=
  rfl

/-! ## Cochain naturality and total settlement -/

theorem differential_relation_naturality
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit)
    (source target : ℤ) :
    (step.cochainFace.differentialGeneratorMap source target).comp
        (additionRelationMap
          (step.cochainFace.complex.X source)) =
      (additionRelationMap
          (step.cochainFace.complex.X target)).comp
        (step.cochainFace.differentialRelationMap source target) :=
  step.cochainFace.differential_relation_naturality source target

theorem differential_presentedMap_comp_zero
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit)
    (first middle last : ℤ)
    (value : (step.cochainFace.termPresentation first).cokernel) :
    finiteAdditiveRelationPresentation_cokernelEquiv _
        (step.cochainFace.termPresentation last)
        (step.cochainFace.differentialPresentedMap middle last
          (step.cochainFace.differentialPresentedMap first middle value)) = 0 :=
  step.cochainFace.differential_presentedMap_comp_zero first middle last value

theorem differentialGeneratorMap_comp_factorizes
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit)
    (first middle last : ℤ) :
    (step.cochainFace.differentialGeneratorMap middle last).comp
        (step.cochainFace.differentialGeneratorMap first middle) =
      (additionRelationMap (step.cochainFace.complex.X last)).comp
        (step.cochainFace.differentialSquareRelationLift first last) :=
  step.cochainFace.differentialGeneratorMap_comp_factorizes_through_relation
    first middle last

theorem settlement_is_total
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    Nonempty step.SettlementOutcome :=
  ⟨step.settlement⟩

theorem wholeLedgerWriteBack_eq_root
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  HEq.rfl

@[simp] theorem nextCurrent_eq_root
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  rfl

theorem installedComplex_factorizes
    (step : RootGeneratedCofinalPresentedComplexSettlementStepAt
      recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit)
        step.sourceOccurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.sourceOccurrence) :=
  recognition.installation.outcome_heq step.sourceOccurrence PUnit.unit

end RootGeneratedCofinalPresentedComplexSettlementStepAt

namespace SourceNativeCofinalPresentedComplexRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def generateStepAt
    (recognition : SourceNativeCofinalPresentedComplexRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootGeneratedCofinalPresentedComplexSettlementStepAt recognition visit :=
  RootGeneratedCofinalPresentedComplexSettlementStepAt.generate

end SourceNativeCofinalPresentedComplexRecognitionAt

end
end CofinalPresentedComplexSettlementFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

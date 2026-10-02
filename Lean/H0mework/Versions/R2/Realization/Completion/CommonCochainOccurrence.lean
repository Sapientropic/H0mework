import H0mework.Versions.R2.Realization.Completion.HistoryDeterminant
import H0mework.Versions.R2.Realization.Completion.ComplexInstallation
import H0mework.Realization.Completion.FaithfulResidual
import H0mework.Foundation.Relations.CochainPresentation
import H0mework.Realization.Arithmetic.DerivedAdicCofiber

/-!
# One common occurrence for history, faithful, and cochain faces

The generic foundation has three useful sibling views of an actual source:
the cofinal history, its faithful map to an actual carrier, and the actual
cochain differential.  This face binds those views before any comparison is
attempted.  The history supplies determinant disposition, the faithful map
supplies relation/kernel/coverage residuals, and the cochain presentation
supplies differential naturality and `d² = 0`.

No equality between the sibling readouts is assumed.  A future source-owned
map may consume this common occurrence and settle a genuine residual; until
then the three generated dispositions remain independently visible but share
the same root, source occurrence, whole-ledger write-back, and next current.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainCommonOccurrence

open CofinalHistorySettlement
open CofinalHistorySettlementFace
open CofinalHistoryDeterminantDisposition
open CofinalPresentedComplexSettlementFace
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CochainRelationPresentation
open DerivedAdicCofiber
open FiniteAdditiveRelationPresentation
open SourceNativeProjectionLaw

noncomputable section

universe u

/-! ## Source-owned sibling material -/

structure SourceNativeCofinalHistoryCochainMaterialLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  private mk ::
  historyLaw : SourceNativeCofinalHistoryMaterialLaw source
  complexAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current →
      RootedAccountedUnfolding (IntegralCochainComplex ℤ)
  evaluatorAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    RootedAccountedUnfolding
      (historyLaw.Generator → (complexAt occurrence).root.X 0)

namespace SourceNativeCofinalHistoryCochainMaterialLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {source : SourceNativeLedgerSource N V}

def create
    (historyLaw : SourceNativeCofinalHistoryMaterialLaw source)
    (complexAt : {current : V.Current} →
      source.source.toRootSource.actual.OccurrenceAt current →
        RootedAccountedUnfolding (IntegralCochainComplex ℤ))
    (evaluatorAt : {current : V.Current} →
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      RootedAccountedUnfolding
        (historyLaw.Generator → (complexAt occurrence).root.X 0)) :
    SourceNativeCofinalHistoryCochainMaterialLaw source :=
  ⟨historyLaw, complexAt, evaluatorAt⟩

def historyAt
    (law : SourceNativeCofinalHistoryCochainMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :=
  law.historyLaw.historyAt occurrence

def evaluatorOccurrenceAt
    (law : SourceNativeCofinalHistoryCochainMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :=
  law.evaluatorAt occurrence

def faithfulAt
    (law : SourceNativeCofinalHistoryCochainMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedCofinalFaithfulRealizationAt
      (law.historyAt occurrence) (law.evaluatorOccurrenceAt occurrence) :=
  RootGeneratedCofinalFaithfulRealizationAt.generate

def cochainAt
    (law : SourceNativeCofinalHistoryCochainMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedCochainRelationPresentationAt
      (law.historyAt occurrence).root (law.complexAt occurrence) :=
  RootGeneratedCochainRelationPresentationAt.generate

/-- The history source already installs its complete seed and continuation
as a dependent projection. Reuse that projection rather than replacing it by
an occurrence seal: a seal alone cannot distinguish two actual histories at
the same emitted occurrence. The larger cochain/evaluator objects remain
conditional material until their own source projection is installed. -/
def toProjectionLaw
    (law : SourceNativeCofinalHistoryCochainMaterialLaw source) :
    SourceNativeProjectionLaw source :=
  law.historyLaw.toProjectionLaw

@[simp] theorem outcomeAt_eq
    (law : SourceNativeCofinalHistoryCochainMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    law.toProjectionLaw.outcomeAt PUnit.unit occurrence =
      .inl ⟨PUnit.unit, law.historyLaw.rawAt occurrence⟩ :=
  rfl

end SourceNativeCofinalHistoryCochainMaterialLaw

/-! ## Root admission and exact common step -/

structure SourceNativeCofinalHistoryCochainRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  private mk ::
  materialLaw : SourceNativeCofinalHistoryCochainMaterialLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeCofinalHistoryCochainRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def create
    (materialLaw : SourceNativeCofinalHistoryCochainMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      materialLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw) :
    SourceNativeCofinalHistoryCochainRecognitionAt root :=
  ⟨materialLaw, installation⟩

end SourceNativeCofinalHistoryCochainRecognitionAt

structure RootGeneratedCofinalHistoryCochainCommonStepAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeCofinalHistoryCochainRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 2) where
  private mk ::

namespace RootGeneratedCofinalHistoryCochainCommonStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryCochainRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit :=
  ⟨⟩

def generated
    (_step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot visit :=
  root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit

def sourceOccurrence
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :=
  step.generated.occurrence

def history
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :=
  recognition.materialLaw.historyAt step.sourceOccurrence

def evaluatorOccurrence
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :=
  recognition.materialLaw.evaluatorOccurrenceAt step.sourceOccurrence

def faithful
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    RootGeneratedCofinalFaithfulRealizationAt step.history
      step.evaluatorOccurrence :=
  recognition.materialLaw.faithfulAt step.sourceOccurrence

def cochainFace
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    RootGeneratedCochainRelationPresentationAt
      step.history.root
      (recognition.materialLaw.complexAt step.sourceOccurrence) :=
  recognition.materialLaw.cochainAt step.sourceOccurrence

def historyDeterminantDisposition
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    CofinalHistoryDeterminantDisposition.DeterminantDispositionOutcome
      step.history :=
  CofinalHistoryDeterminantDisposition.settleWithDeterminant step.history

def faithfulResidualDisposition
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    ResidualDispositionOutcome step.faithful :=
  step.faithful.settleWithResidual

/-! These are sibling outputs, not a comparison theorem. -/
structure CommonDisposition
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    Type (u + 2) where
  history :
    CofinalHistoryDeterminantDisposition.DeterminantDispositionOutcome
      step.history
  faithful : ResidualDispositionOutcome step.faithful
  cochain : RootGeneratedCochainRelationPresentationAt
    step.history.root
    (recognition.materialLaw.complexAt step.sourceOccurrence)

def disposition
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    CommonDisposition step :=
  ⟨step.historyDeterminantDisposition,
    step.faithfulResidualDisposition, step.cochainFace⟩

theorem disposition_is_total
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    Nonempty (CommonDisposition step) :=
  ⟨step.disposition⟩

theorem history_root_eq_cochain_root
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    step.history.root = step.cochainFace.root :=
  rfl

theorem faithful_root_eq_history_root
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    step.faithful.root = step.history.root :=
  rfl

theorem cochain_d_squared
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit)
    (first middle last : ℤ)
    (value : (step.cochainFace.termPresentation first).cokernel) :
    finiteAdditiveRelationPresentation_cokernelEquiv _
        (step.cochainFace.termPresentation last)
        (step.cochainFace.differentialPresentedMap middle last
          (step.cochainFace.differentialPresentedMap first middle value)) = 0 :=
  step.cochainFace.differential_presentedMap_comp_zero first middle last value

def wholeLedgerWriteBack
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :=
  step.generated.wholeLedgerWriteBack

def nextCurrent
    (_step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

theorem wholeLedgerWriteBack_eq_root
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  HEq.rfl

@[simp] theorem nextCurrent_eq_root
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  rfl

theorem installedCochain_factorizes
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit) step.sourceOccurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.sourceOccurrence) :=
  recognition.installation.outcome_heq step.sourceOccurrence PUnit.unit

/-- The installed parent coordinate exposes the seed and continuation that
the cofinal engine actually advances; the same visit supplies ledger and
next. This does not yet certify the separately supplied cochain evaluator. -/
theorem sourceHistoryAction_root_ledger_next
    (step : RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit) :
    step.history.seed =
        (recognition.materialLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).seed ∧
      step.history.actualContinuation =
        (recognition.materialLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).continuation.root ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.installation.embed PUnit.unit) step.sourceOccurrence)
        (recognition.materialLaw.toProjectionLaw.outcomeAt
          PUnit.unit step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨rfl, rfl, step.installedCochain_factorizes,
    step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩

end RootGeneratedCofinalHistoryCochainCommonStepAt

namespace SourceNativeCofinalHistoryCochainRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def generateStepAt
    (recognition : SourceNativeCofinalHistoryCochainRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootGeneratedCofinalHistoryCochainCommonStepAt recognition visit :=
  RootGeneratedCofinalHistoryCochainCommonStepAt.generate

end SourceNativeCofinalHistoryCochainRecognitionAt

end
end CofinalHistoryCochainCommonOccurrence
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

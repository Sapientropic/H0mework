import H0mework.Realization.Perfectification.DualDisposition
import H0mework.Realization.Completion.CommonCochainOccurrence

/-!
# Source-installed cofinal duality transport

This adapter binds a source-owned integral pairing to the *same* complete
cofinal history occurrence that already supplies the relation, faithful, and
cochain sibling faces.  The pairing is not a second source and no
nondegeneracy, inverse, finite-dimensionality, perfectness, or determinant
frame is accepted at the admission boundary.

The generic dual-evaluation compiler then produces a two-sided dualizable
evidence branch or an explicit kernel/cokernel residual.  Root, occurrence,
whole-ledger write-back, and generated next are inherited from the common
face; no comparator between domain shadows is introduced.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainDuality

open CofinalHistorySettlement
open CofinalHistorySettlementFace
open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainCommonOccurrence.RootGeneratedCofinalHistoryCochainCommonStepAt
open SourceGeneratedDualEvaluation

noncomputable section

universe u

/-! ## Source-owned pairing material -/

structure SourceNativeCofinalHistoryCochainDualityMaterialLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  private mk ::
  commonLaw : SourceNativeCofinalHistoryCochainMaterialLaw source
  pairingAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      RootedAccountedUnfolding
        ((commonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ]
          (commonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ] ℤ)

namespace SourceNativeCofinalHistoryCochainDualityMaterialLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {source : SourceNativeLedgerSource N V}

def create
    (commonLaw : SourceNativeCofinalHistoryCochainMaterialLaw source)
    (pairingAt : {current : V.Current} →
      (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
        RootedAccountedUnfolding
          ((commonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ]
            (commonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ] ℤ)) :
    SourceNativeCofinalHistoryCochainDualityMaterialLaw source :=
  ⟨commonLaw, pairingAt⟩

def toProjectionLaw
    (law : SourceNativeCofinalHistoryCochainDualityMaterialLaw source) :
    SourceNativeProjectionLaw source :=
  law.commonLaw.toProjectionLaw

end SourceNativeCofinalHistoryCochainDualityMaterialLaw

/-! ## Root admission -/

structure SourceNativeCofinalHistoryCochainDualityRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  private mk ::
  materialLaw : SourceNativeCofinalHistoryCochainDualityMaterialLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeCofinalHistoryCochainDualityRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def create
    (materialLaw : SourceNativeCofinalHistoryCochainDualityMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      materialLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw) :
    SourceNativeCofinalHistoryCochainDualityRecognitionAt root :=
  ⟨materialLaw, installation⟩

def commonRecognition
    (recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root) :
    SourceNativeCofinalHistoryCochainRecognitionAt root :=
  SourceNativeCofinalHistoryCochainRecognitionAt.create
    recognition.materialLaw.commonLaw recognition.installation

end SourceNativeCofinalHistoryCochainDualityRecognitionAt

/-! ## Exact temporal duality step -/

structure RootGeneratedCofinalHistoryCochainDualityStepAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 2) where
  private mk ::

namespace RootGeneratedCofinalHistoryCochainDualityStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit :=
  ⟨⟩

def commonStep
    (_step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    RootGeneratedCofinalHistoryCochainCommonStepAt
      recognition.commonRecognition visit :=
  recognition.commonRecognition.generateStepAt visit

def sourceOccurrence
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  step.commonStep.sourceOccurrence

abbrev Carrier
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) : Type u :=
  step.commonStep.history.CompletionCarrier

def pairingFace
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    RootGeneratedDualEvaluationPairingAt
      step.commonStep.history.root
      (fun value : Carrier step => RootedAccountedUnfolding.zero value)
      (fun value : Carrier step => RootedAccountedUnfolding.zero value)
      (recognition.materialLaw.pairingAt step.sourceOccurrence) :=
  RootGeneratedDualEvaluationPairingAt.generate
    (left_exact := fun _ => rfl) (right_exact := fun _ => rfl)

def dualityDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    DualityDispositionOutcome step.pairingFace :=
  settleDuality step.pairingFace

structure CommonDualityDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Type (u + 2) where
  common : CommonDisposition step.commonStep
  duality : DualityDispositionOutcome step.pairingFace

def disposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    CommonDualityDisposition step :=
  ⟨step.commonStep.disposition, step.dualityDisposition⟩

theorem disposition_is_total
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Nonempty (CommonDualityDisposition step) :=
  ⟨step.disposition⟩

def wholeLedgerWriteBack
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  step.commonStep.wholeLedgerWriteBack

def nextCurrent
    (_step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

theorem wholeLedgerWriteBack_eq_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  step.commonStep.wholeLedgerWriteBack_eq_root

@[simp] theorem nextCurrent_eq_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  rfl

theorem installedDuality_factorizes
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit) step.sourceOccurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.sourceOccurrence) :=
  recognition.installation.outcome_heq step.sourceOccurrence PUnit.unit

theorem common_root_eq_pairing_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    step.commonStep.history.root = step.pairingFace.root :=
  rfl

end RootGeneratedCofinalHistoryCochainDualityStepAt

namespace SourceNativeCofinalHistoryCochainDualityRecognitionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

def generateStepAt
    (recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit :=
  RootGeneratedCofinalHistoryCochainDualityStepAt.generate

end SourceNativeCofinalHistoryCochainDualityRecognitionAt

end
end CofinalHistoryCochainDuality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

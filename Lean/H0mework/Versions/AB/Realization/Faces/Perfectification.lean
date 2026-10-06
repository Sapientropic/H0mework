import H0mework.Realization.Perfectification.SourceCoimage
import H0mework.Realization.Perfectification.IntegralPair
import H0mework.Realization.Perfectification.ExactObservation
import H0mework.Versions.R2.Realization.Faces.DualityTransport
import H0mework.Versions.AB.Realization.Perfectification.AmbientDisposition
import H0mework.Realization.Perfectification.AmbientExtension

/-!
# Root-generated source perfectification face

This is the root-controlled entry for the universal coimage producer.  The
input is an already admitted `RootGeneratedCofinalHistoryCochainDualityStepAt`:
its history, cochain, faithful realization, pairing, exact occurrence,
whole-ledger write-back, and generated next are therefore one source-owned
step.  The producer only adds the canonical quotient
`P := C / ker (C → Dual C)` and its universal factorization; it does not
rebuild a second history or compare sibling shadows.

The generated face reports dualizability, bounded observation eligibility, or
an exact representation residual.  No finite, projective, nondegenerate,
determinant, inverse, or perfectness premise is accepted.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainDuality

open CofinalHistorySettlement
open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open SourceGeneratedDualEvaluation
open SourceGeneratedPerfectification
open SourceGeneratedCanonicalPerfectPair
open ExactPerfectEnvelopeBoundedDisposition
open CofinalPerfectAmbient
open SourceGeneratedPerfectAmbient

noncomputable section

universe u

namespace RootGeneratedCofinalHistoryCochainDualityStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

abbrev PerfectificationCarrier
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) : Type u :=
  SourceGeneratedPerfectification.PerfectificationCarrier
    step.pairingFace.leftEvaluation

def canonicalMap
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    step.commonStep.history.CompletionCarrier →ₗ[ℤ]
      step.PerfectificationCarrier :=
  SourceGeneratedPerfectification.canonicalMap step.pairingFace.leftEvaluation

def dualEmbedding
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    step.PerfectificationCarrier →ₗ[ℤ]
      Module.Dual ℤ step.commonStep.history.CompletionCarrier :=
  SourceGeneratedPerfectification.dualEmbedding step.pairingFace.leftEvaluation

@[simp] theorem dualEmbedding_comp_canonicalMap
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    (step.dualEmbedding).comp step.canonicalMap =
      step.pairingFace.leftEvaluation :=
  SourceGeneratedPerfectification.dualEmbedding_comp_canonicalMap
    step.pairingFace.leftEvaluation

theorem dualEmbedding_injective
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Function.Injective step.dualEmbedding :=
  SourceGeneratedPerfectification.dualEmbedding_injective
    step.pairingFace.leftEvaluation

theorem canonicalMap_universal
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    {Q : Type*} [AddCommGroup Q]
    (map : step.commonStep.history.CompletionCarrier →ₗ[ℤ] Q)
    (kernel_compatibility :
      LinearMap.ker step.pairingFace.leftEvaluation ≤ LinearMap.ker map) :
    ∃! factor : step.PerfectificationCarrier →ₗ[ℤ] Q,
      factor.comp step.canonicalMap = map :=
  SourceGeneratedPerfectification.canonicalMap_universal
    step.pairingFace.leftEvaluation map kernel_compatibility

def perfectificationDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    SourceGeneratedPerfectification.PerfectificationDisposition
      step.pairingFace.leftEvaluation :=
  SourceGeneratedPerfectification.settlePerfectification
    step.pairingFace.leftEvaluation

def presentationDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    SourceGeneratedPerfectification.PerfectificationPresentationDisposition
      step.pairingFace.leftEvaluation :=
  SourceGeneratedPerfectification.settlePerfectificationPresentation
    step.pairingFace.leftEvaluation

def finiteObservationDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    {O : Type*} [AddCommGroup O]
    (observation : step.PerfectificationCarrier →ₗ[ℤ] O) :
    SourceGeneratedPerfectification.FiniteObservationDisposition observation :=
  SourceGeneratedPerfectification.settleFiniteObservation observation

def boundedDualizableObservationDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    {O : Type*} [AddCommGroup O]
    (observation : step.PerfectificationCarrier →ₗ[ℤ] O) :
    SourceGeneratedPerfectification.BoundedDualizableObservationDisposition
      step.pairingFace.leftEvaluation observation :=
  SourceGeneratedPerfectification.settleBoundedDualizableObservation
    step.pairingFace.leftEvaluation observation

abbrev ActualAmbientLiftDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (soundness : GeneratedRelationSoundnessAt step.commonStep.faithful) :=
  SourceGeneratedPerfectification.SourceGeneratedAmbientLiftDisposition
    step.pairingFace.leftEvaluation
    (step.commonStep.faithful.completionEvaluation soundness)

/-! This package is the sole new authority face.  The step parameter keeps
the source occurrence and its root/ledger/next identity in the type. -/
structure Generated
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Type (u + 3) where
  canonical : step.commonStep.history.CompletionCarrier →ₗ[ℤ]
    step.PerfectificationCarrier
  embedding : step.PerfectificationCarrier →ₗ[ℤ]
    Module.Dual ℤ step.commonStep.history.CompletionCarrier
  canonicalPerfectPair :
    SourceGeneratedCanonicalPerfectPair.Generated
      step.pairingFace.leftEvaluation
  perfectification :
    SourceGeneratedPerfectification.PerfectificationDisposition
      step.pairingFace.leftEvaluation
  presentation :
    SourceGeneratedPerfectification.PerfectificationPresentationDisposition
      step.pairingFace.leftEvaluation
  common : CommonDualityDisposition step
  duality : DualityDispositionOutcome step.pairingFace
  ambient : PerfectAmbientDispositionOutcome step
  ambientExtension :
    SourceGeneratedPerfectAmbient.PerfectAmbientExtensionDisposition
      step.pairingFace.leftEvaluation
  actualLiftDisposition : ∀ soundness : GeneratedRelationSoundnessAt
    step.commonStep.faithful, ActualAmbientLiftDisposition step soundness

def sourceGeneratedPerfectification
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Generated step where
  canonical := step.canonicalMap
  embedding := step.dualEmbedding
  canonicalPerfectPair := SourceGeneratedCanonicalPerfectPair.generate
    step.pairingFace.leftEvaluation
  perfectification := step.perfectificationDisposition
  presentation := step.presentationDisposition
  common := step.disposition
  duality := step.dualityDisposition
  ambient := settlePerfectAmbient step
  ambientExtension :=
    SourceGeneratedPerfectAmbient.settlePerfectAmbientExtension
      step.pairingFace.leftEvaluation
  actualLiftDisposition := fun soundness =>
    SourceGeneratedPerfectification.settleSourceGeneratedAmbientLift
      step.pairingFace.leftEvaluation
      (step.commonStep.faithful.completionEvaluation soundness)

theorem generated_total
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Nonempty (Generated step) :=
  ⟨step.sourceGeneratedPerfectification⟩

theorem generated_embedding_comp_canonical
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    (step.sourceGeneratedPerfectification.embedding).comp
        step.sourceGeneratedPerfectification.canonical =
      step.pairingFace.leftEvaluation := by
  exact step.dualEmbedding_comp_canonicalMap

theorem generated_canonicalPerfectPair_left_zigzag
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    step.sourceGeneratedPerfectification.canonicalPerfectPair.coevaluation.comp
        step.sourceGeneratedPerfectification.canonicalPerfectPair.map =
      LinearMap.id :=
  SourceGeneratedCanonicalPerfectPair.generated_left_zigzag
    step.pairingFace.leftEvaluation

theorem generated_canonicalPerfectPair_right_zigzag
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    step.sourceGeneratedPerfectification.canonicalPerfectPair.map.comp
        step.sourceGeneratedPerfectification.canonicalPerfectPair.coevaluation =
      LinearMap.id :=
  SourceGeneratedCanonicalPerfectPair.generated_right_zigzag
    step.pairingFace.leftEvaluation

def exactBoundedObservationDisposition
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    {O : Type*} [AddCommGroup O]
    (observation : step.PerfectificationCarrier →ₗ[ℤ] O) :
    ExactPerfectEnvelopeBoundedDisposition.Disposition
      step.pairingFace.leftEvaluation observation :=
  ExactPerfectEnvelopeBoundedDisposition.settle
    step.pairingFace.leftEvaluation observation

end RootGeneratedCofinalHistoryCochainDualityStepAt

end
end CofinalHistoryCochainDuality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

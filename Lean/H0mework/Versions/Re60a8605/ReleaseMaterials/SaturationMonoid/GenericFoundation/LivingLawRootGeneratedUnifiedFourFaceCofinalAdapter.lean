import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Realization.Faces.DualityTransport

/-!
# Root-controlled installation of the unified four-face producer

The source-polymorphic producer is installed here on the existing cofinal
history/cochain/duality step.  The input occurrence is exactly the common
step's emitted source occurrence; the evaluation is the installed pairing and
the faithful map is the common step's completion evaluation.  The package is
therefore a dependent face of the existing root, not a new source.  The
whole-ledger write-back and generated next are read directly from the parent
step.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainDuality

open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open UnifiedFourFace

noncomputable section

universe u

namespace RootGeneratedCofinalHistoryCochainDualityStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

abbrev UnifiedSource
    (_step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    visit.current

abbrev UnifiedCarrier
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  step.commonStep.history.CompletionCarrier

abbrev UnifiedInput
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) : Type _ :=
  Input (UnifiedSource step) Unit Unit Unit Unit Unit Unit
    (UnifiedCarrier step) (UnifiedCarrier step)

def unifiedInput
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    UnifiedInput step where
  occurrence := step.commonStep.history.root
  algebraAt := fun _ => ()
  combinatorialAt := fun _ => ()
  topologicalAt := fun _ => ()
  logicalAt := fun _ => ()
  relationAt := fun _ => ()
  cochainAt := fun _ => ()
  dualEvaluationAt := fun _ => step.pairingFace.leftEvaluation
  faithfulAt := fun _ => LinearMap.id

def unifiedGenerated
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    UnifiedFourFace.Generated (unifiedInput step) :=
  UnifiedFourFace.generate (unifiedInput step)

@[simp] theorem unifiedInput_occurrence
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    (unifiedInput step).occurrence = step.commonStep.history.root :=
  rfl

theorem unifiedGenerated_readback
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    (unifiedGenerated step).embedding.comp
        (unifiedGenerated step).canonical =
      UnifiedFourFace.RootDualEvaluation (unifiedInput step) :=
  UnifiedFourFace.generated_dual_readback (unifiedInput step)

theorem unifiedGenerated_canonical_perfect_pair_readback
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    (unifiedGenerated step).canonicalPerfectPair.inclusion.comp
        (unifiedGenerated step).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (UnifiedFourFace.RootDualEvaluation (unifiedInput step)) :=
  SourceGeneratedCanonicalPerfectPair.generated_readback
    (UnifiedFourFace.RootDualEvaluation (unifiedInput step))

theorem unifiedGenerated_total
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    Nonempty (UnifiedFourFace.Generated (unifiedInput step)) :=
  UnifiedFourFace.generated_total (unifiedInput step)

theorem unified_wholeLedgerWriteBack_eq_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    HEq (step.wholeLedgerWriteBack)
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  step.wholeLedgerWriteBack_eq_root

@[simp] theorem unified_nextCurrent_eq_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.nextCurrent_eq_root

end RootGeneratedCofinalHistoryCochainDualityStepAt

end
end CofinalHistoryCochainDuality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

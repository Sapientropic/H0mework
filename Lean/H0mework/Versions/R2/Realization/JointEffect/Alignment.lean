import H0mework.Foundation.Source.UnfoldingZip
import H0mework.Versions.R2.Realization.JointState.TransitionController

/-!
# Full source/target alignment for a dependent joint effect

The compiler target owns a complete pairing occurrence, not only a root
pairing.  This kernel canonically zips the source and target pairing trees by
their accounted branch positions.  Shape mismatch is retained as an explicit
representation residual.  On the aligned branch every corresponding pair is
sent through the existing total joint-transition classifier.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open CofinalHistoryTransition
open RootedAccountedUnfoldingZip
open RootLawDependentJointStateController
open RootLawDependentJointTransition

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def stepTargetExposureAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (pairing : PairingAt recognition.material.parent
      successor.targetOccurrence) :=
  recognition.material.exposureAt successor.targetOccurrence pairing

abbrev PairingAlignmentDispositionAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :=
  RootedAccountedUnfoldingZip.Disposition
    (stepSourcePairingOccurrence step)
    (stepTargetPairingOccurrence step successor)

def settlePairingAlignment
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    PairingAlignmentDispositionAt step successor :=
  RootedAccountedUnfoldingZip.settle
    (stepSourcePairingOccurrence step)
    (stepTargetPairingOccurrence step successor)

abbrev AlignedPairAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :=
  PairingAt recognition.material.parent step.sourceOccurrence ×
    PairingAt recognition.material.parent successor.targetOccurrence

abbrev AlignedJointPayloadAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :=
  Σ pair : AlignedPairAt step successor,
    JointTransitionDispositionAt history pair.1 pair.2
      (stepSourceExposureAt step pair.1).sourceAction.carrierAction
      (stepTargetExposureAt step successor pair.2).sourceAction.carrierAction
      (stepSourceExposureAt step pair.1).measurement
      (stepTargetExposureAt step successor pair.2).measurement
      (stepSourceExposureAt step pair.1).hilbertEvolution
      (stepTargetExposureAt step successor pair.2).hilbertEvolution

def alignedJointPayloadAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (pair : AlignedPairAt step successor) :
    AlignedJointPayloadAt step successor history :=
  ⟨pair, settleJointTransition history pair.1 pair.2
    (stepSourceExposureAt step pair.1).sourceAction.carrierAction
    (stepTargetExposureAt step successor pair.2).sourceAction.carrierAction
    (stepSourceExposureAt step pair.1).measurement
    (stepTargetExposureAt step successor pair.2).measurement
    (stepSourceExposureAt step pair.1).hilbertEvolution
    (stepTargetExposureAt step successor pair.2).hilbertEvolution⟩

def alignedJointOccurrence
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step)
      (stepTargetPairingOccurrence step successor)) :
    RootedAccountedUnfolding
      (AlignedJointPayloadAt step successor history) :=
  alignment.tree.map (alignedJointPayloadAt step successor history)

theorem alignedJointOccurrence_source_rooted
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step)
      (stepTargetPairingOccurrence step successor)) :
    (alignedJointOccurrence step successor history alignment).map
        (fun payload => payload.1.1) =
      stepSourcePairingOccurrence step := by
  rw [alignedJointOccurrence, RootedAccountedUnfolding.map_map]
  change alignment.tree.map Prod.fst = stepSourcePairingOccurrence step
  exact alignment.left_projection

theorem alignedJointOccurrence_target_rooted
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step)
      (stepTargetPairingOccurrence step successor)) :
    (alignedJointOccurrence step successor history alignment).map
        (fun payload => payload.1.2) =
      stepTargetPairingOccurrence step successor := by
  rw [alignedJointOccurrence, RootedAccountedUnfolding.map_map]
  change alignment.tree.map Prod.snd =
    stepTargetPairingOccurrence step successor
  exact alignment.right_projection

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

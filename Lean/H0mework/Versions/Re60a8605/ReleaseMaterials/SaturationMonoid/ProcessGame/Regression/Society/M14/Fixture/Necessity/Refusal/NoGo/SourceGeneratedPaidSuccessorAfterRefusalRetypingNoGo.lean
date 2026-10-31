import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Refusal.Producer.SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver

/-!
# After-refusal retaliation retyping no-gos

The positive target response is retained in every false fibre below.  Price,
service, administrative readout, and the real employment-termination action
cannot be retyped as capture by the target's own noncapture compiler.  Replacing
that compiler by the existing full-capture compiler instead deletes the
noncapture fibre and yields the already constructed capacity-zero countermodel.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost Observer
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M10OccurrenceCapacityProcessFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation

/-! ## Administrative observer kernel -/

abbrev AdministrativeRetaliationOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  AnyContributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
    sourceIndex

abbrev AdministrativeRetaliationVisible :=
  ExactUBIRootRestrictionAt focalSeed

def administrativeRetaliationObserver
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    AuthorityObserver
      (AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex)
      AdministrativeRetaliationVisible AnyPeriodicActualServiceExit where
  forget := fun occurrence => administrativeEligibilityReadout (label occurrence)
  authorityK := fun occurrence =>
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
      oldVisit sourceIndex occurrence.1

def administrativeRetaliationKernelPair
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    AuthorityKernelPair
      (administrativeRetaliationObserver oldVisit sourceIndex label) where
  left := antiRetaliation.standingRenewal.sourceOuterAuthority
  right := antiRetaliation.standingRenewal.targetOuterAuthority
  occurrence_ne := antiRetaliation.sourceAndTargetOuterAuthorities_distinct
  visible_eq := by
    cases label antiRetaliation.standingRenewal.sourceOuterAuthority <;>
      cases label antiRetaliation.standingRenewal.targetOuterAuthority <;>
      rfl
  authority_ne :=
    antiRetaliation.sourceAndTargetActualServiceK_distinct

theorem administrativeRetaliation_noAuthorityFactorization
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ Nonempty
      (AuthorityFactorization
        (administrativeRetaliationObserver oldVisit sourceIndex label)) :=
  (administrativeRetaliationKernelPair antiRetaliation label
    ).noAuthorityFactorization

theorem administrativeRetaliation_noOccurrenceLeftInverse
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ ∃ reconstruct : AdministrativeRetaliationVisible →
        AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (administrativeRetaliationObserver oldVisit sourceIndex label).forget :=
  (administrativeRetaliationKernelPair antiRetaliation label
    ).noOccurrenceLeftInverse

theorem administrativeRetaliation_noFaithfulReconstruction
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (administrativeRetaliationObserver oldVisit sourceIndex label)) :=
  (administrativeRetaliationKernelPair antiRetaliation label
    ).noFaithfulAuthorityReconstruction

/-! ## Exact false retaliation fibres -/

/-- The installed target compiler cannot recapture its own exact response
action. -/
structure ExactAfterRefusalOwnPolicyPriceRecaptureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 29 where
  private mk ::
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  recaptured : birthBearerNoCapture.Captures
    antiRetaliation.targetResponseAction.1

theorem afterRefusalOwnPolicyPriceRecapture_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactAfterRefusalOwnPolicyPriceRecaptureAt oldVisit sourceIndex
        index) :=
  ⟨fun falseRecapture =>
    falseRecapture.antiRetaliation.targetPayment.responseActionUncaptured
      falseRecapture.recaptured⟩

/-- A target channel keeps its exact service authority but cannot manufacture
a price recapture verdict. -/
structure ExactAfterRefusalServiceRecaptureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) : Type 30 where
  private mk ::
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  targetService :
    ConsumedContributionCapacityPostSettlementChannelAt oldVisit sourceIndex
      (index + 1) channel
  targetServiceExact : targetService =
    antiRetaliation.targetChannel channel
  recaptured : birthBearerNoCapture.Captures
    antiRetaliation.targetResponseAction.1

theorem afterRefusalServiceRecapture_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (channel : EssentialAccessChannel) :
    IsEmpty
      (ExactAfterRefusalServiceRecaptureAt oldVisit sourceIndex index
        channel) :=
  ⟨fun falseRecapture =>
    falseRecapture.antiRetaliation.targetPayment.responseActionUncaptured
      falseRecapture.recaptured⟩

/-- An administrative label retains its real root-restriction readout but
cannot be retyped as capture authority. -/
structure ExactAfterRefusalAdministrativeRecaptureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 30 where
  private mk ::
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  label : Bool
  eligibilityReadout : AdministrativeRetaliationVisible
  eligibilityReadoutExact : eligibilityReadout =
    administrativeEligibilityReadout label
  recaptured : birthBearerNoCapture.Captures
    antiRetaliation.targetResponseAction.1

theorem afterRefusalAdministrativeRecapture_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactAfterRefusalAdministrativeRecaptureAt oldVisit sourceIndex
        index) :=
  ⟨fun falseRecapture =>
    falseRecapture.antiRetaliation.targetPayment.responseActionUncaptured
      falseRecapture.recaptured⟩

/-- The real employment-termination action, controller and source trace remain
present but cannot be retyped as capture of the bearer-owned response. -/
structure ExactAfterRefusalEmploymentRetaliationRecaptureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 30 where
  private mk ::
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  terminationAction : birthBearerEmploymentController.ExactActionSeed
  terminationActionExact : terminationAction =
    birthBearerExactEmploymentAction
  terminationControllerExact :
    birthBearerEmploymentController.ControllerAt terminationAction
      birthBearerEmployer
  terminationSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerEmploymentController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerEmploymentController.actionAdmittedAt terminationAction.1
  recaptured : birthBearerNoCapture.Captures
    antiRetaliation.targetResponseAction.1

theorem afterRefusalEmploymentRetaliationRecapture_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactAfterRefusalEmploymentRetaliationRecaptureAt oldVisit sourceIndex
        index) :=
  ⟨fun falseRecapture =>
    falseRecapture.antiRetaliation.targetPayment.responseActionUncaptured
      falseRecapture.recaptured⟩

/-- Full capture really captures the same target action; therefore reporting
that compiler replacement as nonretaliatory is an exact empty replay. -/
structure ExactAfterRefusalFullCaptureReportedNonretaliatoryAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 30 where
  private mk ::
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  falseNoncapture :
    ExactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
      birthBearerFullCapture

theorem afterRefusalFullCaptureReportedNonretaliatory_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit
        sourceIndex index) :=
  ⟨fun falseReport =>
    (fullCaptureNoncapture_isEmpty falseReport.antiRetaliation).false
      falseReport.falseNoncapture⟩

theorem fullCaptureCountermodelCannotReconstructNonretaliatoryReplay
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
          sourceIndex index →
        ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit
          sourceIndex index) :=
  ⟨fun reconstruct =>
    (afterRefusalFullCaptureReportedNonretaliatory_isEmpty oldVisit
      sourceIndex index).false
      (reconstruct
        (exactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
          sourceIndex index))⟩

end
end M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo.administrativeRetaliation_noAuthorityFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo.afterRefusalOwnPolicyPriceRecapture_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo.afterRefusalServiceRecapture_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo.afterRefusalAdministrativeRecapture_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo.afterRefusalEmploymentRetaliationRecapture_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo.afterRefusalFullCaptureReportedNonretaliatory_isEmpty

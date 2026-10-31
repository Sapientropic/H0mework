import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Consumer.ProofCarryingPlatformGateFullAdmission
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Consumer.ProofCarryingCanonicalSocietyCofinalReadout

/-!
# Platform full admission on the cofinal finite-law diagonal

This consumer joins the completed platform admission to the already canonical
paid recurrence at the same `oldVisit/sourceIndex/boundary`.  Their common
seam is the existing `rightReplayAt`; no occurrence equality across ambient
roots is introduced.

For every requested finite law prefix, the existing cofinal readout then
produces a strictly later audited pulse.  That pulse carries the finite root
law, two different actual paths with one normal form and different `K`, the
next actual Payment, target-deletion no-gos, runtime-finality failure and the
literal next cycle generated from the preceding step.  No cofinal schedule or
completed future is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPlatformGateCofinalFiniteLawDiagonal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingPlatformGateFullAdmission

structure PlatformGateFiniteLawDiagonalPointAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (fuel observerFuel m : Nat) : Prop where
  private mk ::
  later : fuel < m
  pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m
  pointMaterial :
    CanonicalSocietyCofinalPointMaterialAt initial observerFuel m pulse
  generatedFinalNextExact :
    generatedFinalNextCycleAt initial m = cycleAt initial (m + 1)
  actualPathsDistinct :
    type_of% pointMaterial.selfU8ActualPathsDistinct
  sameNormalFormDifferentK :
    type_of% pointMaterial.selfU8SameNormalDifferentK
  paymentOccurrencesDistinct :
    type_of% pointMaterial.selfU8PaymentOccurrencesDistinct
  nextPaymentIsFutureBirthPayment :
    type_of% pointMaterial.nextSelfU8PaymentIsFutureBirthPayment
  runtimeFinalityEmpty :
    type_of% pointMaterial.runtimeFinalityReportEmpty
  targetDeletionNoGo : type_of% pointMaterial.targetDeletionNoGo

theorem platformGateFiniteLawDiagonalPointAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (cofinal : ProofCarryingCanonicalSocietyCofinalReadoutAt initial)
    (fuel observerFuel : Nat) :
    ∃ m, PlatformGateFiniteLawDiagonalPointAt initial fuel observerFuel m := by
  rcases cofinal.everyRequestedPoint fuel observerFuel with
    ⟨m, later, pulse, pointMaterial⟩
  exact ⟨m,
    { later := later
      pulse := pulse
      pointMaterial := pointMaterial
      generatedFinalNextExact :=
        generatedFinalNextCycle_eq_cycleAt_succ initial m
      actualPathsDistinct := pointMaterial.selfU8ActualPathsDistinct
      sameNormalFormDifferentK :=
        pointMaterial.selfU8SameNormalDifferentK
      paymentOccurrencesDistinct :=
        pointMaterial.selfU8PaymentOccurrencesDistinct
      nextPaymentIsFutureBirthPayment :=
        pointMaterial.nextSelfU8PaymentIsFutureBirthPayment
      runtimeFinalityEmpty := pointMaterial.runtimeFinalityReportEmpty
      targetDeletionNoGo := pointMaterial.targetDeletionNoGo }⟩

structure ProofCarryingPlatformGateCofinalFiniteLawDiagonalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) : Prop where
  private mk ::
  fullAdmission : Nonempty
    (ProofCarryingPlatformGateFullAdmissionAt oldVisit sourceIndex boundary)
  fullAdmissionConsumer :
    type_of% (platformGateFullAdmission_directConsumer oldVisit sourceIndex
      boundary)
  fullAdmissionRightPaymentExact :
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.rootOccurrence
  initialCycleRightReplayExact :
    (nextNovelty (stepAt initial 0)).leftReplay =
      rightReplayAt oldVisit sourceIndex boundary
  canonicalCofinalReadout :
    ProofCarryingCanonicalSocietyCofinalReadoutAt initial
  everyFiniteLawPrefix : ∀ fuel observerFuel,
    ∃ m, PlatformGateFiniteLawDiagonalPointAt initial fuel observerFuel m
  everyRuntimeFinalityReportEmpty :
    type_of% canonicalCofinalReadout.everyRuntimeFinalityReportEmpty

theorem proofCarryingPlatformGateCofinalFiniteLawDiagonal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    ProofCarryingPlatformGateCofinalFiniteLawDiagonalAt initial := by
  let fullAdmission :=
    proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
  let canonicalCofinalReadout :=
    proofCarryingCanonicalSocietyCofinalReadout initial
  let firstRecurrence :=
    proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (stepAt initial 0)
  exact
    { fullAdmission := ⟨fullAdmission⟩
      fullAdmissionConsumer :=
        platformGateFullAdmission_directConsumer oldVisit sourceIndex boundary
      fullAdmissionRightPaymentExact :=
        fullAdmission.materialFulfillment.admittedObligation.paidAuthorityFace
          |>.exactRightPaymentOccurrence
      initialCycleRightReplayExact := firstRecurrence.oldRightIsNextLeft
      canonicalCofinalReadout := canonicalCofinalReadout
      everyFiniteLawPrefix :=
        platformGateFiniteLawDiagonalPointAt canonicalCofinalReadout
      everyRuntimeFinalityReportEmpty :=
        canonicalCofinalReadout.everyRuntimeFinalityReportEmpty }

theorem platformGateCofinalFiniteLawDiagonal_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    let diagonal := proofCarryingPlatformGateCofinalFiniteLawDiagonal initial
    ProofCarryingPlatformGateCofinalFiniteLawDiagonalAt initial ∧
      Nonempty (ProofCarryingPlatformGateFullAdmissionAt oldVisit sourceIndex
        boundary) ∧
      (nextNovelty (stepAt initial 0)).leftReplay =
        rightReplayAt oldVisit sourceIndex boundary ∧
      (∀ fuel observerFuel,
        ∃ m, PlatformGateFiniteLawDiagonalPointAt initial fuel observerFuel m) ∧
      type_of% diagonal.everyRuntimeFinalityReportEmpty := by
  dsimp
  let diagonal := proofCarryingPlatformGateCofinalFiniteLawDiagonal initial
  exact ⟨diagonal,
    diagonal.fullAdmission,
    diagonal.initialCycleRightReplayExact,
    diagonal.everyFiniteLawPrefix,
    diagonal.everyRuntimeFinalityReportEmpty⟩

end
end M14ProofCarryingPlatformGateCofinalFiniteLawDiagonal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateCofinalFiniteLawDiagonal.platformGateFiniteLawDiagonalPointAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateCofinalFiniteLawDiagonal.proofCarryingPlatformGateCofinalFiniteLawDiagonal
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateCofinalFiniteLawDiagonal.platformGateCofinalFiniteLawDiagonal_directConsumer

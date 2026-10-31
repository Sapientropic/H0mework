import H0mework.Foundation.Arithmetic.TerminalAuthority
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.EconomicSingleFold
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRenewalRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Recognition.ProofCarryingRecognitionWitnessEscapeRegression

/-!
# M14 source-generated economic disposition

The synchronized fold image does not choose an update.  This module factors
the already generated ordinary repair, its fixed viable successor, and the
existing self-U8 update into branch-dependent landing fibres.  A grounded
terminal can arise only through the existing root-native terminal classifier;
the fixed M14 root has no such branch.

The disposition is indexed by an exact accounted occurrence, its fold image,
and an optional heterogeneous landing.  Callers cannot submit an image,
branch tag, capacity, repair, U8 core, terminal, or next to any producer.
No economic AST, second fold, root, ledger, registry, pending branch, or
completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14GeneratedEconomicDisposition

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootedAccountedUnfolding RootArithmeticTerminalAuthority
open Renewal Revision UBI Capacity Policy Legislation Observer Settlement Money
open Settlement.SourceOwnedSettlementCompiler
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M3SettlementDispositionRegression
open M6GoNaturalAuthorityReconstructionRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingLegislationRegression
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14UBIExitCapacityFixture
open M14PeriodicMandatePowerRenewal
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14TenureCaptureRouteRepairNoGoRegression
open M14UBIPolicyBreakingOccurrence
open M14UBIPolicySelfU8Regression
open M14UBIProofCarryingLegislationRegression
open M14ProofCarryingRecognitionWitnessEscapeRegression
open M14EconomicSingleFold

abbrev EconomicLanding := Option AnyAuthoritativeRootCurrent.{0}

def tenureRepairExposureAt (depth : Nat) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  economicRepairExposure (tenureEconomicFailureOccurrenceAt depth)

def tenureEconomicImageAt (depth : Nat) : EconomicFoldImage :=
  economicImage (tenureRepairExposureAt depth)

/-- The repaired landing at one generated depth is witnessed by the exact
repair atom at the next temporal occurrence, rather than by the old failure
image. -/
def postRepairViableExposureAt (depth : Nat) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  .zero (tenureExactEconomicRepairAtomAt (depth + 1))

def postRepairViableImageAt (depth : Nat) : EconomicFoldImage :=
  economicImage (postRepairViableExposureAt depth)

@[simp] theorem postRepairViableExposureAt_rootEvent (depth : Nat) :
    (postRepairViableExposureAt depth).root.erasedRootEvent =
      ⟨temporalVisitAt (depth + 1),
        (periodicSourceBackedPaymentAt (depth + 1)).rootOccurrence⟩ := by
  unfold postRepairViableExposureAt tenureExactEconomicRepairAtomAt
    exactRepairAtom ExactEconomicAtom.ofCanonicalRepair
    RootedAccountedUnfolding.zero
  exact ExactEconomicAtom.erasedRootEvent_ofRepair
    (SourceGeneratedProofCarryingExitRepairAt.generate
      (tenureCaptureOriginAt (depth + 1)))

/-- Definitionally preserved fixed aliases. -/
abbrev postRepairViableExposure := postRepairViableExposureAt 0

abbrev postRepairViableImage := postRepairViableImageAt 0

@[simp] theorem postRepairViableExposure_rootEvent :
    postRepairViableExposure.root.erasedRootEvent =
      ⟨temporalVisitAt 1,
        (periodicSourceBackedPaymentAt 1).rootOccurrence⟩ :=
  postRepairViableExposureAt_rootEvent 0

def actualOrdinaryRenewalAt (depth : Nat) :
    SourceInstalledProofCarryingExitRepairRenewalAt depth
      (canonicalRepairAt (tenureCaptureOriginAt depth)) :=
  SourceInstalledProofCarryingExitRepairRenewalAt.generate depth

def ordinaryEconomicLandingAt (depth : Nat) : EconomicLanding :=
  some
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      (actualOrdinaryRenewalAt depth).generatedNext⟩ :
      AnyAuthoritativeRootCurrent)

def revolutionaryEconomicLanding : EconomicLanding :=
  sourceGeneratedUBIProofCarryingLegislation.policyLegislation
    |>.revolutionaryConsumption |>.map
      (fun _ =>
        sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext)

@[simp] theorem revolutionaryEconomicLanding_eq_some :
    revolutionaryEconomicLanding =
      some sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext :=
  rfl

/-! ## Ordinary repair factor -/

/-- Every actual installed tenure repair factors into the exact fold image
and the old-law generated landing determined by that repair. -/
structure SourceGeneratedOrdinaryEconomicDispositionAt
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) (landing : EconomicLanding) : Type 18 where
  private mk ::
  depth : Nat
  occurrence_eq : occurrence = tenureRepairExposureAt depth
  image_eq : image = economicImage occurrence
  economicRootEventExact : occurrence.root.erasedRootEvent =
    ⟨temporalVisitAt depth,
      (periodicSourceBackedPaymentAt depth).rootOccurrence⟩
  renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth
    (canonicalRepairAt (tenureCaptureOriginAt depth))
  rootOccurrenceExact : renewal.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  selectedWriteCommutes :
    renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld
  wholeLedgerExact : renewal.wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (temporalVisitAt depth)).wholeLedgerWriteBack
  rootFactorization : renewal.source.installed.RootAnswerAndNextFactorizes
  landing_eq : landing = some
    (⟨M9ProofCarryingRenewalInquiryRoot.N, renewal.generatedNext⟩ :
      AnyAuthoritativeRootCurrent)
  generatedNextExact : renewal.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  lawSurfacePreserved : renewal.generatedNext.root.source.lawSurface =
    jointRoot.source.base.lawSurface

/-- Factor an existing actual renewal.  The return indices compute the image
and landing; they are not inputs. -/
def ordinaryEconomicDispositionOf {depth : Nat}
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth
      (canonicalRepairAt (tenureCaptureOriginAt depth))) :
    SourceGeneratedOrdinaryEconomicDispositionAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth)
      (some
        (⟨M9ProofCarryingRenewalInquiryRoot.N, renewal.generatedNext⟩ :
          AnyAuthoritativeRootCurrent)) where
  depth := depth
  occurrence_eq := rfl
  image_eq := rfl
  economicRootEventExact := tenureRepairExposure_rootEvent depth
  renewal := renewal
  rootOccurrenceExact := renewal.rootOccurrence_eq
  selectedWriteCommutes := renewal.ordinarySelectedWrite_commutes
  wholeLedgerExact := rfl
  rootFactorization := renewal.appliedReform.rootFactorization
  landing_eq := rfl
  generatedNextExact := renewal.generatedNext_eq_rootCompiler
  lawSurfacePreserved := renewal.lawSurface_preserved

def ordinaryEconomicDispositionAt (depth : Nat) :
    SourceGeneratedOrdinaryEconomicDispositionAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth)
      (ordinaryEconomicLandingAt depth) :=
  ordinaryEconomicDispositionOf (actualOrdinaryRenewalAt depth)

/-! ## Periodic repaired viable successor -/

/-- The first repaired successor is viable in the exact proven sense used by
the M14 flagship: it has an actual payment-route-service exit, a root
responsibility consumer, renewed mandate authority, residual consumption,
observer correction, and an open U8 route.  Capacity one is retained as a
readout but is not the producer mouth. -/
structure SourceGeneratedPostRepairViableEconomicDispositionAt
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) (landing : EconomicLanding) : Type 18 where
  private mk ::
  depth : Nat
  occurrence_eq : occurrence = postRepairViableExposureAt depth
  image_eq : image = economicImage occurrence
  economicRootEventExact : occurrence.root.erasedRootEvent =
    ⟨temporalVisitAt (depth + 1),
      (periodicSourceBackedPaymentAt (depth + 1)).rootOccurrence⟩
  ordinary : SourceGeneratedOrdinaryEconomicDispositionAt
    (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) landing
  nextVisitExact : ordinary.renewal.generatedNext.visit =
    temporalVisitAt (depth + 1)
  actualExit : PeriodicActualServiceExitAt (depth + 1)
  actualExitCapacity :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  ordinaryRootConsumer : RenewalResponsibilityConsumerAt
    ordinary.renewal.source.installed.operationalAuthority
  successorRootConsumer : RenewalResponsibilityConsumerAt
    actualExit.paymentOccurrence.installed.operationalAuthority
  mandate : SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt
    (depth + 1)
  mandateRootExact : mandate.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  residualConsumer : Nonempty
    (OpenSettlementAt.ActivatedResidualConsumerAt
    (exactOpenSettlement exactResidualActivation))
  sourceOwnedResidual : Nonempty (SourceOwnsResponsibilityIncidence V
    (P.boundarySource
      capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
    (exactOpenSettlement exactResidualActivation).obligation)
  recognitionEscape : SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
    installedRecognitionWitness
  observerCorrection : Nonempty (FaithfulAuthorityReconstruction
    sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver)
  revisionRoute : Nonempty
    (FaithfulCofaceMorphism u8Gate.minimalCoface
      jointCore.revision.generate.toAdmissibleMinimalCoface)
  revisionRuntime :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0

def postRepairViableEconomicDispositionAt (depth : Nat) :
    SourceGeneratedPostRepairViableEconomicDispositionAt
      (postRepairViableExposureAt depth) (postRepairViableImageAt depth)
      (ordinaryEconomicLandingAt depth) :=
  let ordinary := ordinaryEconomicDispositionAt depth
  let actualExit := periodicActualServiceExitAt (depth + 1)
  let mandate := periodicMandatePowerRenewalAt (depth + 1)
  { depth := depth
    occurrence_eq := rfl
    image_eq := rfl
    economicRootEventExact := postRepairViableExposureAt_rootEvent depth
    ordinary := ordinary
    nextVisitExact := ordinary.renewal.generatedNext_repairedFace_capacity_eq_one.1
    actualExit := actualExit
    actualExitCapacity := actualExit.exactCapacity
    ordinaryRootConsumer := ordinary.renewal.appliedReform.rootConsumer
    successorRootConsumer :=
      actualExit.paymentOccurrence.installed.rootResponsibilityConsumer
    mandate := mandate
    mandateRootExact := mandate.rootOccurrenceExact
    residualConsumer :=
      sourceGeneratedUBIProofCarryingLegislation
        |>.residual_destination_commutes |>.2.1
    sourceOwnedResidual :=
      sourceGeneratedUBIProofCarryingLegislation
        |>.residual_destination_commutes |>.2.2
    recognitionEscape := sourceGeneratedProofCarryingRecognitionWitnessEscape
    observerCorrection :=
      proofCarryingRecognitionWitnessEscapeDirectConsumer
        |>.fullActualPathReconstruction
    revisionRoute := policyGate_factorizes_into_jointCore
    revisionRuntime :=
      runtime_consumes_jointCore_after_policy_factorization }

def fixedPostRepairViableEconomicDisposition :
    SourceGeneratedPostRepairViableEconomicDispositionAt
      postRepairViableExposure postRepairViableImage
      (ordinaryEconomicLandingAt 0) :=
  postRepairViableEconomicDispositionAt 0

/-! ## Existing self-U8 factor -/

/-- The fixed source-generated representation failure factors into the same
old fold image and the revised heterogeneous landing. -/
structure SourceGeneratedRequiresU8EconomicDispositionAt
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) (landing : EconomicLanding) : Type 18 where
  private mk ::
  occurrence_eq : occurrence = tenureRepairExposureAt 0
  image_eq : image = economicImage occurrence
  economicRootEventExact : occurrence.root.erasedRootEvent =
    ⟨temporalVisitAt 0,
      (periodicSourceBackedPaymentAt 0).rootOccurrence⟩
  legislation : SourceGeneratedUBIProofCarryingLegislationAt
  exactBreakingOccurrence :
    (⟨jointVisit.current, audit.rootOccurrence⟩ :
      Sigma M14UBIPolicyBreakingOccurrence.Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
      ⟨(temporalVisitAt 0).current,
        (periodicSourceBackedPaymentAt 0).rootOccurrence.occurrence⟩
  gateToCore : Nonempty
    (FaithfulCofaceMorphism u8Gate.minimalCoface
      jointCore.revision.generate.toAdmissibleMinimalCoface)
  exactFirstWrite : jointCore.cofaceFactorization.2.firstWrite =
    M13SelfU8Regression.selfU8.firstWrite
  runtimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0
  runtimeLanding_eq : landing =
    legislation.policyLegislation.revolutionaryConsumption.map
      (fun _ => legislation.policyLegislation.generatedNext)
  landing_eq : landing = some legislation.policyLegislation.generatedNext
  coordinateDistinct : jointUBIProjection ≠ jointInquiryProjection
  ordinaryLandingDistinct : ordinaryEconomicLandingAt 0 ≠ landing

def requiresU8EconomicDisposition :
    SourceGeneratedRequiresU8EconomicDispositionAt
      (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
      revolutionaryEconomicLanding :=
  let legislation := sourceGeneratedUBIProofCarryingLegislation
  { occurrence_eq := rfl
    image_eq := rfl
    economicRootEventExact := tenureRepairExposure_rootEvent 0
    legislation := legislation
    exactBreakingOccurrence := audit_rootOccurrence_is_payment_rootOccurrence
    gateToCore := policyGate_factorizes_into_jointCore
    exactFirstWrite := policyCore_firstWrite_is_selfU8_firstWrite
    runtimeConsumesCore :=
      runtime_consumes_jointCore_after_policy_factorization
    runtimeLanding_eq := rfl
    landing_eq := revolutionaryEconomicLanding_eq_some
    coordinateDistinct := ubi_projection_ne_inquiry_projection
    ordinaryLandingDistinct := by
      intro landing_eq
      apply legislation.ordinary_and_revolutionary_nexts_distinct
      exact Option.some.inj landing_eq }

/-! ## Root-native grounded terminal factor -/

/-- A fixed-root economic terminal is nothing more and nothing less than the
existing arithmetic terminal authority at that exact visit. -/
structure SourceGeneratedGroundedEconomicTerminalAt
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) (landing : EconomicLanding) : Type 18 where
  private mk ::
  depth : Nat
  occurrence_eq : occurrence = tenureRepairExposureAt depth
  image_eq : image = economicImage occurrence
  terminal : GeneratedRootArithmeticTerminalAt
    jointRoot.toAuthoritativeRoot (rootVisitAt depth)
  landing_eq : landing = none

/-- The only terminal producer first invokes the existing total root-native
classifier.  `none` cannot be supplied by a caller as terminal authority. -/
def generateGroundedEconomicTerminalAt? (depth : Nat) :
    Option (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) :=
  match generateRootArithmeticTerminalAt?
      jointRoot.toAuthoritativeRoot (rootVisitAt depth) with
  | none => none
  | some terminal => some
      { depth := depth
        occurrence_eq := rfl
        image_eq := rfl
        terminal := terminal
        landing_eq := rfl }

instance fixedGroundedEconomicTerminal_isEmpty (depth : Nat) :
    IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) :=
  ⟨fun disposition => nomatch disposition.terminal.terminalEvent⟩

/-- Terminal emptiness agrees with the root's actual self-loop successor; it
is not a missing classifier case. -/
theorem fixedRoot_has_actual_successor (depth : Nat) :
    (jointRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (rootVisitAt depth).current).nextCurrent? =
        some (rootVisitAt depth).current :=
  rfl

theorem fixed_grounded_terminal_classifier_eq_none (depth : Nat) :
    generateGroundedEconomicTerminalAt? depth = none := by
  unfold generateGroundedEconomicTerminalAt?
  generalize classifier_eq : generateRootArithmeticTerminalAt?
    jointRoot.toAuthoritativeRoot (rootVisitAt depth) = result
  cases result with
  | none => rfl
  | some terminal => exact nomatch terminal.terminalEvent

/-! ## Four branch factorization -/

abbrev EconomicDispositionAt
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) (landing : EconomicLanding) :=
  SourceGeneratedPostRepairViableEconomicDispositionAt
      occurrence image landing ⊕
    (SourceGeneratedOrdinaryEconomicDispositionAt
      occurrence image landing ⊕
    (SourceGeneratedRequiresU8EconomicDispositionAt
      occurrence image landing ⊕
    SourceGeneratedGroundedEconomicTerminalAt
      occurrence image landing))

/-- In the fixed self-loop root the `none` landing is empty across the whole
four-branch carrier, not only inside the terminal summand. -/
theorem fixedRoot_noneLandingDisposition_isEmpty
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) :
    IsEmpty (EconomicDispositionAt occurrence image none) :=
  ⟨fun disposition => by
    rcases disposition with viable | rest
    · cases viable.ordinary.landing_eq
    · rcases rest with ordinary | rest
      · cases ordinary.landing_eq
      · rcases rest with requiresU8 | terminal
        · cases requiresU8.landing_eq
        · exact nomatch terminal.terminal.terminalEvent⟩

def ordinaryDispositionAt (depth : Nat) : EconomicDispositionAt
    (tenureRepairExposureAt depth) (tenureEconomicImageAt depth)
    (ordinaryEconomicLandingAt depth) :=
  .inr (.inl (ordinaryEconomicDispositionAt depth))

def viableDisposition : EconomicDispositionAt
    postRepairViableExposure postRepairViableImage
    (ordinaryEconomicLandingAt 0) :=
  .inl fixedPostRepairViableEconomicDisposition

def requiresU8Disposition : EconomicDispositionAt
    (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
    revolutionaryEconomicLanding :=
  .inr (.inr (.inl requiresU8EconomicDisposition))

theorem ordinary_and_u8_share_image_but_not_landing :
    Nonempty (SourceGeneratedOrdinaryEconomicDispositionAt
      (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
      (ordinaryEconomicLandingAt 0)) ∧
      Nonempty (SourceGeneratedRequiresU8EconomicDispositionAt
        (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
        revolutionaryEconomicLanding) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding :=
  ⟨⟨ordinaryEconomicDispositionAt 0⟩,
    ⟨requiresU8EconomicDisposition⟩,
    requiresU8EconomicDisposition.ordinaryLandingDistinct⟩

end
end M14GeneratedEconomicDisposition
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14GeneratedEconomicDisposition.ordinaryEconomicDispositionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14GeneratedEconomicDisposition.fixedPostRepairViableEconomicDisposition
#print axioms SaturationMonoid.ProcessGame.Society.M14GeneratedEconomicDisposition.requiresU8EconomicDisposition
#print axioms SaturationMonoid.ProcessGame.Society.M14GeneratedEconomicDisposition.fixed_grounded_terminal_classifier_eq_none

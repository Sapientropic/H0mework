import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Death.PortfolioMaintenanceDeath
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalRevision

/-!
# M14 actual periodic essential-service restoration

At every generated finite root visit, the seventh pre-emitter renewal
coordinate installs the exact health-service action.  The action-bearing
payload then generates the selected row, responsibility consumer,
whole-ledger write-back, same-law next, and the next visit's full actionable
portfolio.

The public producer accepts only `depth`.  It accepts no domain, unit, source
prefix, target portfolio, capacity, row, landing, next current, exit repair,
or U8 object.  The next portfolio is recomputed after the root-generated
next; it is not stored in the pre-emitter payload.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicEssentialServiceRestoration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Renewal Revision UBI Capacity
open Space CrossingCost
open M9ProofCarryingRenewalInquiryRoot
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceEssentialServiceRestoration
open M14ActionableFuturePortfolio
open M14PortfolioMaintenanceDeath

/-! ## Installed action-bearing coordinate -/

def installedEssentialServiceRestorationAt (depth : Nat) :
    SourceInstalledRenewalAt essentialServiceRestorationRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

/-- Same-row bounded reform whose applied action is literally the disposition
already installed in the service-maintenance coordinate. -/
structure SourceInstalledAppliedEssentialServiceRestorationAt
    (depth : Nat)
    (installed : SourceInstalledRenewalAt
      essentialServiceRestorationRecognition (temporalVisitAt depth))
    (applied : EssentialServiceRestorationDispositionAt
      installed.payload.sourceSeed) : Type 3 where
  private mk ::
  applied_eq : applied = installed.payload.disposition
  reform : SourceNativeBoundedInstitutionalReformAt
    installed.operationalAuthority
  rootConsumer : RenewalResponsibilityConsumerAt
    installed.operationalAuthority
  rootFactorization : installed.RootAnswerAndNextFactorizes

namespace SourceInstalledAppliedEssentialServiceRestorationAt

def generate (depth : Nat)
    (installed : SourceInstalledRenewalAt
      essentialServiceRestorationRecognition (temporalVisitAt depth)) :
    SourceInstalledAppliedEssentialServiceRestorationAt depth installed
      installed.payload.disposition where
  applied_eq := rfl
  reform := SourceNativeBoundedInstitutionalReformAt.generate
    installed.operationalAuthority
  rootConsumer := installed.rootResponsibilityConsumer
  rootFactorization := installed.rootAnswerAndNext_factorizes

variable {depth : Nat}
variable {installed : SourceInstalledRenewalAt
  essentialServiceRestorationRecognition (temporalVisitAt depth)}
variable {applied : EssentialServiceRestorationDispositionAt
  installed.payload.sourceSeed}

def selectedWrite
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :=
  restoration.reform.residualRow

theorem selectedWrite_eq_installedSelectedRow
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :
    restoration.selectedWrite = installed.temporalSelectedRow :=
  rfl

theorem selectedWrite_commutes
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :
    restoration.selectedWrite.sourceRow.CommutesWithWorld :=
  restoration.reform.residualRow_commutes_with_wholeLedger

def wholeLedgerWriteBack
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :=
  restoration.reform.wholeLedgerWriteBack

def generatedNext
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :=
  restoration.reform.generatedNext

theorem generatedNext_eq_rootCompiler
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :
    restoration.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  restoration.reform.generatedNext_eq_rootCompiler

theorem lawSurface_preserved
    (restoration : SourceInstalledAppliedEssentialServiceRestorationAt
      depth installed applied) :
    restoration.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface :=
  restoration.reform.lawSurface_preserved

end SourceInstalledAppliedEssentialServiceRestorationAt

/-! ## Full actual restoration -/

structure SourceGeneratedProofCarryingEssentialServiceRestorationAt
    (depth : Nat) : Type 18 where
  private mk ::
  sourceDeath : SourceGeneratedPortfolioMaintenanceDeathAt depth
    (stablePortfolioSourceAt depth)
  installed : SourceInstalledRenewalAt
    essentialServiceRestorationRecognition (temporalVisitAt depth)
  seedExact : installed.payload.sourceSeed =
    M10OccurrenceCapacityProcessFixture.focalSeed
  consumerExact : installed.payload.consumer =
    sourceEssentialServiceMaintenanceRestriction
  actionExact : installed.payload.disposition =
    sourceGeneratedHealthServiceRestoration
  actionDomainExact :
    SourceAppliedEssentialServiceRestorationAt.domainAt
      installed.payload.disposition = healthDomainSeed
  actionUnitExact :
    SourceAppliedEssentialServiceRestorationAt.unitAt
      installed.payload.disposition = healthServiceUnit
  actionRequiredCutExact :
    SourceAppliedEssentialServiceRestorationAt.requiredCut
      installed.payload.disposition = 2
  sourceHealthUnitMissing :
    healthServiceUnit ∉ maintenanceSourceUnits
  sourceUnitsExact :
    maintenanceSourceUnits = (stablePrefixAt depth).units
  rootOccurrence : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot (temporalVisitAt depth)
  rootOccurrenceExact : rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  sourceDeathRootExact :
    sourceDeath.stable.paymentOccurrence.rootOccurrence = rootOccurrence
  sourceDeathHealthEmpty : IsEmpty
    (SourceGeneratedStableDomainServiceIncidenceAt depth
      (exactEssentialAccessSeed .health))
  sourceDeathPortfolioEmpty : IsEmpty
    (CompletePortfolioAt depth (stablePortfolioSourceAt depth))
  sourceDeathCapacityExact :
    (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  sourceEntryExact : installed.payload.sourceEntry =
    RootInquiryU8CompletionRegression.entry
  selectedRowSharedWithUBI :
    HEq installed.payload.selectedRow
      (installedUBIAt depth).payload.selectedRow
  successorSharedWithUBI :
    HEq installed.payload.successor
      (installedUBIAt depth).payload.successor
  applied : SourceInstalledAppliedEssentialServiceRestorationAt
    depth installed installed.payload.disposition
  selectedWriteCommutes : applied.selectedWrite.sourceRow.CommutesWithWorld
  wholeLedgerExact : applied.wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (temporalVisitAt depth)).wholeLedgerWriteBack
  rootFactorization : installed.RootAnswerAndNextFactorizes
  generatedNextExact : applied.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  lawSurfacePreserved : applied.generatedNext.root.source.lawSurface =
    jointRoot.source.base.lawSurface
  nextVisitExact : applied.generatedNext.visit = temporalVisitAt (depth + 1)
  targetPortfolio : SourceGeneratedActionableFuturePortfolioAt (depth + 1)
  targetPortfolioExact : targetPortfolio =
    sourceGeneratedActionableFuturePortfolioAt (depth + 1)
  targetHealth : SourceGeneratedEssentialDomainActionableAt
    (depth + 1) healthAuthority
  targetHealthServesActionUnit :
    (anomiePhaseAt (depth + 1)).served.get
        targetHealth.serviceIncidence.slot =
      SourceAppliedEssentialServiceRestorationAt.unitAt
        installed.payload.disposition
  targetCapacityExact :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  serviceProjectionDistinctFromUBI :
    jointEssentialServiceRestorationProjection ≠ jointUBIProjection
  serviceProjectionDistinctFromInquiry :
    jointEssentialServiceRestorationProjection ≠ jointInquiryProjection
  serviceProjectionDistinctFromFailure :
    jointEssentialServiceRestorationProjection ≠ jointFailureProjection
  serviceProjectionDistinctFromExisting :
    jointEssentialServiceRestorationProjection ≠ jointMandateProjection ∧
      jointEssentialServiceRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointEssentialServiceRestorationProjection ≠ jointUBIProjection ∧
      jointEssentialServiceRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointEssentialServiceRestorationProjection ≠ jointInquiryProjection ∧
      jointEssentialServiceRestorationProjection ≠ jointFailureProjection
  ubiDispositionPreserved :
    (installedUBIAt depth).payload.disposition =
      sourceGeneratedUBIDisposition

/-- Sole actual producer.  Every action, root, ledger, and target object is
read from the installed service coordinate at the generated temporal visit. -/
def sourceGeneratedEssentialServiceRestorationAt (depth : Nat) :
    SourceGeneratedProofCarryingEssentialServiceRestorationAt depth :=
  let installed := installedEssentialServiceRestorationAt depth
  let sourceDeath := portfolioMaintenanceDeathAt depth
  let applied :=
    SourceInstalledAppliedEssentialServiceRestorationAt.generate depth installed
  let targetPortfolio :=
    sourceGeneratedActionableFuturePortfolioAt (depth + 1)
  let targetHealth := targetPortfolio.actionable healthAuthority
  { sourceDeath := sourceDeath
    installed := installed
    seedExact := rfl
    consumerExact := rfl
    actionExact := rfl
    actionDomainExact := rfl
    actionUnitExact := rfl
    actionRequiredCutExact := rfl
    sourceHealthUnitMissing :=
      installed.payload.consumer.healthUnitMissing
    sourceUnitsExact := rfl
    rootOccurrence :=
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth)
    rootOccurrenceExact := rfl
    sourceDeathRootExact :=
      sourceDeath.paymentRootExact
    sourceDeathHealthEmpty := sourceDeath.healthServiceEmpty
    sourceDeathPortfolioEmpty := sourceDeath.completePortfolioEmpty
    sourceDeathCapacityExact := sourceDeath.exactCapacity
    sourceEntryExact := rfl
    selectedRowSharedWithUBI := HEq.rfl
    successorSharedWithUBI := HEq.rfl
    applied := applied
    selectedWriteCommutes := applied.selectedWrite_commutes
    wholeLedgerExact := rfl
    rootFactorization := applied.rootFactorization
    generatedNextExact := applied.generatedNext_eq_rootCompiler
    lawSurfacePreserved := applied.lawSurface_preserved
    nextVisitExact := rfl
    targetPortfolio := targetPortfolio
    targetPortfolioExact := rfl
    targetHealth := targetHealth
    targetHealthServesActionUnit :=
      targetHealth.serviceIncidence.servicedUnit_eq
    targetCapacityExact := actionableExitCapacity_eq_one_at (depth + 1)
    serviceProjectionDistinctFromUBI :=
      essentialService_projection_ne_ubi_projection
    serviceProjectionDistinctFromInquiry :=
      essentialService_projection_ne_inquiry_projection
    serviceProjectionDistinctFromFailure :=
      essentialService_projection_ne_failure_projection
    serviceProjectionDistinctFromExisting :=
      essentialService_projection_distinct_from_existing_coordinates
    ubiDispositionPreserved := rfl }

theorem every_generated_period_has_actual_service_restoration
    (depth : Nat) :
    Nonempty (SourceGeneratedProofCarryingEssentialServiceRestorationAt depth) :=
  ⟨sourceGeneratedEssentialServiceRestorationAt depth⟩

/-! ## No completed future or U8 mouth -/

theorem actual_service_restoration_mouth_has_no_forecast_or_u8_fields
    (depth : Nat) : True := by
  let restoration := sourceGeneratedEssentialServiceRestorationAt depth
  fail_if_success exact restoration.completedSchedule
  fail_if_success exact restoration.targetPrefix
  fail_if_success exact restoration.captureRepair
  fail_if_success exact restoration.audit
  fail_if_success exact restoration.u8Gate
  fail_if_success exact restoration.firstWrite
  trivial

end
end M14PeriodicEssentialServiceRestoration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicEssentialServiceRestoration.sourceGeneratedEssentialServiceRestorationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicEssentialServiceRestoration.every_generated_period_has_actual_service_restoration

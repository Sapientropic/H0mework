import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Policy.UBIPolicyBreakingOccurrence
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalRevision

/-!
# M14 actual proof-carrying exit-repair renewal

The exact repair compiler is a type index of the UBI restriction installed
before the fixed root emits.  At each generated temporal visit an exact
source failure can therefore apply that installed compiler, produce its
proof-carrying repair, and consume the same root occurrence, selected row,
whole-ledger write-back, responsibility consumer, and generated next.

This is the ordinary-repair branch: it uses the existing renewal
answer-and-next.  A `CanonicalFirstRootWriteAt` belongs only to a U8 change of
law language and is neither borrowed nor fabricated here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingExitRepairRenewalRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Revision UBI Capacity Policy
open M9ProofCarryingRenewalInquiryRoot
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EmploymentOutsideOptionGeometryRegression
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14UBIPolicyBreakingOccurrence

/-- Same-row ordinary reform whose applied repair disposition is literally
the disposition of the installed UBI payload.  The producer accepts neither
an action nor a row/next candidate. -/
structure SourceInstalledAppliedTenureRepairReformAt
    (depth : Nat)
    (installed : SourceInstalledRenewalAt ubiRecognition
      (temporalVisitAt depth))
    (applied : UBIDispositionAt installed.payload.sourceSeed) : Type 3 where
  private mk ::
  applied_eq : applied = installed.payload.disposition
  reform : SourceNativeBoundedInstitutionalReformAt
    installed.operationalAuthority
  rootConsumer : RenewalResponsibilityConsumerAt
    installed.operationalAuthority
  rootFactorization : installed.RootAnswerAndNextFactorizes

namespace SourceInstalledAppliedTenureRepairReformAt

def generate (depth : Nat)
    (installed : SourceInstalledRenewalAt ubiRecognition
      (temporalVisitAt depth)) :
    SourceInstalledAppliedTenureRepairReformAt depth installed
      installed.payload.disposition where
  applied_eq := rfl
  reform := SourceNativeBoundedInstitutionalReformAt.generate
    installed.operationalAuthority
  rootConsumer := installed.rootResponsibilityConsumer
  rootFactorization := installed.rootAnswerAndNext_factorizes

end SourceInstalledAppliedTenureRepairReformAt

/-- One actual temporal policy-renewal occurrence.  Its repair is an index,
not a stored suggestion.  The private producer accepts only the exact source
origin and reconstructs every authority object from the installed UBI
coordinate at that depth. -/
structure SourceInstalledProofCarryingExitRepairRenewalAt
    (depth : Nat) (repair : ExactExitRepair) : Type 3 where
  private mk ::
  source : PeriodicUBISourceAt depth
  rootOccurrence : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot (temporalVisitAt depth)
  rootOccurrence_eq : rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  repairProof : SourceGeneratedProofCarryingExitRepairAt
    (tenureCaptureOriginAt depth) repair
  appliedReform : SourceInstalledAppliedTenureRepairReformAt depth
    source.installed source.installed.payload.disposition

namespace SourceInstalledProofCarryingExitRepairRenewalAt

/-- Sole actual-renewal producer.  The tenure-capture origin is read from the
pre-emitter UBI restriction at this depth.  Capacity, effectiveness, a repair
choice, row, write-back, and next current are absent from the mouth. -/
def generate (depth : Nat) :
    SourceInstalledProofCarryingExitRepairRenewalAt depth
      (canonicalRepairAt (tenureCaptureOriginAt depth)) :=
  let source := periodicUBISourceAt depth
  { source := source
    rootOccurrence := (periodicSourceBackedPaymentAt depth).rootOccurrence
    rootOccurrence_eq := (tenureCaptureOriginAt depth).exactTemporalPayment
    repairProof := SourceGeneratedProofCarryingExitRepairAt.generate
      (tenureCaptureOriginAt depth)
    appliedReform :=
      SourceInstalledAppliedTenureRepairReformAt.generate
        depth source.installed }

variable {depth : Nat}
variable {repair : ExactExitRepair}

/-- The applied repair is computed by the exact compiler in this occurrence's
installed UBI restriction. -/
theorem repair_eq_installedCompiler
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    repair = renewal.source.installed.payload.consumer.repairAt
      (tenureCaptureOriginAt depth).failureKind := by
  exact renewal.repairProof.repair_eq

/-- The proof-carried repair is the action already present in the root
payload disposition, not a post-emission suggestion. -/
theorem repair_eq_appliedDisposition
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    repair = renewal.source.installed.payload.disposition.repairAt := by
  exact renewal.repairProof.repair_eq

theorem outcome_eq_one
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    repairOutcomeCapacityAt depth (tenureCaptureOriginAt depth) repair = 1 := by
  rw [renewal.repairProof.repair_eq]
  exact canonical_repair_outcome_eq_one (tenureCaptureOriginAt depth)

theorem effective_unique
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair)
    (candidate : ExactExitRepair) :
    EffectiveRepairAt depth (tenureCaptureOriginAt depth) candidate ↔
      candidate = repair := by
  rw [renewal.repairProof.repair_eq]
  exact effective_repair_iff_eq_canonical
    (tenureCaptureOriginAt depth) candidate

theorem repair_eq_removeCapture
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    repair = .removeCapture := by
  exact renewal.repairProof.repair_eq

/-- The route repair cannot inhabit this UBI-tenure renewal coordinate.  This
does not classify the independent route-restoration coordinate. -/
theorem restoreRoute_is_not_actual_in_tenure_coordinate (depth : Nat) :
    IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
      depth .restoreRoute) :=
  ⟨fun renewal => by
    have impossible := repair_eq_removeCapture renewal
    cases impossible⟩

/-- Ordinary selected write of the exact bounded reform. -/
def ordinarySelectedWrite
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :=
  renewal.appliedReform.reform.residualRow

@[simp] theorem ordinarySelectedWrite_eq_installedSelectedRow
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
  renewal.ordinarySelectedWrite =
      renewal.source.installed.temporalSelectedRow :=
  rfl

theorem ordinarySelectedWrite_commutes
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld :=
  renewal.appliedReform.reform.residualRow_commutes_with_wholeLedger

/-- Same-row evolution and debt lineage are generated by the installed
operational residual, not supplied by the policy consumer. -/
def rowEvolution
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :=
  renewal.appliedReform.reform.rowEvolution

def debtLineage
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :=
  renewal.appliedReform.reform.debtLineage

/-- Exact existing whole-ledger write-back consumed by this reform. -/
def wholeLedgerWriteBack
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :=
  renewal.appliedReform.reform.wholeLedgerWriteBack

/-- Generated next of the ordinary bounded reform. -/
def generatedNext
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :=
  renewal.appliedReform.reform.generatedNext

theorem generatedNext_eq_rootCompiler
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    renewal.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  renewal.appliedReform.reform.generatedNext_eq_rootCompiler

theorem lawSurface_preserved
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    renewal.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface :=
  renewal.appliedReform.reform.lawSurface_preserved

/-- The ordinary next visit consumes the repaired target program carried by
the action-bearing disposition; its exact actual-service geometry computes
capacity one. -/
theorem generatedNext_repairedFace_capacity_eq_one
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    renewal.generatedNext.visit = temporalVisitAt (depth + 1) ∧
      (installedUBIAt (depth + 1)).payload.consumer.programAt =
        renewal.source.installed.payload.disposition.targetProgramAt ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 := by
  exact ⟨rfl, rfl, actionableExitCapacity_eq_one_at (depth + 1)⟩

/-- The installed UBI projection outcome is the active source payload at this
same temporal occurrence. -/
theorem componentOutcome_eq_activePayload
    (renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth repair) :
    ubiRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨renewal.source.installed.active,
        renewal.source.installed.payload⟩ :
        SourceNativeProjectionFiberAt ubiRecognition.law.toProjectionLaw
          PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current)) :=
  renewal.source.installed.componentOutcome_eq_activePayload

end SourceInstalledProofCarryingExitRepairRenewalAt

/-- Distinguished actual tenure-policy event.  Unlike the independently
installed route face, the depth-zero tenure-capture origin is also the
existing source-generated policy breaking occurrence.  The bounded reform
stays on the same law surface and does not borrow the U8 first write. -/
structure DepthZeroActualProofCarryingExitRepairReform : Type 3 where
  private mk ::
  breaking : UBIPolicyBreakingOccurrenceAt
    (M14UBIPolicyBreakingOccurrence.Root.emitted jointVisit.current)
  renewal : SourceInstalledProofCarryingExitRepairRenewalAt 0
    (canonicalRepairAt (tenureCaptureOriginAt 0))
  sameOccurrence :
    (⟨jointVisit.current,
      M14UBIPolicyBreakingOccurrence.Root.emitted jointVisit.current⟩ :
      Sigma M14UBIPolicyBreakingOccurrence.Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
    ⟨(temporalVisitAt 0).current, renewal.rootOccurrence.occurrence⟩

def depthZeroActualProofCarryingExitRepairReform :
    DepthZeroActualProofCarryingExitRepairReform where
  breaking := active
  renewal := SourceInstalledProofCarryingExitRepairRenewalAt.generate 0
  sameOccurrence := rfl

theorem depth_zero_actual_capture_reform_commutes :
    (capturedGeometryCompilerAt 0).actionableExitCapacity = 0 ∧
      repairOutcomeCapacityAt 0 (tenureCaptureOriginAt 0)
        (canonicalRepairAt (tenureCaptureOriginAt 0)) = 1 ∧
      depthZeroActualProofCarryingExitRepairReform.renewal.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt 0) ∧
      depthZeroActualProofCarryingExitRepairReform.renewal.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface :=
  ⟨depthZeroActualProofCarryingExitRepairReform.breaking.capturedCapacity,
    depthZeroActualProofCarryingExitRepairReform.renewal.outcome_eq_one,
    depthZeroActualProofCarryingExitRepairReform.renewal
      |>.generatedNext_eq_rootCompiler,
    depthZeroActualProofCarryingExitRepairReform.renewal
      |>.lawSurface_preserved⟩

/-- Independent pointwise consumer for the one actual source cause of this
fixed root.  The installed compiler, effective repair, actual occurrence,
responsibility consumer, whole-ledger write-back, and generated next commute
without a second root. -/
structure ProofCarryingExitRepairRenewalConsumerAt
    (depth : Nat) : Type 3 where
  private mk ::
  renewal : SourceInstalledProofCarryingExitRepairRenewalAt depth
    (canonicalRepairAt (tenureCaptureOriginAt depth))
  repairFromInstalledCompiler :
    canonicalRepairAt (tenureCaptureOriginAt depth) =
      renewal.source.installed.payload.consumer.repairAt
        (tenureCaptureOriginAt depth).failureKind
  repairFromAppliedDisposition :
    canonicalRepairAt (tenureCaptureOriginAt depth) =
      renewal.source.installed.payload.disposition.repairAt
  appliedDispositionExact :
    renewal.source.installed.payload.disposition =
      sourceGeneratedUBIDisposition
  outcomeExact : repairOutcomeCapacityAt depth
    (tenureCaptureOriginAt depth)
      (canonicalRepairAt (tenureCaptureOriginAt depth)) = 1
  uniqueEffective : ∀ candidate : ExactExitRepair,
    EffectiveRepairAt depth (tenureCaptureOriginAt depth) candidate ↔
      candidate = canonicalRepairAt (tenureCaptureOriginAt depth)
  rootOccurrenceExact : renewal.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  componentOutcomeExact :
    ubiRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨renewal.source.installed.active,
        renewal.source.installed.payload⟩ :
        SourceNativeProjectionFiberAt ubiRecognition.law.toProjectionLaw
          PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current))
  selectedWriteExact : renewal.ordinarySelectedWrite =
    renewal.source.installed.temporalSelectedRow
  selectedWriteCommutes :
    renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld
  rootFactorization : renewal.source.installed.RootAnswerAndNextFactorizes
  generatedNextExact : renewal.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  lawSurfacePreserved : renewal.generatedNext.root.source.lawSurface =
    jointRoot.source.base.lawSurface
  nextRepairedFace :
    renewal.generatedNext.visit = temporalVisitAt (depth + 1) ∧
      (installedUBIAt (depth + 1)).payload.consumer.programAt =
        renewal.source.installed.payload.disposition.targetProgramAt ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1

def proofCarryingExitRepairRenewalConsumerAt (depth : Nat) :
    ProofCarryingExitRepairRenewalConsumerAt depth :=
  let renewal := SourceInstalledProofCarryingExitRepairRenewalAt.generate depth
  { renewal := renewal
    repairFromInstalledCompiler := renewal.repair_eq_installedCompiler
    repairFromAppliedDisposition := renewal.repair_eq_appliedDisposition
    appliedDispositionExact := renewal.source.exactDisposition
    outcomeExact :=
      SourceInstalledProofCarryingExitRepairRenewalAt.outcome_eq_one renewal
    uniqueEffective :=
      SourceInstalledProofCarryingExitRepairRenewalAt.effective_unique renewal
    rootOccurrenceExact := renewal.rootOccurrence_eq
    componentOutcomeExact := renewal.componentOutcome_eq_activePayload
    selectedWriteExact := renewal.ordinarySelectedWrite_eq_installedSelectedRow
    selectedWriteCommutes := renewal.ordinarySelectedWrite_commutes
    rootFactorization := renewal.appliedReform.rootFactorization
    generatedNextExact := renewal.generatedNext_eq_rootCompiler
    lawSurfacePreserved := renewal.lawSurface_preserved
    nextRepairedFace := renewal.generatedNext_repairedFace_capacity_eq_one }

theorem same_readout_generates_distinct_installed_repairs (depth : Nat) :
    failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) =
        failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) ∧
      Nonempty (ProofCarryingExitRepairRenewalConsumerAt depth) ∧
      SourceGeneratedProofCarryingExitRepairAt
        (routeBottleneckOriginAt depth)
        (canonicalRepairAt (routeBottleneckOriginAt depth)) ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) ≠
        canonicalRepairAt (routeBottleneckOriginAt depth) :=
  ⟨failure_readouts_equal depth,
    ⟨proofCarryingExitRepairRenewalConsumerAt depth⟩,
    SourceGeneratedProofCarryingExitRepairAt.generate
      (routeBottleneckOriginAt depth),
    exact_causes_generate_different_repairs depth⟩

/-- No completed temporal repair table enters the final sink. -/
structure ProofCarryingExitRepairRenewalCertificate : Prop where
  depthZeroBreakingReform :
    Nonempty DepthZeroActualProofCarryingExitRepairReform
  depthZeroCaptureReformCommutes :
    (capturedGeometryCompilerAt 0).actionableExitCapacity = 0 ∧
      repairOutcomeCapacityAt 0 (tenureCaptureOriginAt 0)
        (canonicalRepairAt (tenureCaptureOriginAt 0)) = 1
  everyDepthActualTenureCapture : ∀ depth : Nat,
    Nonempty (ProofCarryingExitRepairRenewalConsumerAt depth)
  everyDepthSameRootFactorization : ∀ depth : Nat,
    (proofCarryingExitRepairRenewalConsumerAt depth).renewal.source.installed
      |>.RootAnswerAndNextFactorizes
  everyDepthExactOutcome : ∀ depth : Nat,
    repairOutcomeCapacityAt depth (tenureCaptureOriginAt depth)
      (canonicalRepairAt (tenureCaptureOriginAt depth)) = 1
  everyDepthWrongRepairImpossible : ∀ depth : Nat,
    IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
      depth .restoreRoute)
  everyDepthNextRepairedFace : ∀ depth : Nat,
    let renewal :=
      (proofCarryingExitRepairRenewalConsumerAt depth).renewal
    renewal.generatedNext.visit = temporalVisitAt (depth + 1) ∧
      (installedUBIAt (depth + 1)).payload.consumer.programAt =
        renewal.source.installed.payload.disposition.targetProgramAt ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  everyDepthRouteRepairSourceGenerated : ∀ depth : Nat,
    SourceGeneratedProofCarryingExitRepairAt
      (routeBottleneckOriginAt depth)
      (canonicalRepairAt (routeBottleneckOriginAt depth))
  everyDepthNoCapacityReconstruction : ∀ depth : Nat,
    ¬ ∃ reconstruct : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt depth,
        reconstruct (failureCapacityReadoutAt depth origin) =
          canonicalRepairAt origin

theorem proofCarryingExitRepairRenewalDirectConsumer :
    ProofCarryingExitRepairRenewalCertificate where
  depthZeroBreakingReform :=
    ⟨depthZeroActualProofCarryingExitRepairReform⟩
  depthZeroCaptureReformCommutes :=
    ⟨depth_zero_actual_capture_reform_commutes.1,
      depth_zero_actual_capture_reform_commutes.2.1⟩
  everyDepthActualTenureCapture := fun depth =>
    ⟨proofCarryingExitRepairRenewalConsumerAt depth⟩
  everyDepthSameRootFactorization := fun depth =>
    (proofCarryingExitRepairRenewalConsumerAt depth).rootFactorization
  everyDepthExactOutcome := fun depth =>
    (proofCarryingExitRepairRenewalConsumerAt depth).outcomeExact
  everyDepthWrongRepairImpossible :=
    SourceInstalledProofCarryingExitRepairRenewalAt.restoreRoute_is_not_actual_in_tenure_coordinate
  everyDepthNextRepairedFace := fun depth =>
    (proofCarryingExitRepairRenewalConsumerAt depth).nextRepairedFace
  everyDepthRouteRepairSourceGenerated := fun depth =>
    SourceGeneratedProofCarryingExitRepairAt.generate
      (routeBottleneckOriginAt depth)
  everyDepthNoCapacityReconstruction :=
    no_capacity_only_canonical_repair_reconstruction

end
end M14ProofCarryingExitRepairRenewalRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRenewalRegression.SourceInstalledProofCarryingExitRepairRenewalAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRenewalRegression.SourceInstalledProofCarryingExitRepairRenewalAt.componentOutcome_eq_activePayload
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRenewalRegression.SourceInstalledProofCarryingExitRepairRenewalAt.generatedNext_repairedFace_capacity_eq_one
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRenewalRegression.depth_zero_actual_capture_reform_commutes
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingExitRepairRenewalRegression.proofCarryingExitRepairRenewalDirectConsumer

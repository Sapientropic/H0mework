import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Trace.FiniteActualRepairFailureTrace
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Identification.FullDomainRepairAuthorityObstruction

/-!
# M14 direct consumer for common actual support and paired trace

The common dependent face admits both tenure capture and route bottleneck at
every generated temporal depth.  The canonical pair shares one root
occurrence, source entry, whole-ledger write-back, and generated next while
retaining distinct projection and repair authority.

The requested trace contains both branches.  Bare roots intentionally collide
at equal depth; branchwise root traces and the full failure-kind-stamped root
trace are duplicate-free.  This is the positive support required before a
failure-face measure can be constructed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActualRepairFailureTraceRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy Observer
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14ProofCarryingPeriodicRouteRestoration
open M14ActualRepairFailureOccurrence
open M14FiniteActualRepairFailureTrace
open M14FullDomainRepairAuthorityObstruction

theorem actualRepairFailurePointwiseAt (depth : Nat) :
    Nonempty (ActualRepairFailureAt depth
        (tenureCaptureOriginAt depth)) ∧
      Nonempty (ActualRepairFailureAt depth
        (routeBottleneckOriginAt depth)) ∧
      actualRepairSupportAt depth = Set.univ ∧
      (let tenure := sourceGeneratedActualTenureRepairFailureAt depth
       let route := sourceGeneratedActualRouteRepairFailureAt depth
       tenure.rootOccurrence = route.rootOccurrence ∧
         HEq tenure.sourceEntry route.sourceEntry ∧
         ActualRepairFailureAt.SourceConsumerExactAt
           (tenureCaptureOriginAt depth) tenure ∧
         ActualRepairFailureAt.SourceConsumerExactAt
           (routeBottleneckOriginAt depth) route ∧
         ActualRepairFailureAt.InstalledActionExactAt
           (tenureCaptureOriginAt depth) tenure ∧
         ActualRepairFailureAt.InstalledActionExactAt
           (routeBottleneckOriginAt depth) route ∧
         HEq tenure.wholeLedgerWriteBack route.wholeLedgerWriteBack ∧
         tenure.generatedNext = route.generatedNext ∧
         tenure.projection ≠ route.projection ∧
         tenure.repair ≠ route.repair) ∧
      IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
        depth .removeCapture) :=
  ⟨⟨sourceGeneratedActualTenureRepairFailureAt depth⟩,
    ⟨sourceGeneratedActualRouteRepairFailureAt depth⟩,
    actualRepairSupport_eq_univ depth,
    canonical_actual_pair_shared_root_distinct_authority depth,
    canonical_cross_retypes_are_empty depth |>.1,
    canonical_cross_retypes_are_empty depth |>.2⟩

theorem fullDomainRepairKernelPair_jointly_actual (depth : Nat) :
    Nonempty
      (ActualRepairFailureAt depth
          (fullDomainRepairKernelPairAt depth).left ×
        ActualRepairFailureAt depth
          (fullDomainRepairKernelPairAt depth).right) := by
  change Nonempty
    (ActualRepairFailureAt depth (tenureCaptureOriginAt depth) ×
      ActualRepairFailureAt depth (routeBottleneckOriginAt depth))
  exact ⟨(sourceGeneratedActualTenureRepairFailureAt depth,
    sourceGeneratedActualRouteRepairFailureAt depth)⟩

theorem fullDomainRepairKernelPair_mem_actualSupport (depth : Nat) :
    (fullDomainRepairKernelPairAt depth).left ∈
        actualRepairSupportAt depth ∧
      (fullDomainRepairKernelPairAt depth).right ∈
        actualRepairSupportAt depth := by
  rw [actualRepairSupport_eq_univ]
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem finiteActualRepairFailureTraceAt (horizon : Nat) :
    (sourceGeneratedFiniteActualRepairFailureTrace horizon).length =
        2 * horizon ∧
      (∀ depth : Nat,
        tenureRepairFailureOccurrenceAt depth ∈
            sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
          depth < horizon) ∧
      (∀ depth : Nat,
        routeRepairFailureOccurrenceAt depth ∈
            sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
          depth < horizon) ∧
      (sourceGeneratedFiniteActualRepairFailureTrace horizon).Nodup ∧
      (finiteActualTenureRepairFailureRootTrace horizon).Nodup ∧
      (finiteActualRouteRepairFailureRootTrace horizon).Nodup ∧
      (finiteActualRepairFailureStampedRootTrace horizon).Nodup ∧
      (0 < horizon →
        ¬ (finiteActualRepairFailureBareRootTrace horizon).Nodup) ∧
      (∀ depth : Nat,
        (tenureRepairFailureOccurrenceAt depth).erasedRootOccurrence =
          (routeRepairFailureOccurrenceAt depth).erasedRootOccurrence) ∧
      (∀ occurrence : AnyActualRepairFailure,
        occurrence ∈ sourceGeneratedFiniteActualRepairFailureTrace horizon →
          occurrence.depth < horizon ∧
          (occurrence.failureKind = ExactExitFailureKind.tenureCapture ∨
            occurrence.failureKind = ExactExitFailureKind.routeBottleneck) ∧
          occurrence.actual.rootOccurrence =
            jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
              (temporalVisitAt occurrence.depth) ∧
          ActualRepairFailureAt.SourceConsumerExactAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.InstalledActionExactAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.SelectedWriteCommutesAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.RootFactorizesAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.ComponentOutcomeExactAt occurrence.origin
            occurrence.actual ∧
          HEq occurrence.actual.wholeLedgerWriteBack
            (jointRoot.toAuthoritativeRoot.toLedgerRoot
              |>.generatedAtTemporalVisit
                (temporalVisitAt occurrence.depth)).wholeLedgerWriteBack ∧
          occurrence.actual.generatedNext =
            jointRoot.generatedNextCurrentAt
              (temporalVisitAt occurrence.depth)) :=
  ⟨finiteActualRepairFailureTrace_length horizon,
    fun _depth => tenureOccurrence_mem_pairedTrace_iff,
    fun _depth => routeOccurrence_mem_pairedTrace_iff,
    finiteActualRepairFailureTrace_nodup horizon,
    finiteActualTenureRepairFailureRootTrace_nodup horizon,
    finiteActualRouteRepairFailureRootTrace_nodup horizon,
    finiteActualRepairFailureStampedRootTrace_nodup horizon,
    finiteActualRepairFailureBareRootTrace_not_nodup,
    sameDepth_tenure_route_rootOccurrence_equal,
    fun _occurrence membership =>
      finiteActualRepairFailureTrace_member_exact membership⟩

structure ProofCarryingActualRepairFailureTraceCertificate : Prop where
  pointwise : ∀ depth : Nat,
    Nonempty (ActualRepairFailureAt depth
        (tenureCaptureOriginAt depth)) ∧
      Nonempty (ActualRepairFailureAt depth
        (routeBottleneckOriginAt depth)) ∧
      actualRepairSupportAt depth = Set.univ ∧
      (let tenure := sourceGeneratedActualTenureRepairFailureAt depth
       let route := sourceGeneratedActualRouteRepairFailureAt depth
       tenure.rootOccurrence = route.rootOccurrence ∧
         HEq tenure.sourceEntry route.sourceEntry ∧
         ActualRepairFailureAt.SourceConsumerExactAt
           (tenureCaptureOriginAt depth) tenure ∧
         ActualRepairFailureAt.SourceConsumerExactAt
           (routeBottleneckOriginAt depth) route ∧
         ActualRepairFailureAt.InstalledActionExactAt
           (tenureCaptureOriginAt depth) tenure ∧
         ActualRepairFailureAt.InstalledActionExactAt
           (routeBottleneckOriginAt depth) route ∧
         HEq tenure.wholeLedgerWriteBack route.wholeLedgerWriteBack ∧
         tenure.generatedNext = route.generatedNext ∧
         tenure.projection ≠ route.projection ∧
         tenure.repair ≠ route.repair) ∧
      IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
        depth .removeCapture)
  kernelJointlyActual : ∀ depth : Nat,
    Nonempty
      (ActualRepairFailureAt depth
          (fullDomainRepairKernelPairAt depth).left ×
        ActualRepairFailureAt depth
          (fullDomainRepairKernelPairAt depth).right)
  kernelInActualSupport : ∀ depth : Nat,
    (fullDomainRepairKernelPairAt depth).left ∈
        actualRepairSupportAt depth ∧
      (fullDomainRepairKernelPairAt depth).right ∈
        actualRepairSupportAt depth
  everyFiniteTrace : ∀ horizon : Nat,
    (sourceGeneratedFiniteActualRepairFailureTrace horizon).length =
        2 * horizon ∧
      (∀ depth : Nat,
        tenureRepairFailureOccurrenceAt depth ∈
            sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
          depth < horizon) ∧
      (∀ depth : Nat,
        routeRepairFailureOccurrenceAt depth ∈
            sourceGeneratedFiniteActualRepairFailureTrace horizon ↔
          depth < horizon) ∧
      (sourceGeneratedFiniteActualRepairFailureTrace horizon).Nodup ∧
      (finiteActualTenureRepairFailureRootTrace horizon).Nodup ∧
      (finiteActualRouteRepairFailureRootTrace horizon).Nodup ∧
      (finiteActualRepairFailureStampedRootTrace horizon).Nodup ∧
      (0 < horizon →
        ¬ (finiteActualRepairFailureBareRootTrace horizon).Nodup) ∧
      (∀ depth : Nat,
        (tenureRepairFailureOccurrenceAt depth).erasedRootOccurrence =
          (routeRepairFailureOccurrenceAt depth).erasedRootOccurrence) ∧
      (∀ occurrence : AnyActualRepairFailure,
        occurrence ∈ sourceGeneratedFiniteActualRepairFailureTrace horizon →
          occurrence.depth < horizon ∧
          (occurrence.failureKind = ExactExitFailureKind.tenureCapture ∨
            occurrence.failureKind = ExactExitFailureKind.routeBottleneck) ∧
          occurrence.actual.rootOccurrence =
            jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
              (temporalVisitAt occurrence.depth) ∧
          ActualRepairFailureAt.SourceConsumerExactAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.InstalledActionExactAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.SelectedWriteCommutesAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.RootFactorizesAt occurrence.origin
            occurrence.actual ∧
          ActualRepairFailureAt.ComponentOutcomeExactAt occurrence.origin
            occurrence.actual ∧
          HEq occurrence.actual.wholeLedgerWriteBack
            (jointRoot.toAuthoritativeRoot.toLedgerRoot
              |>.generatedAtTemporalVisit
                (temporalVisitAt occurrence.depth)).wholeLedgerWriteBack ∧
          occurrence.actual.generatedNext =
            jointRoot.generatedNextCurrentAt
              (temporalVisitAt occurrence.depth))

theorem proofCarryingActualRepairFailureTraceDirectConsumer :
    ProofCarryingActualRepairFailureTraceCertificate where
  pointwise := actualRepairFailurePointwiseAt
  kernelJointlyActual := fullDomainRepairKernelPair_jointly_actual
  kernelInActualSupport := fullDomainRepairKernelPair_mem_actualSupport
  everyFiniteTrace := finiteActualRepairFailureTraceAt

end
end M14ProofCarryingActualRepairFailureTraceRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureTraceRegression.actualRepairFailurePointwiseAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureTraceRegression.fullDomainRepairKernelPair_jointly_actual
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureTraceRegression.finiteActualRepairFailureTraceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureTraceRegression.proofCarryingActualRepairFailureTraceDirectConsumer

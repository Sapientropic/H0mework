import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicRootHistory

/-!
# M14 actual-service UBI capacity at every generated period

Every finite root-history depth below regenerates the UBI installation,
occurrence queue, capacity phase, crossing law, actual two-debit service, and
canonical exit geometry at that exact temporal visit.  The source root stores
no `Nat → receipt`, capacity table, matching, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIPeriodicActualServiceCapacity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space CrossingCost UBI
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityDebitedRunFixture
open M11GeneratedSocialSpaceCrossingFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIProofCarryingRootCapacity
open M14UBIPeriodicRootHistory

/-- Reindex the existing recurrent compiler by the UBI payload generated at
this exact temporal depth. -/
def installedCompilerAt (depth : Nat) :
    SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
      M14UBIProofCarryingRootRestriction.LocalGame
      M14UBIProofCarryingRootRestriction.LocalSeed
      M14UBIProofCarryingRootRestriction.LocalSeedAt
      M10OccurrenceCapacityProcessFixture.Lineage
      M10OccurrenceCapacityProcessFixture.lineageOf
      (installedUBIAt depth).payload.sourceSeed :=
  M10OccurrenceCapacityProcessFixture.compiler

@[simp] theorem installedCompilerAt_queue_length (depth : Nat) :
    (installedCompilerAt depth).queue.length = 3 :=
  rfl

def anomiePrefixAt (depth : Nat) :
    SourceGeneratedExactQueuePrefixAt (installedCompilerAt depth) :=
  SourceGeneratedExactQueuePrefixAt.generate (installedCompilerAt depth)
    ⟨3, by rw [installedCompilerAt_queue_length]; decide⟩

def anomiePhaseAt (depth : Nat) :
    SourceGeneratedOccurrenceCapacityPhaseAt
      (installedUBIAt depth) (installedCompilerAt depth)
        (anomiePrefixAt depth) :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    (installedUBIAt depth) (installedCompilerAt depth)
      (anomiePrefixAt depth)

@[simp] theorem anomiePhaseAt_tag (depth : Nat) :
    (anomiePhaseAt depth).phaseTag = .anomie :=
  rfl

@[simp] theorem anomiePhaseAt_capacity (depth : Nat) :
    (anomiePhaseAt depth).capacity = 2 :=
  rfl

@[simp] theorem anomiePhaseAt_served_length (depth : Nat) :
    (anomiePhaseAt depth).served.length = 2 :=
  rfl

abbrev crossingCompilerAt (depth : Nat) :
    SourceOwnedCrossingCompiler (installedCompilerAt depth) :=
  M11GeneratedSocialSpaceCrossingFixture.crossingCompiler

/-- A periodic service receipt explicitly consumes the visit-indexed payment
occurrence before retaining one existing local maintenance receipt.  Thus the
local run shape may recur, but its service authority is carried by the exact
temporal root occurrence rather than by a bare `Nat` label. -/
structure PeriodicServiceReceiptAt
    (depth : Nat)
    (_paymentOccurrence : PeriodicSourceBackedPaymentAt depth)
    (unit : (installedCompilerAt depth).QueueUnit)
    (event : LifecycleEvent M10OccurrenceCapacityDebitedRunFixture.V) : Type where
  private mk ::
  localReceipt : M14UBIProofCarryingRootCapacity.ServiceReceiptAt unit event

def firstServiceReceiptAt (depth : Nat) :
    PeriodicServiceReceiptAt depth (periodicSourceBackedPaymentAt depth) firstUnit
      firstMaintenance.lifecycleEvent where
  localReceipt := M14UBIProofCarryingRootCapacity.ServiceReceiptAt.first

def middleServiceReceiptAt (depth : Nat) :
    PeriodicServiceReceiptAt depth (periodicSourceBackedPaymentAt depth) middleUnit
      secondMaintenance.lifecycleEvent where
  localReceipt := M14UBIProofCarryingRootCapacity.ServiceReceiptAt.middle

def serviceCompilerAt (depth : Nat) :
    SourceOwnedOccurrenceServiceCompiler
      (installedCompilerAt depth) M10OccurrenceCapacityDebitedRunFixture.P where
  ServesAt := PeriodicServiceReceiptAt depth
    (periodicSourceBackedPaymentAt depth)

def actualSettlementAt (depth : Nat) : ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth) where
  sourceBudget_eq_capacity := rfl
  eventsLength_eq_allocated := rfl
  serviceAt := by
    rintro ⟨index, index_lt⟩
    cases index with
    | zero => exact firstServiceReceiptAt depth
    | succ index =>
        cases index with
        | zero => exact middleServiceReceiptAt depth
        | succ index =>
            exact False.elim (by
              change Nat.succ (Nat.succ index) < 2 at index_lt
              omega)

def geometryCompilerAt (depth : Nat) : SourceOwnedExitGeometryCompilerAt
    exitCapacityProgram (anomiePhaseAt depth) (crossingCompilerAt depth)
      run (serviceCompilerAt depth) (actualSettlementAt depth) where
  PaysForAt := SourceBackedUBIPaymentReceiptAt
  RoutesAt := SourceGeneratedUBIRouteReceiptAt

def capturedGeometryCompilerAt (depth : Nat) :
    SourceOwnedExitGeometryCompilerAt
      capturedProgram (anomiePhaseAt depth) (crossingCompilerAt depth)
        run (serviceCompilerAt depth) (actualSettlementAt depth) where
  PaysForAt := SourceBackedUBIPaymentReceiptAt
  RoutesAt := SourceGeneratedUBIRouteReceiptAt

def firstSlotAt (depth : Nat) : Fin (anomiePhaseAt depth).served.length :=
  ⟨0, by rw [anomiePhaseAt_served_length]; decide⟩

def firstFeasibleExitAt (depth : Nat) :
    ExactFeasibleExitEdgeAt (geometryCompilerAt depth)
      ExitFutureCode.leave (firstSlotAt depth) :=
  FeasibleExitEdgeAt.generate
    (actualSettlement := actualSettlementAt depth)
    actionableExit.2 SourceBackedUBIPaymentReceiptAt.generate
      (SourceGeneratedUBIRouteReceiptAt.generate _)

def actionableExitRenewalAt (depth : Nat) :
    (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt where
  code := .leave
  slot := firstSlotAt depth
  feasible := firstFeasibleExitAt depth

theorem capacity_positive_at (depth : Nat) :
    0 < (geometryCompilerAt depth).actionableExitCapacity :=
  (geometryCompilerAt depth).capacity_positive_iff_actionableExitRenewal.mpr
    ⟨actionableExitRenewalAt depth⟩

theorem strongest_actual_exit_renewal_iff_at (depth : Nat) :
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ↔
      ∃ (code : exitRelationCompiler.FutureCode)
        (slot : Fin (anomiePhaseAt depth).served.length),
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code ∧
        Nonempty (SourceBackedUBIPaymentReceiptAt
          exitCapacityProgram.purchasingPowerStanding code) ∧
        Nonempty (SourceGeneratedUBIRouteReceiptAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := anomiePhaseAt depth)
            (crossingCompiler := crossingCompilerAt depth) slot)) :=
  (geometryCompilerAt depth).actionableExitRenewal_nonempty_iff_full_contract

theorem actionableExitCapacity_eq_one_at (depth : Nat) :
    (geometryCompilerAt depth).actionableExitCapacity = 1 := by
  have upper :=
    (geometryCompilerAt depth).capacity_le_surviving_actionable_codes
  rw [survivingCodes_card_eq_one] at upper
  have lower : 1 ≤ (geometryCompilerAt depth).actionableExitCapacity :=
    Nat.succ_le_iff.mpr (capacity_positive_at depth)
  exact Nat.le_antisymm upper lower

theorem captured_nominal_capacity_eq_zero_at (depth : Nat) :
    (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 :=
  (capturedGeometryCompilerAt depth).nominal_transfer_no_exit_capacity
    nominalTransfer

theorem capacity_bounded_by_actual_service_and_root_at (depth : Nat) :
    (geometryCompilerAt depth).actionableExitCapacity ≤
        (anomiePhaseAt depth).served.length ∧
      (geometryCompilerAt depth).actionableExitCapacity ≤
        (anomiePhaseAt depth).capacity :=
  ⟨(geometryCompilerAt depth).capacity_le_actual_served_slots,
    (geometryCompilerAt depth).capacity_le_rootOperationalCapacity⟩

theorem anomie_with_positive_exit_capacity_at (depth : Nat) :
    (anomiePhaseAt depth).phaseTag = .anomie ∧
      0 < (geometryCompilerAt depth).actionableExitCapacity ∧
      (anomiePhaseAt depth).backlog ≠ [] := by
  refine ⟨anomiePhaseAt_tag depth, capacity_positive_at depth, ?_⟩
  exact (anomiePhaseAt depth).anomie_backlog_ne_nil (anomiePhaseAt_tag depth)

/-- Complete arbitrary-depth consumer carrier.  It is generated on demand
from `temporalVisitAt depth`; no family of results is stored in the root. -/
structure PeriodicActualServiceExitAt (depth : Nat) : Type 16 where
  private mk ::
  paymentOccurrence : PeriodicSourceBackedPaymentAt depth
  paymentOccurrence_eq :
    paymentOccurrence = periodicSourceBackedPaymentAt depth
  paymentInstalled_eq : paymentOccurrence.installed = installedUBIAt depth
  actualSettlement : ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth)
  actualSettlement_eq : actualSettlement = actualSettlementAt depth
  feasibleEdge : ExactFeasibleExitEdgeAt (geometryCompilerAt depth)
    ExitFutureCode.leave (firstSlotAt depth)
  feasibleEdge_eq : feasibleEdge = firstFeasibleExitAt depth
  actionableRenewal :
    (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt
  actionableRenewal_eq : actionableRenewal = actionableExitRenewalAt depth
  exactCapacity : (geometryCompilerAt depth).actionableExitCapacity = 1
  capturedCapacity :
    (capturedGeometryCompilerAt depth).actionableExitCapacity = 0
  rootFactorization : paymentOccurrence.installed.RootAnswerAndNextFactorizes

def periodicActualServiceExitAt (depth : Nat) :
    PeriodicActualServiceExitAt depth where
  paymentOccurrence := periodicSourceBackedPaymentAt depth
  paymentOccurrence_eq := rfl
  paymentInstalled_eq := rfl
  actualSettlement := actualSettlementAt depth
  actualSettlement_eq := rfl
  feasibleEdge := firstFeasibleExitAt depth
  feasibleEdge_eq := rfl
  actionableRenewal := actionableExitRenewalAt depth
  actionableRenewal_eq := rfl
  exactCapacity := actionableExitCapacity_eq_one_at depth
  capturedCapacity := captured_nominal_capacity_eq_zero_at depth
  rootFactorization :=
    (periodicSourceBackedPaymentAt depth).rootFactorization

/-- The visit index fixes one canonical payment, settlement, feasible edge and
renewal.  Hence an exact periodic actual-service authority has no hidden
witness choice inside its fibre. -/
theorem periodicActualServiceExitAt_eq_canonical
    {depth : Nat} (actualExit : PeriodicActualServiceExitAt depth) :
    actualExit = periodicActualServiceExitAt depth := by
  rcases actualExit with
    ⟨paymentOccurrence, paymentOccurrence_eq, paymentInstalled_eq,
      actualSettlement, actualSettlement_eq, feasibleEdge, feasibleEdge_eq,
      actionableRenewal, actionableRenewal_eq, exactCapacity,
      capturedCapacity, rootFactorization⟩
  cases paymentOccurrence_eq
  cases actualSettlement_eq
  cases feasibleEdge_eq
  cases actionableRenewal_eq
  rfl

instance periodicActualServiceExitAtSubsingleton (depth : Nat) :
    Subsingleton (PeriodicActualServiceExitAt depth) where
  allEq left right :=
    (periodicActualServiceExitAt_eq_canonical left).trans
      (periodicActualServiceExitAt_eq_canonical right).symm

/-- Even when a low-universe root mouth can retain only existential
authority, selecting its underlying high-universe value recovers the unique
source-generated occurrence at that depth. -/
theorem periodicActualServiceExit_choice_eq_canonical
    {depth : Nat} (authority : Nonempty (PeriodicActualServiceExitAt depth)) :
    Classical.choice authority = periodicActualServiceExitAt depth :=
  periodicActualServiceExitAt_eq_canonical (Classical.choice authority)

/-- Actual-service authority indexed by the existing temporal visit. -/
structure ActualServiceExitAtVisit
    (visit : SourceNativeTemporalVisitAt
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot) :
    Type 16 where
  private mk ::
  depth : Nat
  visit_eq : visit = temporalVisitAt depth
  actualExit : PeriodicActualServiceExitAt depth

def actualServiceExitAtVisit (depth : Nat) :
    ActualServiceExitAtVisit (temporalVisitAt depth) where
  depth := depth
  visit_eq := rfl
  actualExit := periodicActualServiceExitAt depth

abbrev AnyPeriodicActualServiceExit :=
  Sigma ActualServiceExitAtVisit

def periodicActualServiceExitOccurrenceAt (depth : Nat) :
    AnyPeriodicActualServiceExit :=
  ⟨temporalVisitAt depth, actualServiceExitAtVisit depth⟩

def AnyPeriodicActualServiceExit.paymentOccurrence
    (actualExit : AnyPeriodicActualServiceExit) :
    AnySourceBackedPaymentOccurrence :=
  ⟨temporalVisitAt actualExit.2.depth,
    actualExit.2.actualExit.paymentOccurrence⟩

theorem AnyPeriodicActualServiceExit.paymentOccurrence_visit_eq
    (actualExit : AnyPeriodicActualServiceExit) :
    actualExit.paymentOccurrence.1 = actualExit.1 :=
  actualExit.2.visit_eq.symm

@[simp] theorem periodicActualServiceExit_paymentOccurrence (depth : Nat) :
    (periodicActualServiceExitOccurrenceAt depth).paymentOccurrence =
      periodicPaymentOccurrenceAt depth :=
  rfl

theorem periodicActualServiceExitOccurrenceAt_injective :
    Function.Injective periodicActualServiceExitOccurrenceAt := by
  intro left right equality
  have payment_eq := congrArg AnyPeriodicActualServiceExit.paymentOccurrence
    equality
  rw [periodicActualServiceExit_paymentOccurrence,
    periodicActualServiceExit_paymentOccurrence] at payment_eq
  exact periodicPaymentOccurrenceAt_injective payment_eq

theorem every_generated_period_has_actual_service_exit (depth : Nat) :
    Nonempty (PeriodicActualServiceExitAt depth) :=
  ⟨periodicActualServiceExitAt depth⟩

/-- Regression guard: the all-depth producer is downstream and does not add a
completed service/capacity family to the installed root restriction. -/
theorem root_payload_has_no_completed_periodic_service (_depth : Nat) : True := by
  fail_if_success
    exact (installedUBIAt _depth).payload.consumer.actualSettlement
  fail_if_success
    exact (installedUBIAt _depth).payload.consumer.actionableExitCapacity
  trivial

end
end M14UBIPeriodicActualServiceCapacity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPeriodicActualServiceCapacity.actionableExitCapacity_eq_one_at
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPeriodicActualServiceCapacity.periodicActualServiceExitAt_eq_canonical
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPeriodicActualServiceCapacity.periodicActualServiceExit_choice_eq_canonical
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPeriodicActualServiceCapacity.periodicActualServiceExitOccurrenceAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPeriodicActualServiceCapacity.every_generated_period_has_actual_service_exit

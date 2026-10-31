import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.ActionableExitCapacity
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityDebitedRun
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot

/-!
# M14 actionable UBI capacity on the M9/M13 root

The UBI coordinate, proof-carrying coordinate, inquiry, and failure are all
born in the literal M9/M13 authority inventory.  This file consumes the UBI
coordinate after emission.  A three-occurrence queue meets the common root
row's capacity two; two actual maintenance debits service the allocated
prefix; exact payment and route receipts then generate a canonical maximum
matching.  No sibling root, selected matching, or completed future appears.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIProofCarryingRootCapacity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space CrossingCost UBI
open UBI.Capacity
open UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityDebitedRunFixture
open M11GeneratedSocialSpaceCrossingFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M9ProofCarryingRenewalInquiryRoot

/-- The existing recurrent compiler reindexed by the exact UBI payload seed. -/
def installedCompiler : SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
    M14UBIProofCarryingRootRestriction.LocalGame
    M14UBIProofCarryingRootRestriction.LocalSeed
    M14UBIProofCarryingRootRestriction.LocalSeedAt
    M10OccurrenceCapacityProcessFixture.Lineage
    M10OccurrenceCapacityProcessFixture.lineageOf
    installedUBI.payload.sourceSeed :=
  M10OccurrenceCapacityProcessFixture.compiler

@[simp] theorem installedCompiler_queue_length :
    installedCompiler.queue.length = 3 :=
  rfl

def anomiePrefix : SourceGeneratedExactQueuePrefixAt installedCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate installedCompiler
    ⟨3, by rw [installedCompiler_queue_length]; decide⟩

def anomiePhase : SourceGeneratedOccurrenceCapacityPhaseAt
    installedUBI installedCompiler anomiePrefix :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    installedUBI installedCompiler anomiePrefix

@[simp] theorem anomiePhase_tag : anomiePhase.phaseTag = .anomie :=
  rfl

@[simp] theorem anomiePhase_capacity : anomiePhase.capacity = 2 :=
  rfl

@[simp] theorem anomiePhase_served_length : anomiePhase.served.length = 2 :=
  rfl

/-- The generated social-space compiler is the crossing law of this same
installed M10 occurrence seed. -/
abbrev crossingCompiler : SourceOwnedCrossingCompiler installedCompiler :=
  M11GeneratedSocialSpaceCrossingFixture.crossingCompiler

/-- Ordered service receipts tie the first two generated queue occurrences to
the two actual maintenance events. -/
inductive ServiceReceiptAt :
    installedCompiler.QueueUnit →
      LifecycleEvent M10OccurrenceCapacityDebitedRunFixture.V → Type
  | first : ServiceReceiptAt firstUnit firstMaintenance.lifecycleEvent
  | middle : ServiceReceiptAt middleUnit secondMaintenance.lifecycleEvent

def serviceCompiler : SourceOwnedOccurrenceServiceCompiler
    installedCompiler M10OccurrenceCapacityDebitedRunFixture.P where
  ServesAt := ServiceReceiptAt

/-- Exact actual settlement of the root-allocated prefix. -/
def actualSettlement : ExactServedCrossingDebitedRunAt
    anomiePhase debited serviceCompiler where
  sourceBudget_eq_capacity := rfl
  eventsLength_eq_allocated := rfl
  serviceAt := by
    rintro ⟨index, index_lt⟩
    cases index with
    | zero => exact ServiceReceiptAt.first
    | succ index =>
        cases index with
        | zero => exact ServiceReceiptAt.middle
        | succ index =>
            exact False.elim (by
              change Nat.succ (Nat.succ index) < 2 at index_lt
              omega)

/-- The geometry consumes exactly the payment and route families encoded in
the UBI root restriction's type indices. -/
def geometryCompiler : SourceOwnedExitGeometryCompilerAt
    exitCapacityProgram anomiePhase crossingCompiler run serviceCompiler
      actualSettlement where
  PaysForAt := SourceBackedUBIPaymentReceiptAt
  RoutesAt := SourceGeneratedUBIRouteReceiptAt

def capturedGeometryCompiler : SourceOwnedExitGeometryCompilerAt
    capturedProgram anomiePhase crossingCompiler run serviceCompiler
      actualSettlement where
  PaysForAt := SourceBackedUBIPaymentReceiptAt
  RoutesAt := SourceGeneratedUBIRouteReceiptAt

def firstSlot : Fin anomiePhase.served.length :=
  ⟨0, by decide⟩

def firstFeasibleExit : ExactFeasibleExitEdgeAt geometryCompiler
    ExitFutureCode.leave firstSlot :=
  FeasibleExitEdgeAt.generate
    (actualSettlement := actualSettlement)
    actionableExit.2 SourceBackedUBIPaymentReceiptAt.generate
      (SourceGeneratedUBIRouteReceiptAt.generate _)

def actionableExitRenewal :
    geometryCompiler.SourceGeneratedActionableExitRenewalAt where
  code := .leave
  slot := firstSlot
  feasible := firstFeasibleExit

theorem capacity_positive : 0 < geometryCompiler.actionableExitCapacity :=
  geometryCompiler.capacity_positive_iff_actionableExitRenewal.mpr
    ⟨actionableExitRenewal⟩

/-- Exact maximum theorem on the fixed source geometry: a generated UBI exit
exists iff one source-generated, non-idle, uncaptured continuation is backed
by the exact payment, route, and actual service occurrence. -/
theorem strongest_actual_exit_renewal_iff :
    Nonempty geometryCompiler.SourceGeneratedActionableExitRenewalAt ↔
      ∃ (code : exitRelationCompiler.FutureCode)
        (slot : Fin anomiePhase.served.length),
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code ∧
        Nonempty (SourceBackedUBIPaymentReceiptAt
          exitCapacityProgram.purchasingPowerStanding code) ∧
        Nonempty (SourceGeneratedUBIRouteReceiptAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := anomiePhase) (crossingCompiler := crossingCompiler)
            slot)) :=
  geometryCompiler.actionableExitRenewal_nonempty_iff_full_contract

theorem survivingCodes_card_eq_one :
    exitCapacityProgram.exitCone.survivingCodes.card = 1 := by
  classical
  rw [Finset.card_eq_one]
  refine ⟨ExitFutureCode.leave,
    Finset.eq_singleton_iff_unique_mem.mpr ⟨actionableExit.2, ?_⟩⟩
  intro code member
  have generated :=
    (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
      noCapture independentExitRelation code).mp member
  cases code with
  | idle => exact False.elim (generated.2.2.1 rfl)
  | work =>
      have continuation := Classical.choice generated.2.1
      exact nomatch continuation
  | leave => rfl

/-- Exactly one simultaneous role-independent exit survives: service offers
two slots, but the source relation owns one uncaptured actionable code. -/
theorem actionableExitCapacity_eq_one :
    geometryCompiler.actionableExitCapacity = 1 := by
  have upper := geometryCompiler.capacity_le_surviving_actionable_codes
  rw [survivingCodes_card_eq_one] at upper
  have lower : 1 ≤ geometryCompiler.actionableExitCapacity :=
    Nat.succ_le_iff.mpr capacity_positive
  exact Nat.le_antisymm upper lower

/-- The same source payment and actual services generate no actionable exit
when price capture consumes the only independent continuation. -/
theorem captured_nominal_actual_capacity_eq_zero :
    capturedGeometryCompiler.actionableExitCapacity = 0 :=
  capturedGeometryCompiler.nominal_transfer_no_exit_capacity nominalTransfer

theorem capacity_bounded_by_actual_service_and_root :
    geometryCompiler.actionableExitCapacity ≤ anomiePhase.served.length ∧
      geometryCompiler.actionableExitCapacity ≤ anomiePhase.capacity :=
  ⟨geometryCompiler.capacity_le_actual_served_slots,
    geometryCompiler.capacity_le_rootOperationalCapacity⟩

/-- Anomie does not imply zero exit capacity: this exact occurrence serves two
of three crossings, retains backlog, and still realizes one independent exit. -/
theorem anomie_with_positive_exit_capacity :
    anomiePhase.phaseTag = .anomie ∧
      0 < geometryCompiler.actionableExitCapacity ∧
      anomiePhase.backlog ≠ [] := by
  refine ⟨anomiePhase_tag, capacity_positive, ?_⟩
  exact anomiePhase.anomie_backlog_ne_nil anomiePhase_tag

/-- The UBI and proof-carrying coordinates consume the same exact root row and
whole-ledger successor. -/
theorem proofCarrying_and_ubi_share_root_authority :
    installedRenewal.payload.sourceEntry = installedUBI.payload.sourceEntry ∧
      HEq installedRenewal.payload.selectedRow installedUBI.payload.selectedRow ∧
      HEq installedRenewal.payload.successor installedUBI.payload.successor ∧
      installedRenewal.RootAnswerAndNextFactorizes ∧
      installedUBI.RootAnswerAndNextFactorizes :=
  ⟨installed_coordinates_share_sourceEntry,
    installed_coordinates_share_selectedRow,
    installed_coordinates_share_successor,
    installedRenewal.rootAnswerAndNext_factorizes,
    ubi_root_factorization⟩

/-- The pre-emitter UBI payload contains only its source restriction; the
actionable renewal is produced here after actual payment/route/service join. -/
theorem root_payload_does_not_preinstall_exit_verdict : True := by
  fail_if_success exact installedUBI.payload.consumer.exitRenewal
  trivial

end
end M14UBIProofCarryingRootCapacity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBIProofCarryingRootCapacity.strongest_actual_exit_renewal_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIProofCarryingRootCapacity.actionableExitCapacity_eq_one
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIProofCarryingRootCapacity.proofCarrying_and_ubi_share_root_authority

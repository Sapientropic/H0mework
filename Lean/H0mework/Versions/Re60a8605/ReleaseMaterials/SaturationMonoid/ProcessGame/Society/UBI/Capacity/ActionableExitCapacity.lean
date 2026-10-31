import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.EmploymentIndependentExit
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.CanonicalMaximumMatching
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.CrossingCostPhase
import Mathlib.Data.Fintype.Card

/-!
# Source-generated actionable-exit service capacity

An uncaptured continuation is not yet an actionable social exit.  It must be
payable by the exact purchasing-power standing, routed through a generated
crossing, and assigned to an actually debited service slot.  This module
canonically maximizes simultaneous feasible assignments without storing a
caller-selected matching.

The result is bounded both by relation-owned actionable codes and by actual
service receipts, hence by the installed root progress budget.  Anomie may
leave positive exit capacity; it only prevents serving every arrival.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UBI
namespace Capacity

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money Power
open Renewal _root_.SaturationMonoid.ProcessGame.Society.Capacity
open Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler

universe u

variable {Source State : Type u}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, u, u} occurrenceOf game}
variable {V : ResponsibilityLifecycle.Vocabulary.{u}}
variable {P : NativeResponsibilityProcess V}
variable {incidence : ActorResponsibilityIncidence core V}
variable
  {exchangeRelationCompiler : SourceOwnedRelationRoleCompiler.{u, u, u, u}
    occurrenceOf game core.targetFace}
variable
  {exchangeLaw : SourceOwnedExchangeLaw.{u, u, u, u, u, u}
    core V P incidence exchangeRelationCompiler}
variable
  {settlementCompiler : SourceOwnedSettlementCompiler.{u, u, u, u, u, u, u}
    exchangeLaw}
variable
  {activationCompiler :
    SourceOwnedResidualConsumerCompiler.{u, u, u, u, u, u, u, u}
      settlementCompiler}

variable {controllerFace : M0BoundaryFace.{u, u, u} occurrenceOf}
variable
  {exitRelationCompiler : SourceOwnedRelationRoleCompiler.{u, u, u, u}
    occurrenceOf game core.targetFace}
variable
  {employmentController : SourceOwnedActionControllerCompiler.{u, u, u, u}
    game controllerFace}
variable [Zero (exitRelationCompiler.Phase game.source)]

variable {paymentSeed : activationCompiler.ExactActivationSeed}
variable {PriceValue : Type u}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (paymentSeed.occurrence activationCompiler) PriceValue}
variable {employer : employmentController.Actor}
variable {worker : exitRelationCompiler.Actor}
variable {employment exitRelation : exitRelationCompiler.GeneratedRelation}
variable {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
  (OpenSettlementAt settlementCompiler
    (paymentSeed.occurrence activationCompiler))
  (exactOpenSettlement paymentSeed)}
variable {program : ExitCapacityProgramAt paymentSeed observer employer worker
  employment exitRelation capture}

variable {N : WorldRelationNetwork.{u}}
variable {RootV : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N RootV}
variable {CapacitySource CapacityState : Type u}
variable {capacityOccurrenceOf :
  CapacitySource → RootedAccountedUnfolding CapacityState}
variable {capacityGame : SaturationMonoid.ProcessGame capacityOccurrenceOf}
variable {Seed : Type u}
variable {SeedAt : CapacitySource → CapacityState → Seed → Prop}
variable {Lineage : CapacitySource → Type u}
variable {lineageOf : ∀ source,
  SourceSeed capacityOccurrenceOf Seed SeedAt source → Lineage source}
variable {ConsumerAt DispositionAt :
  SourceSeed capacityOccurrenceOf Seed SeedAt capacityGame.source → Type u}
variable {recognition : SourceNativeRenewalRecognitionAt root capacityGame Seed
  SeedAt ConsumerAt DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {installed : SourceInstalledRenewalAt recognition visit}
variable {rateCompiler : SourceOwnedOccurrenceRateCompiler.{u, u, u, u, u}
  capacityGame Seed SeedAt Lineage lineageOf installed.payload.sourceSeed}
variable {exactPrefix : SourceGeneratedExactQueuePrefixAt rateCompiler}
variable {phase : SourceGeneratedOccurrenceCapacityPhaseAt
  installed rateCompiler exactPrefix}
variable {crossingCompiler : SourceOwnedCrossingCompiler rateCompiler}

variable {RunV : ResponsibilityLifecycle.Vocabulary.{u}}
variable {RunP : NativeResponsibilityProcess RunV}
variable {B : NativeCarryDebitProcess RunP}
variable {runLineage : RunV.Lineage}
variable {sourceState targetState : ResponsibilityState RunV}
variable {run : RunP.Run sourceState targetState}
variable {debited : NativeDebitedRun RunP B runLineage run}
variable {service : SourceOwnedOccurrenceServiceCompiler rateCompiler RunP}
variable {actualSettlement : ExactServedCrossingDebitedRunAt
  phase debited service}

/-- Source law for the two missing incidence families.  It stores no payment
witness, code, route, slot, matching, capacity, or completed path. -/
structure SourceOwnedExitGeometryCompilerAt
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture)
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed rateCompiler exactPrefix)
    (crossingCompiler : SourceOwnedCrossingCompiler rateCompiler)
    {sourceState targetState : ResponsibilityState RunV}
    (run : RunP.Run sourceState targetState)
    (service : SourceOwnedOccurrenceServiceCompiler rateCompiler RunP)
    (actualSettlement : ExactServedCrossingDebitedRunAt
      phase debited service) :
    Type (u + 1) where
  PaysForAt : PurchasingPowerStandingAt paymentSeed observer →
    exitRelationCompiler.FutureCode → Type u
  RoutesAt : exitRelationCompiler.FutureCode →
    crossingCompiler.ExactCrossing → Type u

namespace SourceOwnedExitGeometryCompilerAt

variable (geometryCompiler : SourceOwnedExitGeometryCompilerAt
  program phase crossingCompiler run service actualSettlement)

/-- One exact code/service-slot incidence. -/
structure FeasibleExitEdgeAt
    (code : exitRelationCompiler.FutureCode)
    (slot : Fin phase.served.length) : Type u where
  codeSurvives : code ∈ program.exitCone.survivingCodes
  paymentReceipt : geometryCompiler.PaysForAt
    program.purchasingPowerStanding code
  routeReceipt : geometryCompiler.RoutesAt code
    (ExactServedCrossingDebitedRunAt.servicedCrossingAt
      (phase := phase) (crossingCompiler := crossingCompiler) slot)
  eventIndex : Fin run.events.length
  sameOrdinal : eventIndex.val = slot.val
  serviceReceipt : service.ServesAt
    (phase.served.get slot)
    (run.events.get eventIndex)

namespace FeasibleExitEdgeAt

variable {geometryCompiler : SourceOwnedExitGeometryCompilerAt
  program phase crossingCompiler run service actualSettlement}
variable {code : exitRelationCompiler.FutureCode}
variable {slot : Fin phase.served.length}

/-- Sole producer: payment and route receipts are joined to the canonical
actual lifecycle service receipt at the same ordinal. -/
def generate
    (codeSurvives : code ∈ program.exitCone.survivingCodes)
    (paymentReceipt : geometryCompiler.PaysForAt
      program.purchasingPowerStanding code)
    (routeReceipt : geometryCompiler.RoutesAt code
      (ExactServedCrossingDebitedRunAt.servicedCrossingAt
        (phase := phase) (crossingCompiler := crossingCompiler) slot)) :
    FeasibleExitEdgeAt (phase := phase) (run := run) (service := service)
      (actualSettlement := actualSettlement) geometryCompiler code slot where
  codeSurvives := codeSurvives
  paymentReceipt := paymentReceipt
  routeReceipt := routeReceipt
  eventIndex := Fin.cast actualSettlement.eventsLength_eq_allocated.symm slot
  sameOrdinal := rfl
  serviceReceipt := actualSettlement.serviceReceiptAt slot

end FeasibleExitEdgeAt

abbrev ExactFeasibleExitEdgeAt
    (code : exitRelationCompiler.FutureCode)
    (slot : Fin phase.served.length) :=
  FeasibleExitEdgeAt (phase := phase) (run := run) (service := service)
    (actualSettlement := actualSettlement) geometryCompiler code slot

local instance futureCodeDecidableEq :
    DecidableEq exitRelationCompiler.FutureCode :=
  exitRelationCompiler.futureCodeDecidableEq

/-- Canonical bipartite geometry: surviving codes on the left, actual debited
service ordinals on the right. -/
noncomputable def matchingGeometry :
    CanonicalBipartiteFeasibility exitRelationCompiler.FutureCode
      (Fin phase.served.length) where
  leftCarrier := program.exitCone.survivingCodes
  rightCarrier := (Finset.univ : Finset (Fin phase.served.length))
  Feasible := fun code slot =>
    Nonempty (ExactFeasibleExitEdgeAt geometryCompiler code slot)
  feasibleDecidable := fun _ _ => Classical.propDecidable _

/-- Maximum simultaneous actionable exits. -/
noncomputable def actionableExitCapacity : Nat :=
  geometryCompiler.matchingGeometry.maximumMatchingCapacity

/-- A real renewal consumes one exact feasible code/slot edge. -/
structure SourceGeneratedActionableExitRenewalAt : Type u where
  code : exitRelationCompiler.FutureCode
  slot : Fin phase.served.length
  feasible : ExactFeasibleExitEdgeAt geometryCompiler code slot

theorem capacity_positive_iff_feasible_edge :
    0 < geometryCompiler.actionableExitCapacity ↔
      ∃ code slot,
        Nonempty (ExactFeasibleExitEdgeAt geometryCompiler code slot) := by
  rw [actionableExitCapacity,
    geometryCompiler.matchingGeometry.positive_capacity_iff_feasible_edge]
  constructor
  · rintro ⟨edge, edgeMember⟩
    have generated :=
      (geometryCompiler.matchingGeometry.mem_edgeCarrier_iff edge).mp
        edgeMember
    exact ⟨edge.1, edge.2, generated.2.2⟩
  · rintro ⟨code, slot, feasible⟩
    refine ⟨(code, slot),
      (geometryCompiler.matchingGeometry.mem_edgeCarrier_iff
        (code, slot)).mpr ?_⟩
    rcases feasible with ⟨edge⟩
    exact ⟨edge.codeSurvives, Finset.mem_univ _, ⟨edge⟩⟩

theorem capacity_positive_iff_actionableExitRenewal :
    0 < geometryCompiler.actionableExitCapacity ↔
      Nonempty geometryCompiler.SourceGeneratedActionableExitRenewalAt := by
  rw [geometryCompiler.capacity_positive_iff_feasible_edge]
  constructor
  · rintro ⟨code, slot, ⟨feasible⟩⟩
    exact ⟨⟨code, slot, feasible⟩⟩
  · rintro ⟨renewal⟩
    exact ⟨renewal.code, renewal.slot, ⟨renewal.feasible⟩⟩

/-- Strongest iff: actual exit renewal exists exactly when one generated,
non-idle, uncaptured target continuation is paid by the source-backed
purchasing-power standing, routed through an exact crossing, and joined to an
actually debited service ordinal.  Employment loss and relation independence
remain immutable indices of `program`. -/
theorem actionableExitRenewal_nonempty_iff_full_contract :
    Nonempty geometryCompiler.SourceGeneratedActionableExitRenewalAt ↔
      ∃ (code : exitRelationCompiler.FutureCode)
        (slot : Fin phase.served.length),
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          exitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ capture.Captures code ∧
        Nonempty (geometryCompiler.PaysForAt
          program.purchasingPowerStanding code) ∧
        Nonempty (geometryCompiler.RoutesAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := phase) (crossingCompiler := crossingCompiler) slot)) := by
  constructor
  · rintro ⟨renewal⟩
    have generated :=
      (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
        capture exitRelation renewal.code).mp
        renewal.feasible.codeSurvives
    exact ⟨renewal.code, renewal.slot, generated.1, generated.2.1,
      generated.2.2.1, generated.2.2.2,
      ⟨renewal.feasible.paymentReceipt⟩,
      ⟨renewal.feasible.routeReceipt⟩⟩
  · rintro ⟨code, slot, inCarrier, continuation, nonIdle, uncaptured,
      ⟨paymentReceipt⟩, ⟨routeReceipt⟩⟩
    have codeSurvives : code ∈ program.exitCone.survivingCodes :=
      (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
        capture exitRelation code).mpr
        ⟨inCarrier, continuation, nonIdle, uncaptured⟩
    let feasible := FeasibleExitEdgeAt.generate
      (actualSettlement := actualSettlement) codeSurvives paymentReceipt
        routeReceipt
    exact ⟨⟨code, slot, feasible⟩⟩

theorem capacity_le_surviving_actionable_codes :
    geometryCompiler.actionableExitCapacity ≤
      program.exitCone.survivingCodes.card :=
  geometryCompiler.matchingGeometry.maximumMatchingCapacity_le_left

theorem capacity_le_actual_served_slots :
    geometryCompiler.actionableExitCapacity ≤
      phase.served.length := by
  change geometryCompiler.matchingGeometry.maximumMatchingCapacity ≤
    phase.served.length
  calc
    _ ≤ geometryCompiler.matchingGeometry.rightCarrier.card :=
      geometryCompiler.matchingGeometry.maximumMatchingCapacity_le_right
    _ = phase.served.length := by
      simp only [matchingGeometry, Finset.card_univ, Fintype.card_fin]

theorem capacity_le_rootOperationalCapacity :
    geometryCompiler.actionableExitCapacity ≤
      phase.capacity := by
  exact geometryCompiler.capacity_le_actual_served_slots.trans <| by
    rw [phase.served_length]
    exact Nat.min_le_left _ _

theorem no_actual_service_no_exit_capacity
    (noService : phase.served = []) :
    geometryCompiler.actionableExitCapacity = 0 := by
  have lengthZero : phase.served.length = 0 := by simp [noService]
  apply Nat.eq_zero_of_le_zero
  simpa [lengthZero] using
    geometryCompiler.capacity_le_actual_served_slots

theorem full_capture_no_exit_capacity
    (fullCapture : program.exitCone.FullPriceCaptureAt) :
    geometryCompiler.actionableExitCapacity = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [geometryCompiler.capacity_positive_iff_feasible_edge]
  rintro ⟨_code, _slot, ⟨edge⟩⟩
  have noExit : IsEmpty program.exitCone.ActionableExitAt :=
    program.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mpr
      fullCapture
  exact noExit.false ⟨_, edge.codeSurvives⟩

theorem nominal_transfer_no_exit_capacity
    (nominal : NominalTransferReadoutAt program) :
    geometryCompiler.actionableExitCapacity = 0 :=
  geometryCompiler.full_capture_no_exit_capacity nominal.fullCapture

theorem no_payment_receipts_no_exit_capacity
    (noPayment : ∀ code,
      IsEmpty (geometryCompiler.PaysForAt
        program.purchasingPowerStanding code)) :
    geometryCompiler.actionableExitCapacity = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [geometryCompiler.capacity_positive_iff_feasible_edge]
  rintro ⟨code, _slot, ⟨edge⟩⟩
  exact (noPayment code).false edge.paymentReceipt

theorem no_route_receipts_no_exit_capacity
    (noRoute : ∀ code crossing,
      IsEmpty (geometryCompiler.RoutesAt code crossing)) :
    geometryCompiler.actionableExitCapacity = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [geometryCompiler.capacity_positive_iff_feasible_edge]
  rintro ⟨code, slot, ⟨edge⟩⟩
  exact (noRoute code
    (ExactServedCrossingDebitedRunAt.servicedCrossingAt
      (phase := phase) (crossingCompiler := crossingCompiler) slot)).false
    edge.routeReceipt

end SourceOwnedExitGeometryCompilerAt

end Capacity
end UBI
end Society
end ProcessGame
end SaturationMonoid

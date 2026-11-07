import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.ActionableExitCapacity
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Completion

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

namespace SourceOwnedExitGeometryCompilerAt

variable (geometryCompiler : SourceOwnedExitGeometryCompilerAt
  program phase crossingCompiler run service actualSettlement)

/-- Retain the original non-idle target futures as demand. Capture,
payment and route still decide which original edges can be used. -/
noncomputable def originalDemandGeometry :
    CanonicalBipartiteFeasibility exitRelationCompiler.FutureCode (Fin phase.served.length) :=
  { geometryCompiler.matchingGeometry with
    leftCarrier := exitRelationCompiler.actionableFutureCodesAt exitRelation .target }

theorem original_demand_keeps_exactly_the_same_paid_edges :
    geometryCompiler.originalDemandGeometry.edgeCarrier = geometryCompiler.matchingGeometry.edgeCarrier := by
  classical
  ext edge
  rw [geometryCompiler.originalDemandGeometry.mem_edgeCarrier_iff,
    geometryCompiler.matchingGeometry.mem_edgeCarrier_iff]
  constructor
  · rintro ⟨_, item, ⟨paid⟩⟩
    exact ⟨paid.codeSurvives, item, ⟨paid⟩⟩
  · rintro ⟨survives, item, paid⟩
    exact ⟨(Finset.mem_filter.mp survives).1, item, paid⟩

theorem original_demand_has_the_same_actual_exit_capacity :
    geometryCompiler.originalDemandGeometry.maximumMatchingCapacity = geometryCompiler.actionableExitCapacity := by
  unfold actionableExitCapacity CanonicalBipartiteFeasibility.maximumMatchingCapacity
    CanonicalBipartiteFeasibility.matchings CanonicalBipartiteFeasibility.IsMatching
  rw [original_demand_keeps_exactly_the_same_paid_edges]

/-- No captured original continuation can disappear from the demand side
of the capacity equation. The paid side still uses the same actual edges. -/
theorem actual_exit_capacity_and_original_deficit_balance_the_full_source_demand :
    geometryCompiler.actionableExitCapacity + maximumDeficit geometryCompiler.originalDemandGeometry =
      (exitRelationCompiler.actionableFutureCodesAt exitRelation .target).card := by
  rw [← original_demand_has_the_same_actual_exit_capacity geometryCompiler]
  exact actual_capacity_plus_the_largest_original_deficit_is_the_full_need _

theorem full_capture_leaves_all_original_exit_demand_as_an_exact_deficit
    (captured : program.exitCone.FullPriceCaptureAt) :
    maximumDeficit geometryCompiler.originalDemandGeometry =
      (exitRelationCompiler.actionableFutureCodesAt exitRelation .target).card := by
  have balance := geometryCompiler.actual_exit_capacity_and_original_deficit_balance_the_full_source_demand
  rw [geometryCompiler.full_capture_no_exit_capacity captured, zero_add] at balance
  exact balance

theorem the_original_exit_neighbours_require_payment_route_and_noncapture
    (codes : Finset exitRelationCompiler.FutureCode)
    (original : codes ⊆ geometryCompiler.originalDemandGeometry.leftCarrier)
    (slot : Fin phase.served.length) :
    slot ∈ neighbours geometryCompiler.originalDemandGeometry codes ↔
      ∃ code ∈ codes, ¬ capture.Captures code ∧
        Nonempty (geometryCompiler.PaysForAt program.purchasingPowerStanding code) ∧
        Nonempty (geometryCompiler.RoutesAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := phase) (crossingCompiler := crossingCompiler) slot)) := by
  classical
  rw [neighbour_iff_original_compatible_edge]
  constructor
  · rintro ⟨code, listed, _, ⟨paid⟩⟩
    have actual := (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff capture exitRelation code).mp
      paid.codeSurvives
    exact ⟨code, listed, actual.2.2.2, ⟨paid.paymentReceipt⟩, ⟨paid.routeReceipt⟩⟩
  · rintro ⟨code, listed, independent, ⟨payment⟩, ⟨route⟩⟩
    have survives : code ∈ program.exitCone.survivingCodes :=
      Finset.mem_filter.mpr ⟨original listed, independent⟩
    exact ⟨code, listed, Finset.mem_univ _, ⟨FeasibleExitEdgeAt.generate
      (actualSettlement := actualSettlement) survives payment route⟩⟩

end SourceOwnedExitGeometryCompilerAt

end Capacity
end UBI
end Society
end ProcessGame
end SaturationMonoid

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.OriginalDemand
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Money.PurchasingPower.Observer

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

variable {NewValue : Type u}
variable (replacement : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (paymentSeed.occurrence activationCompiler) NewValue)

/-- Reobserve the same payment and relation. No source or capture law is
changed by changing its quote. -/
def reobservedProgram : ExitCapacityProgramAt paymentSeed replacement employer worker
    employment exitRelation capture :=
  ExitCapacityProgramAt.generate (program.payment.reobserve replacement)
    program.employmentLoss program.exitInterest program.employment_ne_exitRelation

/-- Each retained payment receipt still belongs to the old actual payment.
The replacement observer contributes no receipts of its own. -/
def reobserve (geometry : SourceOwnedExitGeometryCompilerAt program phase crossingCompiler run service actualSettlement) :
    SourceOwnedExitGeometryCompilerAt (reobservedProgram (program := program) replacement)
      phase crossingCompiler run service actualSettlement where
  PaysForAt := fun _ code => geometry.PaysForAt program.purchasingPowerStanding code
  RoutesAt := geometry.RoutesAt

theorem changing_only_the_observation_keeps_all_original_paid_exit_edges
    (geometry : SourceOwnedExitGeometryCompilerAt program phase crossingCompiler run service actualSettlement) :
    (geometry.reobserve replacement).originalDemandGeometry.edgeCarrier = geometry.originalDemandGeometry.edgeCarrier := by
  classical
  ext edge
  rw [((geometry.reobserve replacement).originalDemandGeometry).mem_edgeCarrier_iff,
    geometry.originalDemandGeometry.mem_edgeCarrier_iff]
  constructor
  · rintro ⟨original, served, ⟨paid⟩⟩
    exact ⟨original, served, ⟨FeasibleExitEdgeAt.generate
      (actualSettlement := actualSettlement) paid.codeSurvives paid.paymentReceipt paid.routeReceipt⟩⟩
  · rintro ⟨original, served, ⟨paid⟩⟩
    exact ⟨original, served, ⟨FeasibleExitEdgeAt.generate
      (actualSettlement := actualSettlement) paid.codeSurvives paid.paymentReceipt paid.routeReceipt⟩⟩

theorem changing_only_the_observation_keeps_original_exit_capacity_and_shortage
    (geometry : SourceOwnedExitGeometryCompilerAt program phase crossingCompiler run service actualSettlement) :
    (geometry.reobserve replacement).actionableExitCapacity = geometry.actionableExitCapacity ∧
      maximumDeficit (geometry.reobserve replacement).originalDemandGeometry =
        maximumDeficit geometry.originalDemandGeometry := by
  let revised := geometry.reobserve replacement
  have oldEdges := geometry.original_demand_keeps_exactly_the_same_paid_edges
  have revisedEdges := revised.original_demand_keeps_exactly_the_same_paid_edges
  have edges := revisedEdges.symm.trans
    ((geometry.changing_only_the_observation_keeps_all_original_paid_exit_edges replacement).trans oldEdges)
  have capacity : revised.actionableExitCapacity = geometry.actionableExitCapacity := by
    unfold actionableExitCapacity CanonicalBipartiteFeasibility.maximumMatchingCapacity
      CanonicalBipartiteFeasibility.matchings CanonicalBipartiteFeasibility.IsMatching
    rw [edges]
  have first := revised.actual_exit_capacity_and_original_deficit_balance_the_full_source_demand
  have second := geometry.actual_exit_capacity_and_original_deficit_balance_the_full_source_demand
  rw [capacity] at first
  exact ⟨capacity, Nat.add_left_cancel (first.trans second.symm)⟩

end SourceOwnedExitGeometryCompilerAt

end Capacity
end UBI
end Society
end ProcessGame
end SaturationMonoid

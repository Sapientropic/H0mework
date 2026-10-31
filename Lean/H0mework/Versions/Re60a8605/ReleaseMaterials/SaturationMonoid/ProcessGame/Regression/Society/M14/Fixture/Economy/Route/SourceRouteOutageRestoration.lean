import H0mework.Society.Renewal.InstalledRenewalProjection
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.UBIProofCarryingRootRestriction

/-!
# M14 root-independent route-outage restoration

A route outage is not another branch inside the installed UBI disposition.
It owns a distinct renewal-law mouth: the source route family is definitionally
empty, while the target route family is the existing generated UBI receipt
family.  The applied action is indexed by the existing route-bottleneck kind
and compiler-generated `restoreRoute` repair.

This fixture is root-polymorphic.  It contains no temporal depth, service or
capacity result, living root, row, ledger, next current, trace, measure, U8
object, or completed future.  A later same-root coordinate must supply its own
existing renewal shell before the outage and action can become operational.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceRouteOutageRestoration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money Renewal UBI Policy
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M10OccurrenceCapacityProcessFixture
open M11GeneratedSocialSpaceCrossingFixture
open M14UBIExitCapacityFixture
open M14EssentialAccessRelationFixture
open M14UBIProofCarryingRootRestriction

abbrev LocalGame := M14UBIProofCarryingRootRestriction.LocalGame
abbrev LocalSeed := M14UBIProofCarryingRootRestriction.LocalSeed
abbrev LocalSeedAt := M14UBIProofCarryingRootRestriction.LocalSeedAt

/-- Exact absent route-incidence family.  It is a type family, not a Boolean
outage flag or an observer verdict. -/
abbrev RouteOutageRoutesAt
    (_code : exitRelationCompiler.FutureCode)
    (_crossing : ConcreteCrossing) : Type :=
  PEmpty

/-! ## Source restriction -/

/-- Root-independent source cause.  The route family is a dependent index;
the exact source producer below fixes it to `RouteOutageRoutesAt`. -/
structure SourceRouteOutageRestrictionAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source)
    (RoutesAt : exitRelationCompiler.FutureCode →
      ConcreteCrossing → Type) : Type where
  private mk ::
  seed_eq : seed = focalSeed
  tenureInterest : essentialAccessRelationCompiler.GeneratedInterestAt
    tenureActor tenureRelation
  tenureActorIsCounterparty :
    tenureActor = Money.exactCounterpartyActor exactResidualActivation
  tenurePhase : essentialAccessRelationCompiler.phaseStep tenureRelation =
    .tenure
  tenureRole : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target .tenureProvider
  uncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  paymentReceipt : SourceBackedUBIPaymentReceiptAt
    exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave
  routeMissing : (crossing : ConcreteCrossing) →
    IsEmpty (RoutesAt ExitFutureCode.leave crossing)

abbrev ExactSourceRouteOutageRestrictionAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  SourceRouteOutageRestrictionAt seed RouteOutageRoutesAt

/-- Sole route-outage source producer. -/
def sourceRouteOutageRestriction :
    ExactSourceRouteOutageRestrictionAt focalSeed where
  seed_eq := rfl
  tenureInterest := M14EssentialAccessRelationFixture.tenureInterest
  tenureActorIsCounterparty := tenure_actor_is_exact_payment_counterparty
  tenurePhase := tenure_phase_is_generated
  tenureRole := ⟨M14EssentialAccessRelationFixture.tenureInterest, rfl⟩
  uncaptured := by simp [noCapture]
  paymentReceipt := SourceBackedUBIPaymentReceiptAt.generate
  routeMissing := fun _crossing => by
    change IsEmpty PEmpty
    infer_instance

/-! ## Type-indexed restoration action -/

/-- The action changes only the route-incidence family.  Its failure kind and
repair are existing policy indices; neither is selected by a result readout. -/
structure SourceAppliedRouteRestorationAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source)
    (sourceRoutes targetRoutes : exitRelationCompiler.FutureCode →
      ConcreteCrossing → Type)
    (failureKind : ExactExitFailureKind)
    (repair : ExactExitRepair) : Type where
  private mk ::
  seed_eq : seed = focalSeed
  sourceRoutes_eq : sourceRoutes = RouteOutageRoutesAt
  targetRoutes_eq : targetRoutes = SourceGeneratedUBIRouteReceiptAt
  sourceCause : SourceRouteOutageRestrictionAt seed sourceRoutes
  failureKind_eq : failureKind = .routeBottleneck
  repair_eq : repair = exactExitRepairCompiler.compile failureKind

abbrev ExactSourceAppliedRouteRestorationAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  SourceAppliedRouteRestorationAt seed RouteOutageRoutesAt
    SourceGeneratedUBIRouteReceiptAt .routeBottleneck .restoreRoute

/-- Sole applied-action producer.  The generated target receipt family is a
type index; no completed receipt table is stored in the value. -/
def sourceGeneratedRouteRestoration :
    ExactSourceAppliedRouteRestorationAt focalSeed where
  seed_eq := rfl
  sourceRoutes_eq := rfl
  targetRoutes_eq := rfl
  sourceCause := sourceRouteOutageRestriction
  failureKind_eq := rfl
  repair_eq := rfl

namespace SourceAppliedRouteRestorationAt

def failureKindAt
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    {sourceRoutes targetRoutes : exitRelationCompiler.FutureCode →
      ConcreteCrossing → Type}
    {failureKind : ExactExitFailureKind} {repair : ExactExitRepair}
    (_action : SourceAppliedRouteRestorationAt seed sourceRoutes targetRoutes
      failureKind repair) : ExactExitFailureKind :=
  failureKind

def repairAt
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    {sourceRoutes targetRoutes : exitRelationCompiler.FutureCode →
      ConcreteCrossing → Type}
    {failureKind : ExactExitFailureKind} {repair : ExactExitRepair}
    (_action : SourceAppliedRouteRestorationAt seed sourceRoutes targetRoutes
      failureKind repair) : ExactExitRepair :=
  repair

@[simp] theorem exact_failureKindAt :
    failureKindAt sourceGeneratedRouteRestoration =
      ExactExitFailureKind.routeBottleneck :=
  rfl

@[simp] theorem exact_repairAt :
    repairAt sourceGeneratedRouteRestoration = ExactExitRepair.restoreRoute :=
  rfl

end SourceAppliedRouteRestorationAt

/-! ## Root-polymorphic law mouth -/

abbrev RouteOutageConsumerAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  ExactSourceRouteOutageRestrictionAt seed

abbrev RouteRestorationDispositionAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  ExactSourceAppliedRouteRestorationAt seed

abbrev SourceRouteOutageRestorationLawAt
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    (source : SourceNativeLedgerSource N RootV) :=
  SourceNativeRenewalProjectionLaw source LocalGame LocalSeed LocalSeedAt
    RouteOutageConsumerAt RouteRestorationDispositionAt

/-- The later living root supplies only its already generated shell.  Cause,
route families, failure kind, and repair remain fixed by this fixture. -/
def sourceRouteOutageRestorationLaw
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source) :
    SourceRouteOutageRestorationLawAt source :=
  SourceNativeRenewalProjectionLaw.ofRootShell shell focalSeed
    sourceRouteOutageRestriction sourceGeneratedRouteRestoration

/-! ## Exact negative controls -/

instance removeCaptureRouteRestoration_isEmpty : IsEmpty
    (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
      SourceGeneratedUBIRouteReceiptAt .routeBottleneck .removeCapture) :=
  ⟨fun action => by
    have impossible := action.repair_eq
    cases impossible⟩

instance tenureKindRouteRestoration_isEmpty : IsEmpty
    (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
      SourceGeneratedUBIRouteReceiptAt .tenureCapture .restoreRoute) :=
  ⟨fun action => by cases action.failureKind_eq⟩

theorem noRouteOutageCause_noRestoration
    (noCause : IsEmpty
      (ExactSourceRouteOutageRestrictionAt focalSeed)) :
    IsEmpty (ExactSourceAppliedRouteRestorationAt focalSeed) :=
  ⟨fun action => noCause.false action.sourceCause⟩

/-- An actually generated full-route receipt refutes retyping that route
family as the outage source. -/
instance generatedFullRouteSource_isNotOutage : IsEmpty
    (SourceRouteOutageRestrictionAt focalSeed
      SourceGeneratedUBIRouteReceiptAt) :=
  ⟨fun source =>
    (source.routeMissing firstCrossing).false
      (SourceGeneratedUBIRouteReceiptAt.generate firstCrossing)⟩

instance generatedFullRouteSource_cannotGenerateRouteRestoration : IsEmpty
    (SourceAppliedRouteRestorationAt focalSeed
      SourceGeneratedUBIRouteReceiptAt SourceGeneratedUBIRouteReceiptAt
      .routeBottleneck .restoreRoute) :=
  ⟨fun action => generatedFullRouteSource_isNotOutage.false
    action.sourceCause⟩

/-- The empty source family cannot be re-used as the action target. -/
instance outageTarget_cannotGenerateRouteRestoration : IsEmpty
    (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
      RouteOutageRoutesAt .routeBottleneck .restoreRoute) :=
  ⟨fun action => by
    have familyEq := action.targetRoutes_eq
    have typeEq := congrFun
      (congrFun familyEq ExitFutureCode.leave) firstCrossing
    have generated := SourceGeneratedUBIRouteReceiptAt.generate firstCrossing
    have impossible : RouteOutageRoutesAt ExitFutureCode.leave firstCrossing :=
      typeEq.symm ▸ generated
    exact nomatch impossible⟩

theorem route_restoration_mouth_has_no_temporal_or_probability_fields : True := by
  fail_if_success exact sourceGeneratedRouteRestoration.depth
  fail_if_success exact sourceGeneratedRouteRestoration.service
  fail_if_success exact sourceGeneratedRouteRestoration.capacity
  fail_if_success exact sourceGeneratedRouteRestoration.root
  fail_if_success exact sourceGeneratedRouteRestoration.selectedRow
  fail_if_success exact sourceGeneratedRouteRestoration.wholeLedger
  fail_if_success exact sourceGeneratedRouteRestoration.nextCurrent
  fail_if_success exact sourceGeneratedRouteRestoration.trace
  fail_if_success exact sourceGeneratedRouteRestoration.measure
  fail_if_success exact sourceGeneratedRouteRestoration.probability
  fail_if_success exact sourceGeneratedRouteRestoration.u8Core
  fail_if_success exact sourceGeneratedRouteRestoration.completedFuture
  trivial

end
end M14SourceRouteOutageRestoration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceRouteOutageRestoration.sourceRouteOutageRestriction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceRouteOutageRestoration.sourceGeneratedRouteRestoration
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceRouteOutageRestoration.sourceRouteOutageRestorationLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceRouteOutageRestoration.generatedFullRouteSource_isNotOutage

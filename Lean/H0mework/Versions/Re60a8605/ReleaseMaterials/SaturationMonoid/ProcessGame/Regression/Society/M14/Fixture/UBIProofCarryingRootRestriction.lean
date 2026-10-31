import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.UBIExitCapacityFixture
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessPaymentPurposeLaw
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.Fixture.GeneratedSocialSpaceCrossing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Policy.SourceOwnedExitRepairCompiler

/-!
# M14 source-native UBI root restriction

The restriction installed into the existing M9/M13 root carries the source
program and exact repair compiler needed to ask and repair the UBI question.
Its local seed is the focal seed of the existing recurrent M10 occurrence
process, so the later capacity phase is indexed by the same installed renewal
coordinate.

Payment and route authority are fixed type indices of the restriction.  Their
receipts are generated later from the exact purchasing-power standing and the
exact crossing occurrence.  The separate payload disposition carries the
source tenure-capture facts and compiler-applied capture removal, but no exit
verdict, chosen continuation, service slot, matching, capacity, effectiveness
proof, or completed future is stored before emission.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIProofCarryingRootRestriction

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Capacity Space Policy
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M8MoneyRootInstallationRegression
open M10OccurrenceCapacityProcessFixture
open M14UBIExitCapacityFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw

abbrev LocalGame := M10OccurrenceCapacityProcessFixture.game
abbrev LocalSeed := M10OccurrenceCapacityProcessFixture.Seed
abbrev LocalSeedAt := M10OccurrenceCapacityProcessFixture.seedAt

abbrev ConcreteProgramType := ExitCapacityProgramAt exactResidualActivation
  (rootPriceObserver exactResidualActivation) employer worker
  employmentRelation independentExitRelation noCapture

abbrev ConcreteCapturedProgramType :=
  ExitCapacityProgramAt exactResidualActivation
    (rootPriceObserver exactResidualActivation) employer worker
    employmentRelation independentExitRelation fullCapture

abbrev ConcreteStanding := PurchasingPowerStandingAt exactResidualActivation
  (rootPriceObserver exactResidualActivation)

abbrev ConcreteCrossing :=
  M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.ExactCrossing

/-- A payment receipt is indexed by the exact source-backed standing and
records its generating event and next state.  The private constructor prevents
a nominal balance readout from being substituted for the payment occurrence. -/
structure SourceBackedUBIPaymentReceiptAt
    (standing : ConcreteStanding)
    (code : exitRelationCompiler.FutureCode) : Type where
  private mk ::
  standing_eq : standing = exitCapacityProgram.purchasingPowerStanding
  code_eq : code = ExitFutureCode.leave
  eventTrace : ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
    residualConsumerCompiler.activationSeedAt
      Lifecycle.actualEventGame.source state
      (PurchasingPowerStandingAt.renewalEvent standing)
  nextGenerated_eq : exitCapacityProgram.payment.nextGenerated =
    PurchasingPowerStandingAt.nextGeneratedState standing

namespace SourceBackedUBIPaymentReceiptAt

/-- Sole exact producer for the UBI payment incidence. -/
def generate : SourceBackedUBIPaymentReceiptAt
    exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave where
  standing_eq := rfl
  code_eq := rfl
  eventTrace := exitCapacityProgram.payment_event_mem_source_trace
  nextGenerated_eq := exitCapacityProgram.payment_next_is_exact_generated

end SourceBackedUBIPaymentReceiptAt

/-- A route receipt retains the exact position-indexed crossing, both endpoint
incidences, and the source boundary classifier that opened the route. -/
structure SourceGeneratedUBIRouteReceiptAt
    (code : exitRelationCompiler.FutureCode)
    (crossing : ConcreteCrossing) : Type where
  private mk ::
  code_eq : code = ExitFutureCode.leave
  crossing_mem : crossing ∈
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.crossingTrace
  origin_incidence :
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.SiteSeedAt
      LocalGame.source crossing.state
      (M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.originSeedAt
        crossing)
  target_incidence :
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.SiteSeedAt
      LocalGame.source crossing.state
      (M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.targetSeedAt
        crossing)
  boundaryActive :
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.BoundaryActiveAt
      crossing
  boundaryClassified :
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.classifyBoundary
      crossing = Sum.inl boundaryActive

namespace SourceGeneratedUBIRouteReceiptAt

/-- Sole route producer; every receipt is computed from one exact crossing. -/
def generate (crossing : ConcreteCrossing) :
    SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave crossing where
  code_eq := rfl
  crossing_mem :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.exactCrossing_mem
      crossing
  origin_incidence :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.originSeedIncidence
      crossing
  target_incidence :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.targetSeedIncidence
      crossing
  boundaryActive := PUnit.unit
  boundaryClassified := rfl

end SourceGeneratedUBIRouteReceiptAt

/-- Pre-emitter source facts for the fixed tenure-capture policy failure.
There is no temporal payment/service result, capacity, exit emptiness,
effectiveness verdict, or repair result in this carrier. -/
structure SourceTenureCaptureFailure : Prop where
  private mk ::
  captured : fullCapture.Captures ExitFutureCode.leave
  paymentPurpose : ExactTenurePaymentPurposeAt
  tenureInterest : essentialAccessRelationCompiler.GeneratedInterestAt
    tenureActor tenureRelation
  tenureActorIsCounterparty :
    tenureActor = Money.exactCounterpartyActor exactResidualActivation
  tenurePhase : essentialAccessRelationCompiler.phaseStep tenureRelation =
    .tenure
  tenureRole : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target .tenureProvider

namespace SourceTenureCaptureFailure

/-- Sole source producer. -/
theorem generate : SourceTenureCaptureFailure where
  captured := rfl
  paymentPurpose := exactTenurePaymentPurpose
  tenureInterest := M14EssentialAccessRelationFixture.tenureInterest
  tenureActorIsCounterparty := tenure_actor_is_exact_payment_counterparty
  tenurePhase := tenure_phase_is_generated
  tenureRole := ⟨M14EssentialAccessRelationFixture.tenureInterest, rfl⟩

end SourceTenureCaptureFailure

/-- Applied ordinary policy disposition installed before emission.  Its type
indices are the exact captured source program, repaired no-capture target,
and compiler-generated repair.  Outcome capacity is deliberately absent. -/
structure SourceAppliedTenureCaptureRepairAt
    (sourceProgram : ConcreteCapturedProgramType)
    (targetProgram : ConcreteProgramType)
    (repair : ExactExitRepair) : Type where
  private mk ::
  sourceFailure : SourceTenureCaptureFailure
  repair_eq : repair =
    exactExitRepairCompiler.compile ExactExitFailureKind.tenureCapture
  target_uncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  payment_preserved : sourceProgram.payment = targetProgram.payment
  standing_preserved : sourceProgram.purchasingPowerStanding =
    targetProgram.purchasingPowerStanding
  employmentLoss_preserved : sourceProgram.employmentLoss =
    targetProgram.employmentLoss
  exitInterest_preserved : sourceProgram.exitInterest =
    targetProgram.exitInterest

abbrev ExactSourceAppliedTenureCaptureRepair :=
  SourceAppliedTenureCaptureRepairAt capturedProgram exitCapacityProgram
    ExactExitRepair.removeCapture

namespace SourceAppliedTenureCaptureRepairAt

/-- Sole applied-disposition producer. -/
def generate : ExactSourceAppliedTenureCaptureRepair where
  sourceFailure := SourceTenureCaptureFailure.generate
  repair_eq := rfl
  target_uncaptured := by simp [noCapture]
  payment_preserved := rfl
  standing_preserved := rfl
  employmentLoss_preserved := rfl
  exitInterest_preserved := rfl

/-- Repair readout from the disposition's type index. -/
def repairAt
    {sourceProgram : ConcreteCapturedProgramType}
    {targetProgram : ConcreteProgramType}
    {repair : ExactExitRepair}
    (_disposition : SourceAppliedTenureCaptureRepairAt
      sourceProgram targetProgram repair) : ExactExitRepair :=
  repair

/-- Repaired target program from the disposition's type index. -/
def targetProgramAt
    {sourceProgram : ConcreteCapturedProgramType}
    {targetProgram : ConcreteProgramType}
    {repair : ExactExitRepair}
    (_disposition : SourceAppliedTenureCaptureRepairAt
      sourceProgram targetProgram repair) : ConcreteProgramType :=
  targetProgram

end SourceAppliedTenureCaptureRepairAt

/-- Exact pre-emitter restriction.  The program and the two receipt families
and repair compiler are type indices rather than replaceable fields.  The
only stored datum is the incidence of this restriction at the recurrent
process's focal source seed; the applied repair is carried separately by the
root payload disposition. -/
structure UBIRootRestrictionAt
    (program : ConcreteProgramType)
    (PaysForAt : ConcreteStanding →
      exitRelationCompiler.FutureCode → Type)
    (RoutesAt : exitRelationCompiler.FutureCode →
      ConcreteCrossing → Type)
    (repairCompiler : SourceOwnedExitRepairCompiler)
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) : Type where
  private mk ::
  seed_eq : seed = M10OccurrenceCapacityProcessFixture.focalSeed

abbrev ExactUBIRootRestrictionAt := UBIRootRestrictionAt
  exitCapacityProgram SourceBackedUBIPaymentReceiptAt
    SourceGeneratedUBIRouteReceiptAt exactExitRepairCompiler

/-- The sole source restriction; it contains no completed UBI verdict. -/
def sourceGeneratedUBIRootRestriction :
    ExactUBIRootRestrictionAt M10OccurrenceCapacityProcessFixture.focalSeed :=
  ⟨rfl⟩

namespace UBIRootRestrictionAt

/-- Source program fixed by the restriction's type index. -/
def programAt
    {program : ConcreteProgramType}
    {PaysForAt : ConcreteStanding →
      exitRelationCompiler.FutureCode → Type}
    {RoutesAt : exitRelationCompiler.FutureCode → ConcreteCrossing → Type}
    {repairCompiler : SourceOwnedExitRepairCompiler}
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    (_restriction : UBIRootRestrictionAt program PaysForAt RoutesAt
      repairCompiler seed) : ConcreteProgramType :=
  program

/-- Apply the exact compiler fixed by the restriction's type index.  The
restriction stores no repair result or outcome. -/
def repairAt
    {program : ConcreteProgramType}
    {PaysForAt : ConcreteStanding →
      exitRelationCompiler.FutureCode → Type}
    {RoutesAt : exitRelationCompiler.FutureCode → ConcreteCrossing → Type}
    {repairCompiler : SourceOwnedExitRepairCompiler}
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    (_restriction : UBIRootRestrictionAt program PaysForAt RoutesAt
      repairCompiler seed)
    (failure : repairCompiler.FailureKind) : repairCompiler.Repair :=
  repairCompiler.compile failure

end UBIRootRestrictionAt

/-- Eligibility labels are observer readouts and cannot alter the restriction
installed in the root inventory. -/
def administrativeEligibilityReadout (_label : Bool) :
    ExactUBIRootRestrictionAt M10OccurrenceCapacityProcessFixture.focalSeed :=
  sourceGeneratedUBIRootRestriction

@[simp] theorem administrative_labels_do_not_control_renewal :
    administrativeEligibilityReadout false =
      administrativeEligibilityReadout true :=
  rfl

abbrev UBIConsumerAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  ExactUBIRootRestrictionAt seed

abbrev UBIDispositionAt
    (_seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  ExactSourceAppliedTenureCaptureRepair

/-- Exact action-bearing disposition installed in the UBI projection. -/
def sourceGeneratedUBIDisposition :
    UBIDispositionAt M10OccurrenceCapacityProcessFixture.focalSeed :=
  SourceAppliedTenureCaptureRepairAt.generate

end
end M14UBIProofCarryingRootRestriction
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBIProofCarryingRootRestriction.SourceAppliedTenureCaptureRepairAt.generate

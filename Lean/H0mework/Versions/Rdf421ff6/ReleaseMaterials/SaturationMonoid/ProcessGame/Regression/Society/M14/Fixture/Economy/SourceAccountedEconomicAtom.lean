import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.PeriodicMandatePowerRenewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRegression

/-!
# M14 source-accounted economic atoms

An economic atom is not an economic AST node.  Its event carrier is only a
dependent sum of an already generated clean failure origin, or that same
origin paired with the existing private proof-carrying repair.  A private
atom then anchors the event to the mandate coordinate and exact compiler
occurrence at its temporal depth.

The atom stores no capacity, failure-kind readout, repair value,
effectiveness verdict, price, utility, root row, whole-ledger write-back,
generated next, periodic table, or completed future.  Row, ledger, and next
authority are always reread from the installed mandate/root compiler.  A
later fold module seals one of these anchors behind private evidence before
using it as the `RootedAccountedUnfolding` generator; it needs no economic
syntax or second fold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceAccountedEconomicAtom

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14PeriodicMandatePowerRenewal

/-! ## Existing source events, not an economic syntax -/

/-- A clean source failure together with its exact temporal depth.  The
origin contains no capacity, exit-emptiness, or repair outcome. -/
abbrev EconomicFailureEvent :=
  Sigma fun depth : Nat => RepairFailureOriginAt depth

/-- A repair event exists only when the existing private proof-carrying
producer has generated the canonical repair for the same clean origin. -/
abbrev EconomicRepairEvent :=
  Sigma fun failure : EconomicFailureEvent =>
    PLift (SourceGeneratedProofCarryingExitRepairAt failure.2
      (canonicalRepairAt failure.2))

/-- The event carrier reuses `Sum`; it adds no domain-specific constructor
language. -/
abbrev EconomicEvent := EconomicFailureEvent ⊕ EconomicRepairEvent

namespace EconomicEvent

def failure : EconomicEvent → EconomicFailureEvent
  | .inl failure => failure
  | .inr repair => repair.1

def depth (event : EconomicEvent) : Nat :=
  event.failure.1

def origin (event : EconomicEvent) : RepairFailureOriginAt event.depth :=
  event.failure.2

end EconomicEvent

def failureEvent {depth : Nat}
    (origin : RepairFailureOriginAt depth) : EconomicEvent :=
  .inl ⟨depth, origin⟩

def repairEvent {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) : EconomicEvent :=
  .inr ⟨⟨depth, origin⟩, ⟨proof⟩⟩

@[simp] theorem failureEvent_depth {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    (failureEvent origin).depth = depth :=
  rfl

@[simp] theorem failureEvent_origin {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    (failureEvent origin).origin = origin :=
  rfl

@[simp] theorem repairEvent_depth {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) :
    (repairEvent proof).depth = depth :=
  rfl

@[simp] theorem repairEvent_origin {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) :
    (repairEvent proof).origin = origin :=
  rfl

/-! ## Exact source/root anchor -/

/-- One economic event anchored to the exact actual root occurrence at its
generated temporal visit.  Mandate installation supplies the already-live
entry/row/ledger/next authority; none is copied into the atom. -/
structure SourceAccountedEconomicAtomAt (event : EconomicEvent) : Type 18 where
  private mk ::
  mandate :
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt event.depth
  rootOccurrence :
    jointRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (temporalVisitAt event.depth).current
  rootOccurrenceExact : rootOccurrence =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit (temporalVisitAt event.depth)).occurrence

namespace SourceAccountedEconomicAtomAt

/-- Failure-atom root-accounting anchor.  Its sole input is the already typed
clean source origin; capacity, cause labels, repair and root authority are not
arguments.  The origin itself remains the source producer. -/
def generateFailure {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    SourceAccountedEconomicAtomAt (failureEvent origin) where
  mandate := periodicMandatePowerRenewalAt depth
  rootOccurrence :=
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit (temporalVisitAt depth)).occurrence
  rootOccurrenceExact := rfl

/-- Repair-atom root-accounting anchor.  The only additional input is the
existing private proof generated for this exact origin and canonical repair. -/
def generateRepair {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) :
    SourceAccountedEconomicAtomAt (repairEvent proof) where
  mandate := periodicMandatePowerRenewalAt depth
  rootOccurrence :=
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit (temporalVisitAt depth)).occurrence
  rootOccurrenceExact := rfl

/-- Canonical installed repair anchor with no caller-supplied repair. -/
def generateCanonicalRepair {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    SourceAccountedEconomicAtomAt
      (repairEvent (SourceGeneratedProofCarryingExitRepairAt.generate origin)) :=
  generateRepair (SourceGeneratedProofCarryingExitRepairAt.generate origin)

variable {event : EconomicEvent}
variable (atom : SourceAccountedEconomicAtomAt event)

def visit (_atom : SourceAccountedEconomicAtomAt event) :
    SourceNativeTemporalVisitAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  temporalVisitAt event.depth

def exactTemporalRootEvent : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot atom.visit :=
  jointRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt atom.visit

def installedMandate :
    SourceInstalledRenewalAt mandateRecognition atom.visit :=
  atom.mandate.installed

def installedUBI : SourceInstalledRenewalAt ubiRecognition atom.visit :=
  installedUBIAt event.depth

def sourceEntry := atom.installedMandate.payload.sourceEntry

def sourceSelectedRow := atom.installedMandate.payload.selectedRow

def temporalSelectedRow := atom.installedMandate.temporalSelectedRow

def wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot.source.source
      atom.exactTemporalRootEvent.occurrence :=
  atom.exactTemporalRootEvent.wholeLedgerWriteBack

def generatedNext : SourceNativeAuthoritativeRootCurrentAt
    M9ProofCarryingRenewalInquiryRoot.N :=
  atom.mandate.generatedNext

/-! ## Exact provenance readouts -/

@[simp] theorem visit_eq :
    atom.visit = temporalVisitAt event.depth :=
  rfl

@[simp] theorem exactTemporalRootEvent_eq :
    atom.exactTemporalRootEvent =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt (temporalVisitAt event.depth)) :=
  rfl

theorem rootOccurrence_eq_exactTemporal :
    atom.rootOccurrence = atom.exactTemporalRootEvent.occurrence := by
  exact atom.rootOccurrenceExact

theorem origin_payment_is_exactTemporalRootEvent :
    (periodicSourceBackedPaymentAt event.depth).rootOccurrence =
      atom.exactTemporalRootEvent := by
  exact event.origin.exactTemporalPayment

@[simp] theorem sourceEntry_eq_rootEntry :
    atom.sourceEntry = RootInquiryU8CompletionRegression.entry :=
  atom.mandate.sourceEntryExact

theorem sourceSelectedRow_heq_ubi :
    HEq atom.sourceSelectedRow atom.installedUBI.payload.selectedRow :=
  atom.mandate.selectedRowShared

theorem successor_heq_ubi :
    HEq atom.installedMandate.payload.successor
      atom.installedUBI.payload.successor :=
  atom.mandate.successorShared

theorem wholeLedgerWriteBack_eq :
    atom.wholeLedgerWriteBack =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit atom.visit).wholeLedgerWriteBack := by
  rfl

theorem rootAnswerAndNext_factorizes :
    atom.installedMandate.RootAnswerAndNextFactorizes :=
  atom.mandate.rootFactorization

@[simp] theorem generatedNext_eq :
    atom.generatedNext = jointRoot.generatedNextCurrentAt atom.visit :=
  atom.mandate.generatedNextExact

/-! ## Failure/repair same-authority theorem -/

def CanonicalRepairSharesRootAuthorityAt {depth : Nat}
    (origin : RepairFailureOriginAt depth) : Prop :=
  let failure := generateFailure origin
  let repair := generateCanonicalRepair origin
  failure.visit = repair.visit ∧
    failure.rootOccurrence = repair.rootOccurrence ∧
    failure.sourceEntry = repair.sourceEntry ∧
    HEq failure.sourceSelectedRow repair.sourceSelectedRow ∧
    failure.wholeLedgerWriteBack = repair.wholeLedgerWriteBack ∧
    failure.generatedNext = repair.generatedNext

theorem canonicalRepair_same_root_authority {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    CanonicalRepairSharesRootAuthorityAt origin :=
  ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl⟩

/-! ## Heterogeneous cross-visit occurrence identity -/

abbrev AnyExactRootOccurrence := ExactTemporalCausalRootEvent
  jointRoot.toAuthoritativeRoot.toLedgerRoot

def erasedRootOccurrence : AnyExactRootOccurrence :=
  ⟨atom.visit, atom.exactTemporalRootEvent⟩

theorem erasedRootOccurrence_ne_of_depth_ne
    {leftEvent rightEvent : EconomicEvent}
    (left : SourceAccountedEconomicAtomAt leftEvent)
    (right : SourceAccountedEconomicAtomAt rightEvent)
    (depth_ne : leftEvent.depth ≠ rightEvent.depth) :
    left.erasedRootOccurrence ≠ right.erasedRootOccurrence := by
  intro equality
  have visit_eq := congrArg Sigma.fst equality
  exact depth_ne (temporalVisitAt_injective visit_eq)

/-! ## No verdict or future storage -/

theorem atom_has_no_economic_verdict_or_future_fields : True := by
  fail_if_success exact atom.capacity
  fail_if_success exact atom.failureKind
  fail_if_success exact atom.repair
  fail_if_success exact atom.effectiveness
  fail_if_success exact atom.outcome
  fail_if_success exact atom.periodicTable
  fail_if_success exact atom.completedFuture
  trivial

end SourceAccountedEconomicAtomAt

/-! ## Canonical fixed events for the later unfolding consumer -/

def tenureFailureAtomAt (depth : Nat) :
    SourceAccountedEconomicAtomAt
      (failureEvent (tenureCaptureOriginAt depth)) :=
  SourceAccountedEconomicAtomAt.generateFailure
    (tenureCaptureOriginAt depth)

def routeFailureAtomAt (depth : Nat) :
    SourceAccountedEconomicAtomAt
      (failureEvent (routeBottleneckOriginAt depth)) :=
  SourceAccountedEconomicAtomAt.generateFailure
    (routeBottleneckOriginAt depth)

def tenureRepairAtomAt (depth : Nat) :
    SourceAccountedEconomicAtomAt
      (repairEvent (SourceGeneratedProofCarryingExitRepairAt.generate
        (tenureCaptureOriginAt depth))) :=
  SourceAccountedEconomicAtomAt.generateCanonicalRepair
    (tenureCaptureOriginAt depth)

def routeRepairAtomAt (depth : Nat) :
    SourceAccountedEconomicAtomAt
      (repairEvent (SourceGeneratedProofCarryingExitRepairAt.generate
        (routeBottleneckOriginAt depth))) :=
  SourceAccountedEconomicAtomAt.generateCanonicalRepair
    (routeBottleneckOriginAt depth)

end
end M14SourceAccountedEconomicAtom
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceAccountedEconomicAtom.SourceAccountedEconomicAtomAt.generateFailure
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceAccountedEconomicAtom.SourceAccountedEconomicAtomAt.generateRepair
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceAccountedEconomicAtom.SourceAccountedEconomicAtomAt.canonicalRepair_same_root_authority
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceAccountedEconomicAtom.SourceAccountedEconomicAtomAt.erasedRootOccurrence_ne_of_depth_ne

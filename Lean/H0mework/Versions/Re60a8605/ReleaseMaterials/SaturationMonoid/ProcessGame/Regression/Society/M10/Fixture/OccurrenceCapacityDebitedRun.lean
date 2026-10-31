import H0mework.Foundation.Responsibility.ResponsibilityCapacityKernel

/-!
# Two-step actual debit fixture for M10

This regression-only process performs two genuine maintenance occurrences on
one live responsibility.  Its source-owned budget is two, its target budget
is zero, and each decrement is tied to the exact lifecycle edge.  M10 uses
it only downstream of the independently generated critical phase.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10OccurrenceCapacityDebitedRunFixture

open ResponsibilityLifecycle
open ComplementObservation

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := PUnit
  Content := PUnit
  Residual := PUnit
  Bearer := PUnit
  ProtectedInterest := PUnit
  Scope := PUnit
  Lineage := PUnit
  Incidence := PUnit
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun _ => MinimalRegistrableSourceAnchor.canonical () ()
  sourceIncidence := fun _ => ()
  ObstructionAt := fun _ => PUnit
  demandContent := fun _ => ()
  demandResidual := fun _ => ()
  CommitmentAt := fun _ _ => PUnit
  MandateOriginAt := fun _ _ => PUnit
  AcceptedTaskAt := fun _ _ => PUnit
  ActiveDependencyAt := fun _ _ => PUnit
  ProtectedRiskAt := fun _ _ => PUnit
  AdmissionAuthorityAt := fun _ _ => PUnit
  AcceptedAt := fun _ _ _ => PUnit
  StandingMandateAt := fun _ _ _ => PUnit
  DischargeJurisdiction := fun _ _ => PUnit
  ProgressAt := fun _ _ _ _ => PUnit
  MaintenanceAt := fun _ _ _ => PUnit
  TypedDeferAt := fun _ _ _ => PUnit
  ScopeNarrowingAt := fun _ _ _ => PUnit
  TransferAcceptedAt := fun _ _ _ _ => PUnit
  FulfilledAt := fun _ _ _ => PUnit
  WaivedAt := fun _ _ _ => PUnit
  InvalidatedAt := fun _ _ _ => PUnit
  AbandonedAt := fun _ _ _ => PUnit
  ImpossibleResidueAcceptedAt := fun _ _ _ => PUnit
  SupersessionAt := fun _ _ _ _ _ _ _ => PUnit
  ReopenAt := fun _ _ _ _ _ _ _ => PUnit
  JurisdictionEndedAt := fun _ _ _ => PUnit
  ConsentRevokedAt := fun _ _ _ => PUnit
  CapacityReleasedAt := fun _ _ _ => PUnit
  UpperRouteAt := fun _ _ _ => PUnit
  NextActorSignal := PUnit
  AgeSignal := PUnit
  TransferOfferSignal := PUnit

abbrev V := vocabulary

def admissionPayload : NativeAdmissionPayload V where
  sourceEvent := ()
  content := ()
  residual := ()
  bearer := ()
  beneficiary := ()
  scope := ()
  lineage := ()
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def process : NativeResponsibilityProcess V where
  AdmissionEvent := PUnit
  admissionPayload := fun _ => admissionPayload
  BoundaryEvent := fun _ => PUnit
  boundarySource := fun _ => ()
  boundary_anchor_eq := fun _ => rfl
  boundary_incidence_eq := fun _ => rfl
  boundaryDisposition := fun _ => .carry (.maintained ())
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun event => nomatch event

abbrev P := process

def emptyState : ResponsibilityState V := ResponsibilityState.empty V

def admissionEdge : P.Edge emptyState := .admit ()

def sourceState : ResponsibilityState V := admissionEdge.target

def sourceSlot : Fin sourceState.slots.length :=
  ⟨0, by simp [sourceState, admissionEdge, emptyState,
    NativeResponsibilityProcess.Edge.target]⟩

theorem sourcePresent :
    sourceState.slots.get sourceSlot = .live admissionPayload.toObligation :=
  rfl

def firstMaintenance : P.Edge sourceState :=
  .cross sourceSlot admissionPayload.toObligation sourcePresent ()

def middleSlot : Fin firstMaintenance.target.slots.length :=
  ⟨0, by simp [firstMaintenance, sourceState, admissionEdge, emptyState,
    NativeResponsibilityProcess.Edge.target]⟩

theorem middlePresent :
    firstMaintenance.target.slots.get middleSlot =
      .live admissionPayload.toObligation :=
  rfl

def secondMaintenance : P.Edge firstMaintenance.target :=
  .cross middleSlot admissionPayload.toObligation middlePresent ()

/-- Budget is generated from the actual lifecycle history: two at the
admitted source, one after the first maintenance, zero after the second. -/
def budgetAt (state : ResponsibilityState V) (_lineage : V.Lineage) : Nat :=
  3 - state.history.length

@[simp] theorem source_budget_eq_two : budgetAt sourceState () = 2 := rfl

@[simp] theorem middle_budget_eq_one :
    budgetAt firstMaintenance.target () = 1 := rfl

@[simp] theorem target_budget_eq_zero :
    budgetAt secondMaintenance.target () = 0 := rfl

def firstDebit : ActualMaintenanceDebit P budgetAt firstMaintenance () where
  slot := 0
  obligation := admissionPayload.toObligation
  sourceEvent := ()
  receipt := ()
  event_eq := rfl
  source_live := rfl
  target_live := rfl
  lineage_eq := rfl
  strict_debit := by decide

def secondDebit : ActualMaintenanceDebit P budgetAt secondMaintenance () where
  slot := 0
  obligation := admissionPayload.toObligation
  sourceEvent := ()
  receipt := ()
  event_eq := rfl
  source_live := rfl
  target_live := rfl
  lineage_eq := rfl
  strict_debit := by decide

inductive DebitEvent :
    {source : ResponsibilityState V} → P.Edge source → V.Lineage → Type
  | first : DebitEvent firstMaintenance ()
  | second : DebitEvent secondMaintenance ()

def debitProcess : NativeCarryDebitProcess P where
  budgetAt := budgetAt
  DebitEvent := DebitEvent
  debitReceipt := by
    intro source edge lineage event
    cases event with
    | first => exact firstDebit
    | second => exact secondDebit

def run : P.Run sourceState secondMaintenance.target :=
  .step (.step .nil firstMaintenance) secondMaintenance

@[simp] theorem run_events_length : run.events.length = 2 := rfl

def debited : NativeDebitedRun P debitProcess () run :=
  .step
    (.step (.nil sourceState) firstMaintenance
      M10OccurrenceCapacityDebitedRunFixture.DebitEvent.first)
    secondMaintenance
      M10OccurrenceCapacityDebitedRunFixture.DebitEvent.second

theorem actual_run_exhausts_budget :
    debitProcess.budgetAt secondMaintenance.target () = 0 :=
  NativeDebitedRun.targetBudget_eq_zero_of_events_length_eq_sourceBudget
    debited rfl

end M10OccurrenceCapacityDebitedRunFixture
end Society
end ProcessGame
end SaturationMonoid

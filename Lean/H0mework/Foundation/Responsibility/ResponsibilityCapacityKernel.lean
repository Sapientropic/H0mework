import H0mework.Foundation.Responsibility.Lineage

/-!
# Capacity obstruction and finite carrying budget

Capacity shortage is generated from an actual readout.  It is not interpreted
as discharge, and it does not select a downstream branch.  `StrictBudgetRun`
is the lower arithmetic consumer; `NativeDebitedRun` connects it to an exact
lifecycle run, concrete maintained obligation, stable slot, debt lineage, and
source-owned debit event.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle

universe u

structure CapacityVocabulary (V : Vocabulary.{u}) where
  IncompatibleDemand : Type u
  AffectedDependency : Type u
  ProtectedBoundary : Type u

/-- Actual capacity readout.  All affected obligations and protected
boundaries remain visible when capacity is insufficient. -/
structure CapacityReadout (V : Vocabulary.{u})
    (C : CapacityVocabulary V) : Type u where
  sourceEvent : V.SourceEvent
  bearer : V.Bearer
  admitted : List (AdmittedObligation V)
  demandedCapacity : Nat
  availableCapacity : Nat
  incompatibleDemands : List C.IncompatibleDemand
  affectedDependencies : List C.AffectedDependency
  protectedBoundaries : List C.ProtectedBoundary

/-- Capacity obstruction is the positive shortage witness generated from one
exact readout.  It contains no prioritization, transfer, narrowing, or exit
choice. -/
structure CapacityObstruction
    {V : Vocabulary.{u}} {C : CapacityVocabulary V}
    (readout : CapacityReadout V C) : Type where
  shortage : readout.availableCapacity < readout.demandedCapacity

def CapacityReadout.obstruction?
    {V : Vocabulary.{u}} {C : CapacityVocabulary V}
    (readout : CapacityReadout V C) : Option (CapacityObstruction readout) :=
  if shortage : readout.availableCapacity < readout.demandedCapacity then
    some ⟨shortage⟩
  else
    none

theorem CapacityReadout.obstruction?_eq_some_iff
    {V : Vocabulary.{u}} {C : CapacityVocabulary V}
    (readout : CapacityReadout V C) :
    (∃ obstruction, readout.obstruction? = some obstruction) ↔
      readout.availableCapacity < readout.demandedCapacity := by
  constructor
  · rintro ⟨obstruction, produced⟩
    simp only [CapacityReadout.obstruction?] at produced
    split at produced
    · assumption
    · cases produced
  · intro shortage
    refine ⟨⟨shortage⟩, ?_⟩
    simp [CapacityReadout.obstruction?, shortage]

theorem CapacityReadout.obstruction?_eq_none_iff
    {V : Vocabulary.{u}} {C : CapacityVocabulary V}
    (readout : CapacityReadout V C) :
    readout.obstruction? = none ↔
      readout.demandedCapacity ≤ readout.availableCapacity := by
  simp [CapacityReadout.obstruction?]

/-- A domain process owns the actual capacity event and its readout. -/
structure NativeCapacityProcess (V : Vocabulary.{u})
    (C : CapacityVocabulary V) : Type (u + 1) where
  CapacityEvent : Type u
  readout : CapacityEvent → CapacityReadout V C

def NativeCapacityProcess.obstruction?
    {V : Vocabulary.{u}} {C : CapacityVocabulary V}
    (process : NativeCapacityProcess V C) (event : process.CapacityEvent) :
    Option (CapacityObstruction (process.readout event)) :=
  (process.readout event).obstruction?

/-- One source-owned debit for one exact lifecycle edge.  The event equality
prevents a numeric decrement from being detached from the concrete maintained
obligation, stable slot, and lineage that produced it. -/
structure ActualMaintenanceDebit
    {V : Vocabulary.{u}} (P : NativeResponsibilityProcess V)
    (budgetAt : ResponsibilityState V → V.Lineage → Nat)
    {source : ResponsibilityState V} (edge : P.Edge source)
    (lineage : V.Lineage) : Type u where
  slot : Nat
  obligation : AdmittedObligation V
  sourceEvent : V.SourceEvent
  receipt : V.MaintenanceAt sourceEvent obligation.content obligation.scope
  event_eq : edge.lifecycleEvent =
    .carried slot obligation sourceEvent (.maintained receipt)
  source_live : source.slots[slot]? = some (.live obligation)
  target_live : edge.target.slots[slot]? = some (.live obligation)
  lineage_eq : obligation.lineage = lineage
  strict_debit : budgetAt edge.target lineage < budgetAt source lineage

/-- The debit event cannot be detached from the exact source anchor and
responsibility incidence carried by the lifecycle boundary that generated
it.  This is derived from `event_eq`; it is not an extra domain premise. -/
def ActualMaintenanceDebit.sourceOwnership
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {budgetAt : ResponsibilityState V → V.Lineage → Nat}
    {source : ResponsibilityState V} {edge : P.Edge source}
    {lineage : V.Lineage}
    (debit : ActualMaintenanceDebit P budgetAt edge lineage) :
    SourceOwnsResponsibilityIncidence V debit.sourceEvent debit.obligation := by
  rcases debit with
    ⟨slot, obligation, sourceEvent, receipt, event_eq, source_live,
      target_live, lineage_eq, strict_debit⟩
  cases edge with
  | admit event =>
      simp [NativeResponsibilityProcess.Edge.lifecycleEvent] at event_eq
  | reopen edgeSlot archive present event =>
      simp [NativeResponsibilityProcess.Edge.lifecycleEvent] at event_eq
  | cross edgeSlot edgeObligation present event =>
      cases disposition_eq : P.boundaryDisposition event with
      | carry disposition =>
          cases disposition with
          | progressed nextResidual progressReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.carried edgeSlot.val edgeObligation
                  (P.boundarySource event)
                  (.progressed nextResidual progressReceipt) =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
          | progressedAndTransferred nextResidual nextBearer progressReceipt
              transferReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.carried edgeSlot.val edgeObligation
                  (P.boundarySource event)
                  (.progressedAndTransferred nextResidual nextBearer
                    progressReceipt transferReceipt) =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
          | maintained maintenanceReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.carried edgeSlot.val edgeObligation
                  (P.boundarySource event) (.maintained maintenanceReceipt) =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
              exact ⟨P.boundary_anchor_eq event,
                P.boundary_incidence_eq event⟩
          | deferred deferReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.carried edgeSlot.val edgeObligation
                  (P.boundarySource event) (.deferred deferReceipt) =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
          | narrowed nextScope narrowingReceipt jurisdiction =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.carried edgeSlot.val edgeObligation
                  (P.boundarySource event)
                  (.narrowed nextScope narrowingReceipt jurisdiction) =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
          | transferred nextBearer transferReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.carried edgeSlot.val edgeObligation
                  (P.boundarySource event)
                  (.transferred nextBearer transferReceipt) =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
      | terminal terminalReceipt =>
          cases terminalReceipt with
          | final finalReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.terminal edgeSlot.val edgeObligation
                  (P.boundarySource event) finalReceipt =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
          | superseded supersessionReceipt =>
              rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
                disposition_eq] at event_eq
              change LifecycleEvent.superseded edgeSlot.val edgeObligation
                  (P.boundarySource event) supersessionReceipt =
                LifecycleEvent.carried slot obligation sourceEvent
                  (.maintained receipt) at event_eq
              cases event_eq
      | bearerRelease releaseReceipt =>
          rw [NativeResponsibilityProcess.Edge.lifecycleEvent,
            disposition_eq] at event_eq
          change LifecycleEvent.bearerReleased edgeSlot.val edgeObligation
              (P.boundarySource event) releaseReceipt =
            LifecycleEvent.carried slot obligation sourceEvent
              (.maintained receipt) at event_eq
          cases event_eq

/-- A domain process owns both the budget readout and the event family that
can generate an actual maintenance debit.  A caller cannot turn a bare
decreasing natural-number chain into a lifecycle debit. -/
structure NativeCarryDebitProcess
    {V : Vocabulary.{u}} (P : NativeResponsibilityProcess V) : Type (u + 1) where
  budgetAt : ResponsibilityState V → V.Lineage → Nat
  DebitEvent :
    {source : ResponsibilityState V} → P.Edge source → V.Lineage → Type u
  debitReceipt :
    {source : ResponsibilityState V} → {edge : P.Edge source} →
      {lineage : V.Lineage} → DebitEvent edge lineage →
        ActualMaintenanceDebit P budgetAt edge lineage

/-- A finite sequence of genuinely nontrivial unchanged carries.  Every step
strictly debits the remaining budget. -/
inductive StrictBudgetRun (start : Nat) : Nat → Type
  | nil : StrictBudgetRun start start
  | step {middle target : Nat}
      (prior : StrictBudgetRun start middle)
      (debit : target < middle) : StrictBudgetRun start target

def StrictBudgetRun.length
    {start target : Nat} (run : StrictBudgetRun start target) : Nat :=
  match run with
  | .nil => 0
  | .step prior _ => prior.length + 1

/-- Independent liveness consumer: an unchanged-carry run plus its remaining
budget cannot be longer than the initial budget. -/
theorem StrictBudgetRun.length_add_target_le_start
    {start target : Nat} (run : StrictBudgetRun start target) :
    run.length + target ≤ start := by
  induction run with
  | nil => simp [StrictBudgetRun.length]
  | step prior debit ih =>
      simp only [StrictBudgetRun.length]
      omega

theorem StrictBudgetRun.length_le_start
    {start target : Nat} (run : StrictBudgetRun start target) :
    run.length ≤ start := by
  exact Nat.le_trans (Nat.le_add_right run.length target)
    run.length_add_target_le_start

theorem no_strictBudgetRun_longer_than_start
    {start target : Nat} (run : StrictBudgetRun start target) :
    ¬ start < run.length :=
  Nat.not_lt_of_ge run.length_le_start

/-- An exact lifecycle run whose every edge is accompanied by a debit event
generated by the same source-owned debit process. -/
inductive NativeDebitedRun
    {V : Vocabulary.{u}} (P : NativeResponsibilityProcess V)
    (B : NativeCarryDebitProcess P) (lineage : V.Lineage) :
    {source target : ResponsibilityState V} → P.Run source target → Type u
  | nil (state : ResponsibilityState V) :
      NativeDebitedRun P B lineage (.nil : P.Run state state)
  | step
      {source middle : ResponsibilityState V}
      {prior : P.Run source middle}
      (debited : NativeDebitedRun P B lineage prior)
      (edge : P.Edge middle)
      (debit : B.DebitEvent edge lineage) :
      NativeDebitedRun P B lineage (.step prior edge)

def NativeDebitedRun.toStrictBudgetRun
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run) :
    StrictBudgetRun (B.budgetAt source lineage) (B.budgetAt target lineage) :=
  match debited with
  | .nil _ => .nil
  | .step prior edge debit =>
      .step prior.toStrictBudgetRun (B.debitReceipt debit).strict_debit

def NativeDebitedRun.length
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run) : Nat :=
  match debited with
  | .nil _ => 0
  | .step prior _ _ => prior.length + 1

theorem NativeDebitedRun.toStrictBudgetRun_length
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run) :
    debited.toStrictBudgetRun.length = debited.length := by
  induction debited with
  | nil => rfl
  | step prior edge debit ih =>
      simp only [NativeDebitedRun.toStrictBudgetRun,
        StrictBudgetRun.length, NativeDebitedRun.length, ih]

theorem NativeDebitedRun.length_eq_run_events_length
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run) :
    debited.length = run.events.length := by
  induction debited with
  | nil => rfl
  | step prior edge debit ih =>
      simp [NativeDebitedRun.length, NativeResponsibilityProcess.Run.events, ih]

/-- Independent liveness consumer on the actual lifecycle run: its number of
generated maintenance events plus the remaining target budget is bounded by
the source-owned budget at the exact source. -/
theorem NativeDebitedRun.events_length_add_targetBudget_le_sourceBudget
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run) :
    run.events.length + B.budgetAt target lineage ≤
      B.budgetAt source lineage := by
  rw [← debited.length_eq_run_events_length,
    ← debited.toStrictBudgetRun_length]
  exact debited.toStrictBudgetRun.length_add_target_le_start

theorem NativeDebitedRun.no_more_events_than_sourceBudget
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run) :
    ¬ B.budgetAt source lineage < run.events.length := by
  exact Nat.not_lt_of_ge
    (Nat.le_trans (Nat.le_add_right run.events.length
      (B.budgetAt target lineage))
      debited.events_length_add_targetBudget_le_sourceBudget)

/-- At zero source-owned budget there can be no generated maintenance debit
for a further exact edge.  Such an edge cannot extend the certified
unchanged-maintenance carrier by silently manufacturing a numeric decrement. -/
theorem NativeCarryDebitProcess.no_debitEvent_of_budget_eq_zero
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    (B : NativeCarryDebitProcess P) {lineage : V.Lineage}
    {source : ResponsibilityState V}
    (zero : B.budgetAt source lineage = 0) (edge : P.Edge source) :
    IsEmpty (B.DebitEvent edge lineage) where
  false debit := by
    have strict := (B.debitReceipt debit).strict_debit
    rw [zero] at strict
    omega

/-- Spending exactly the source budget along the actual run forces its exact
target budget to zero. -/
theorem NativeDebitedRun.targetBudget_eq_zero_of_events_length_eq_sourceBudget
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run)
    (exhausted : run.events.length = B.budgetAt source lineage) :
    B.budgetAt target lineage = 0 := by
  have bound := debited.events_length_add_targetBudget_le_sourceBudget
  rw [exhausted] at bound
  omega

/-- A certified actual lifecycle run that has spent its source budget cannot
be extended by another generated maintenance debit.  Any further lifecycle
edge requires a separately generated non-maintenance disposition receipt. -/
theorem NativeDebitedRun.no_extension_of_sourceBudget_exhausted
    {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
    {B : NativeCarryDebitProcess P} {lineage : V.Lineage}
    {source target : ResponsibilityState V} {run : P.Run source target}
    (debited : NativeDebitedRun P B lineage run)
    (exhausted : run.events.length = B.budgetAt source lineage)
    (edge : P.Edge target) : IsEmpty (B.DebitEvent edge lineage) :=
  B.no_debitEvent_of_budget_eq_zero
    (debited.targetBudget_eq_zero_of_events_length_eq_sourceBudget exhausted)
    edge

end ResponsibilityLifecycle
end SaturationMonoid

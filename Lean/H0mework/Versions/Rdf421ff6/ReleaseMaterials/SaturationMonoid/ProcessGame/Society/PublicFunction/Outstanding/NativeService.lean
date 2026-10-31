import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Continuation
import H0mework.Foundation.Agency.OriginExit

/-! The registered service protocol assumes its own original task slots.
The bearer is its instruction seat, never a Party or an assigned worker.
Admission consumes the actual first root write; fulfilment consumes an
actual in-window whole-slot payment and the same task-row write.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.NativeService

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ComplementObservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

def seat : Fin (ProgrammeSource.registrationSize source.input) :=
  ⟨0, by change 0 < 1; decide⟩

def registrationTarget := ProgrammeSource.targetEntry source.input .bootstrap
  (.instruction (seat source))

/-- This receipt is indexed by the original compiler's first-write row.
Bootstrap observation receipts are not used as admission authority. -/
structure RegistrationReceipt where
  write : LedgerEntryEvolutionAt (ProgrammeSource.N source.input)
    ((ProgrammeLedger.evolution source.input .bootstrap).origin
      (registrationTarget source)).1 (registrationTarget source)
  written : write = ((ProgrammeLedger.evolution source.input .bootstrap).origin
    (registrationTarget source)).2
  inherited : ((ProgrammeLedger.evolution source.input .bootstrap).origin
    (registrationTarget source)).1 =
      ProgrammeWorld.inheritedEntry _ (ProgrammeSource.registrationSize source.input)
  debit : (registrationTarget source).progressBudget <
    (ProgrammeWorld.inheritedEntry
      (RawCurrent Party Good Technology Instrument)
      (ProgrammeSource.registrationSize source.input)).progressBudget

def registered : RegistrationReceipt source where
  write := ((ProgrammeLedger.evolution source.input .bootstrap).origin
    (registrationTarget source)).2
  written := rfl
  inherited := (ProgrammeLedger.first_origin_parent_iff source.input
    (registrationTarget source)).mpr (by intro impossible; cases impossible)
  debit := ProgrammeLedger.first_child_debit source.input (registrationTarget source)
    (by intro impossible; cases impossible)

structure Event where
  index : source.Slot
  ordinal : Nat

structure AdmissionAt (event : Event source) (index : source.Slot) where
  at_registration : event.ordinal = 0
  original_slot : event.index = index
  registration : RegistrationReceipt source

structure AssumptionAt (holder : Fin (ProgrammeSource.registrationSize source.input))
    (event : Event source) (index : source.Slot) extends AdmissionAt source event index where
  own_seat : holder = seat source

structure VisitReceipt (event : Event source) : Type where
  running : 0 < event.ordinal
  task_write : ProgrammeLedger.transferReceiptOf source.input
      (source.taskWrite (event.ordinal - 1)).2 =
    some (source.writtenReceipt (event.ordinal - 1))
  current : source.runningCurrent (event.ordinal - 1) =
    (ProgrammeHistory.visitAt source.input event.ordinal).current

def visitReceipt (index : source.Slot) (depth : Nat) :
    VisitReceipt source ⟨index, depth + 1⟩ where
  running := Nat.zero_lt_succ depth
  task_write := source.receipt_is_in_original_task_write depth
  current := source.runningCurrent_is_original_visit depth

structure FulfilledAt (event : Event source) (content scope : source.Slot) : Type where
  content_eq : content = event.index
  scope_eq : scope = event.index
  actual : VisitReceipt source event
  payment : source.ActualSlotPaid event.ordinal event.index

structure RetainedAt (event : Event source) (content scope : source.Slot) : Type where
  content_eq : content = event.index
  scope_eq : scope = event.index
  actual : VisitReceipt source event
  unpaid : ¬ source.ActualSlotPaid event.ordinal event.index

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event source
  Content := source.Slot
  Residual := Bundle Good
  Bearer := Fin (ProgrammeSource.registrationSize source.input)
  ProtectedInterest := Party
  Scope := source.Slot
  Lineage := source.Slot
  Incidence := source.Slot
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical event.index event.index
  sourceIncidence := Event.index
  ObstructionAt := fun _ => Empty
  demandContent := fun obstruction => nomatch obstruction
  demandResidual := fun obstruction => nomatch obstruction
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := AdmissionAt source
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt source
  AcceptedAt := AssumptionAt source
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun content scope => PLift (content = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := RetainedAt source
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := FulfilledAt source
  WaivedAt := fun _ _ _ => Empty
  InvalidatedAt := fun _ _ _ => Empty
  AbandonedAt := fun _ _ _ => Empty
  ImpossibleResidueAcceptedAt := fun _ _ _ => Empty
  SupersessionAt := fun _ _ _ _ _ _ _ => Empty
  ReopenAt := fun _ _ _ _ _ _ _ => Empty
  JurisdictionEndedAt := fun _ _ _ => Empty
  ConsentRevokedAt := fun _ _ _ => Empty
  CapacityReleasedAt := fun _ _ _ => Empty
  UpperRouteAt := fun _ _ _ => Empty
  NextActorSignal := Nat
  AgeSignal := Nat
  TransferOfferSignal := Empty

abbrev V := vocabulary source

def admissionPayload (index : source.Slot) : NativeAdmissionPayload (V source) where
  sourceEvent := ⟨index, 0⟩
  content := index
  residual := (source.seed.slot index).goods
  bearer := seat source
  beneficiary := (source.seed.slot index).bearer
  scope := index
  lineage := index
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask ⟨rfl, rfl, registered source⟩
  authority := ⟨rfl, rfl, registered source⟩
  assumption := .accepted ⟨⟨rfl, rfl, registered source⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (index : source.Slot) := (admissionPayload source index).toObligation

/-- The actual visit chooses the disposition; this event has no payment,
terminal, target obligation, or selected branch field. -/
structure Review (obligation : AdmittedObligation (V source)) where
  index : source.Slot
  depth : Nat
  content_eq : obligation.content = index
  scope_eq : obligation.scope = index
  admission_index : obligation.admission.sourceEvent.index = index

def review (index : source.Slot) (depth : Nat) : Review source (obligation source index) :=
  ⟨index, depth, rfl, rfl, rfl⟩

def reviewSource {obligation : AdmittedObligation (V source)}
    (event : Review source obligation) : Event source := ⟨event.index, event.depth + 1⟩

def disposition {obligation : AdmittedObligation (V source)}
    (event : Review source obligation) :
    BoundaryDisposition (V source) obligation (reviewSource source event) :=
  if paid : source.ActualSlotPaid (event.depth + 1) event.index then
    .terminal (.final (.fulfilled
      ⟨event.content_eq, event.scope_eq, visitReceipt source event.index event.depth, paid⟩))
  else .carry (.maintained
    ⟨event.content_eq, event.scope_eq, visitReceipt source event.index event.depth, paid⟩)

def process : NativeResponsibilityProcess (V source) where
  AdmissionEvent := source.Slot
  admissionPayload := admissionPayload source
  BoundaryEvent := Review source
  boundarySource := reviewSource source
  boundary_anchor_eq := by
    intro obligation event
    change MinimalRegistrableSourceAnchor.canonical event.index event.index =
      MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index
        obligation.admission.sourceEvent.index
    rw [event.admission_index]
  boundary_incidence_eq := by
    intro obligation event
    exact event.admission_index.symm
  boundaryDisposition := disposition source
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def admissionEdge (index : source.Slot) :
    (process source).Edge (ResponsibilityState.empty (V source)) := .admit index

def admittedState (index : source.Slot) := (admissionEdge source index).target

def slot (index : source.Slot) : Fin (admittedState source index).slots.length :=
  ⟨0, by simp [admittedState, admissionEdge, NativeResponsibilityProcess.Edge.target]⟩

theorem admitted_present (index : source.Slot) :
    (admittedState source index).slots.get (slot source index) =
      .live (obligation source index) := rfl

def reviewEdge (index : source.Slot) (depth : Nat) :
    (process source).Edge (admittedState source index) :=
  .cross (slot source index) (obligation source index)
    (admitted_present source index) (review source index depth)

theorem unpaid_is_still_live (index : source.Slot) (depth : Nat)
    (unpaid : ¬ source.ActualSlotPaid (depth + 1) index) :
    (reviewEdge source index depth).target.slots[0]? =
      some (.live (obligation source index)) := by
  have target := NativeResponsibilityProcess.cross_target_slot (P := process source)
    (slot source index) (obligation source index) (admitted_present source index)
      (review source index depth)
  simpa [reviewEdge, process, disposition, review, unpaid,
    BoundaryDisposition.targetSlot, ActiveCarryDisposition.target, slot] using target

theorem paid_has_terminal_receipt (index : source.Slot) (depth : Nat)
    (paid : source.ActualSlotPaid (depth + 1) index) :
    ∃ archive, (reviewEdge source index depth).target.slots[0]? = some (.terminal archive) := by
  have target := NativeResponsibilityProcess.cross_target_slot (P := process source)
    (slot source index) (obligation source index) (admitted_present source index)
      (review source index depth)
  simp only [process, disposition, review, dif_pos paid] at target
  exact ⟨_, target⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.NativeService

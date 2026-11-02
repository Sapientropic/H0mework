import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source
import H0mework.Foundation.Agency.OriginExit
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.Readback

/-! The registered service protocol assumes its own original task slots.
The bearer is its instruction seat, never a Party or an assigned worker.
Admission consumes the actual first root write; fulfilment consumes an
actual in-window whole-slot payment and the same task-row write.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ComplementObservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (inputs : List (RawEvent Party Good Port Technology Instrument))

def ActualSlotPaid (ordinal : Nat) (index : source.Slot) : Prop :=
  source.SlotPaid (OutstandingSource.History.currentAt source inputs ordinal)
    (ProgrammeSource.rawEvent (OutstandingSource.History.input source inputs)
      (ProgrammeHistory.visitAt (OutstandingSource.History.input source inputs) ordinal).current) index

instance (ordinal : Nat) (index : source.Slot) : Decidable (ActualSlotPaid source inputs ordinal index) := by
  unfold ActualSlotPaid
  infer_instance

theorem prefix_payment_is_actual (ordinal : Nat) (index : source.Slot) :
    source.SlotPaid (OutstandingSource.History.trailAt source inputs ordinal).frame.raw
      (OutstandingSource.History.word source inputs ordinal
        (OutstandingSource.History.trailAt source inputs ordinal).frame) index ↔
      ActualSlotPaid source inputs ordinal index := by
  rw [← (OutstandingSource.History.actual_frame source inputs ordinal).1,
    ← (OutstandingSource.History.actual_frame source inputs ordinal).2]
  rfl

def seat : Fin (ProgrammeSource.registrationSize (OutstandingSource.History.input source inputs)) :=
  ⟨0, by change 0 < 1; decide⟩

def registrationTarget := ProgrammeSource.targetEntry (OutstandingSource.History.input source inputs) .bootstrap
  (.instruction (seat source inputs))

/-- This receipt is indexed by the original compiler's first-write row.
Bootstrap observation receipts are not used as admission authority. -/
structure RegistrationReceipt where
  write : LedgerEntryEvolutionAt (ProgrammeSource.N (OutstandingSource.History.input source inputs))
    ((ProgrammeLedger.evolution (OutstandingSource.History.input source inputs) .bootstrap).origin
      (registrationTarget source inputs)).1 (registrationTarget source inputs)
  written : write = ((ProgrammeLedger.evolution (OutstandingSource.History.input source inputs) .bootstrap).origin
    (registrationTarget source inputs)).2
  inherited : ((ProgrammeLedger.evolution (OutstandingSource.History.input source inputs) .bootstrap).origin
    (registrationTarget source inputs)).1 =
      ProgrammeWorld.inheritedEntry _ (ProgrammeSource.registrationSize (OutstandingSource.History.input source inputs))
  debit : (registrationTarget source inputs).progressBudget <
    (ProgrammeWorld.inheritedEntry
      (RawCurrent Party Good Technology Instrument)
      (ProgrammeSource.registrationSize (OutstandingSource.History.input source inputs))).progressBudget

def registered : RegistrationReceipt source inputs where
  write := ((ProgrammeLedger.evolution (OutstandingSource.History.input source inputs) .bootstrap).origin
    (registrationTarget source inputs)).2
  written := rfl
  inherited := (ProgrammeLedger.first_origin_parent_iff (OutstandingSource.History.input source inputs)
    (registrationTarget source inputs)).mpr (by intro impossible; cases impossible)
  debit := ProgrammeLedger.first_child_debit (OutstandingSource.History.input source inputs) (registrationTarget source inputs)
    (by intro impossible; cases impossible)

/-- A later source supplies only its executable input and an actual visit.
Expiry is checked against the original task, never its replacement window. -/
structure ExpiredInput where
  nextSource : OutstandingSource Party Good Port Technology Instrument
  nextInputs : List (RawEvent Party Good Port Technology Instrument)
  depth : Nat
  expired : source.seed.task.deadline <
    (OutstandingSource.History.currentAt nextSource nextInputs (depth + 1)).clock

def ExpiredInput.actual (input : ExpiredInput source) :=
  OutstandingSource.History.actualExecution input.nextSource input.nextInputs input.depth

def ExpiredInput.read (nextSource : OutstandingSource Party Good Port Technology Instrument)
    (nextInputs : List (RawEvent Party Good Port Technology Instrument)) (depth : Nat) : Option (ExpiredInput source) :=
  if expired : source.seed.task.deadline < (OutstandingSource.History.currentAt nextSource nextInputs (depth + 1)).clock
  then some ⟨nextSource,nextInputs,depth,expired⟩ else none

structure ExpiredInput.Receipt (input : ExpiredInput source) where
  task_write : ProgrammeLedger.transferReceiptOf (OutstandingSource.History.input input.nextSource input.nextInputs)
      (OutstandingSource.History.taskWrite input.nextSource input.nextInputs input.depth).2 =
    some (OutstandingSource.History.writtenReceipt input.nextSource input.nextInputs input.depth)
  current : OutstandingSource.History.runningCurrent input.nextSource input.nextInputs input.depth =
    (ProgrammeHistory.visitAt (OutstandingSource.History.input input.nextSource input.nextInputs) (input.depth + 1)).current
  before : (input.actual source).before = OutstandingSource.History.currentAt input.nextSource input.nextInputs (input.depth + 1)
  submitted : (input.actual source).submitted = ProgrammeSource.rawEvent
    (OutstandingSource.History.input input.nextSource input.nextInputs)
    (ProgrammeHistory.visitAt (OutstandingSource.History.input input.nextSource input.nextInputs) (input.depth + 1)).current
  after : (input.actual source).after = OutstandingSource.History.currentAt input.nextSource input.nextInputs (input.depth + 2)

theorem ExpiredInput.receipt (input : ExpiredInput source) : input.Receipt source :=
  ⟨OutstandingSource.History.receipt_is_in_own_original_write _ _ _,
    OutstandingSource.History.runningCurrent_is_own_visit _ _ _,rfl,rfl,
    OutstandingSource.History.actual_next _ _ _⟩

theorem ExpiredInput.original_window_is_actually_unpayable (input : ExpiredInput source) (index : source.Slot) :
    ¬ source.SlotPaid (input.actual source).before (input.actual source).submitted index := by
  intro paid
  have monotone := source.seed.law.next_clock_nondecreasing (input.actual source).before (input.actual source).submitted
  exact (not_le_of_gt (lt_of_lt_of_le input.expired monotone)) paid.2.1

/-- Legacy periods and the richer Physical compiler are two source views;
actual requests retain their own micro/period clock. -/
inductive InputOverride
  | periods (inputs : List (RawEvent Party Good Port Technology Instrument))
  | actual (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source)
  | expired (input : ExpiredInput source)

instance : Coe (List (RawEvent Party Good Port Technology Instrument)) (InputOverride source) :=
  ⟨InputOverride.periods⟩

structure Event (inputs : List (RawEvent Party Good Port Technology Instrument)) where
  index : source.Slot
  ordinal : Nat
  inputOverride : Option (InputOverride source) := none

def Event.actualInputs (event : Event source inputs) :=
  match event.inputOverride with
  | some (.periods original) => original
  | some (.actual _) | some (.expired _) | none => inputs

def Event.Paid (event : Event source inputs) : Prop :=
  match event.inputOverride with
  | some (.actual actual) => actual.Paid event.index
  | some (.expired _) => False
  | some (.periods _) | none => ActualSlotPaid source (event.actualInputs source inputs) event.ordinal event.index

instance (event : Event source inputs) : Decidable (event.Paid source inputs) := by
  unfold Event.Paid
  split <;> infer_instance

theorem legacy_period_payment_is_unchanged (index : source.Slot) (ordinal : Nat)
    (original : List (RawEvent Party Good Port Technology Instrument)) :
    (Event.Paid source inputs ⟨index, ordinal, some (.periods original)⟩) =
      ActualSlotPaid source original ordinal index := rfl

structure AdmissionAt (event : Event source inputs) (index : source.Slot) where
  at_registration : event.ordinal = 0
  original_slot : event.index = index
  registration : RegistrationReceipt source inputs

structure AssumptionAt (holder : Fin (ProgrammeSource.registrationSize (OutstandingSource.History.input source inputs)))
    (event : Event source inputs) (index : source.Slot) extends AdmissionAt source inputs event index where
  own_seat : holder = seat source inputs

structure HistoricalVisitReceipt (event : Event source inputs) : Type where
  running : 0 < event.ordinal
  task_write : ProgrammeLedger.transferReceiptOf (OutstandingSource.History.input source (event.actualInputs source inputs))
      ((OutstandingSource.History.taskWrite source (event.actualInputs source inputs)) (event.ordinal - 1)).2 =
    some ((OutstandingSource.History.writtenReceipt source (event.actualInputs source inputs)) (event.ordinal - 1))
  current : (OutstandingSource.History.runningCurrent source (event.actualInputs source inputs)) (event.ordinal - 1) =
    (ProgrammeHistory.visitAt (OutstandingSource.History.input source (event.actualInputs source inputs)) event.ordinal).current

inductive VisitReceipt (event : Event source inputs) : Type
  | period (receipt : HistoricalVisitReceipt source inputs event)
  | actual (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source)
      (source_eq : event.inputOverride = some (.actual input)) (receipt : input.Receipt)
  | expired (input : ExpiredInput source)
      (source_eq : event.inputOverride = some (.expired input)) (receipt : input.Receipt source)

def visitReceiptAt (index : source.Slot) (depth : Nat)
    (actualInputs : Option (List (RawEvent Party Good Port Technology Instrument))) :
    VisitReceipt source inputs ⟨index, depth + 1, actualInputs.map InputOverride.periods⟩ :=
  .period {
    running := Nat.zero_lt_succ depth
    task_write := by
      cases actualInputs <;> exact (OutstandingSource.History.receipt_is_in_own_original_write source _) depth
    current := by
      cases actualInputs <;> exact (OutstandingSource.History.runningCurrent_is_own_visit source _) depth }

def visitReceipt (index : source.Slot) (depth : Nat) : VisitReceipt source inputs ⟨index, depth + 1, none⟩ :=
  visitReceiptAt source inputs index depth none

def actualEvent (index : source.Slot)
    (actual : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source) :
    Event source inputs := ⟨index, 0, some (.actual actual)⟩

def actualReceipt (index : source.Slot)
    (actual : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source) :
    VisitReceipt source inputs (actualEvent source inputs index actual) := .actual actual rfl actual.receipt

/-- This observation maintains an expired responsibility; it has no payment
claim about the original window. New-window payment belongs to its own task. -/
def expiredEvent (index : source.Slot) (input : ExpiredInput source) : Event source inputs :=
  ⟨index,input.depth + 1,some (.expired input)⟩

def expiredReceipt (index : source.Slot) (input : ExpiredInput source) :
    VisitReceipt source inputs (expiredEvent source inputs index input) := .expired input rfl (input.receipt source)

theorem expired_event_cannot_fulfil_the_original_window (index : source.Slot) (input : ExpiredInput source) :
    ¬ Event.Paid source inputs (expiredEvent source inputs index input) := fun impossible => impossible

structure FulfilledAt (event : Event source inputs) (content scope : source.Slot) : Type where
  content_eq : content = event.index
  scope_eq : scope = event.index
  actual : VisitReceipt source inputs event
  payment : event.Paid source inputs

structure RetainedAt (event : Event source inputs) (content scope : source.Slot) : Type where
  content_eq : content = event.index
  scope_eq : scope = event.index
  actual : VisitReceipt source inputs event
  unpaid : ¬ event.Paid source inputs

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event source inputs
  Content := source.Slot
  Residual := Bundle Good
  Bearer := Fin (ProgrammeSource.registrationSize (OutstandingSource.History.input source inputs))
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
  AcceptedTaskAt := AdmissionAt source inputs
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt source inputs
  AcceptedAt := AssumptionAt source inputs
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun content scope => PLift (content = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := RetainedAt source inputs
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := FulfilledAt source inputs
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

abbrev V := vocabulary source inputs

def admissionPayload (index : source.Slot) : NativeAdmissionPayload (V source inputs) where
  sourceEvent := ⟨index, 0, none⟩
  content := index
  residual := (source.seed.slot index).goods
  bearer := seat source inputs
  beneficiary := (source.seed.slot index).bearer
  scope := index
  lineage := index
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask ⟨rfl, rfl, registered source inputs⟩
  authority := ⟨rfl, rfl, registered source inputs⟩
  assumption := .accepted ⟨⟨rfl, rfl, registered source inputs⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (index : source.Slot) := (admissionPayload source inputs index).toObligation

/-- The actual visit chooses the disposition; this event has no payment,
terminal, target obligation, or selected branch field. -/
structure Review (obligation : AdmittedObligation (V source inputs)) where
  index : source.Slot
  depth : Nat
  content_eq : obligation.content = index
  scope_eq : obligation.scope = index
  admission_index : obligation.admission.sourceEvent.index = index

def review (index : source.Slot) (depth : Nat) : Review source inputs (obligation source inputs index) :=
  ⟨index, depth, rfl, rfl, rfl⟩

def reviewSource {obligation : AdmittedObligation (V source inputs)}
    (event : Review source inputs obligation) : Event source inputs := ⟨event.index, event.depth + 1, none⟩

def disposition {obligation : AdmittedObligation (V source inputs)}
    (event : Review source inputs obligation) :
    BoundaryDisposition (V source inputs) obligation (reviewSource source inputs event) :=
  if paid : (ActualSlotPaid source inputs) (event.depth + 1) event.index then
    .terminal (.final (.fulfilled
      ⟨event.content_eq, event.scope_eq, visitReceipt source inputs event.index event.depth, paid⟩))
  else .carry (.maintained
    ⟨event.content_eq, event.scope_eq, visitReceipt source inputs event.index event.depth, paid⟩)

def process : NativeResponsibilityProcess (V source inputs) where
  AdmissionEvent := source.Slot
  admissionPayload := admissionPayload source inputs
  BoundaryEvent := Review source inputs
  boundarySource := reviewSource source inputs
  boundary_anchor_eq := by
    intro obligation event
    change MinimalRegistrableSourceAnchor.canonical event.index event.index =
      MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index
        obligation.admission.sourceEvent.index
    rw [event.admission_index]
  boundary_incidence_eq := by
    intro obligation event
    exact event.admission_index.symm
  boundaryDisposition := disposition source inputs
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def admissionEdge (index : source.Slot) :
    (process source inputs).Edge (ResponsibilityState.empty (V source inputs)) := .admit index

def admittedState (index : source.Slot) := (admissionEdge source inputs index).target

def slot (index : source.Slot) : Fin (admittedState source inputs index).slots.length :=
  ⟨0, by simp [admittedState, admissionEdge, NativeResponsibilityProcess.Edge.target]⟩

theorem admitted_present (index : source.Slot) :
    (admittedState source inputs index).slots.get (slot source inputs index) =
      .live (obligation source inputs index) := rfl

def reviewEdge (index : source.Slot) (depth : Nat) :
    (process source inputs).Edge (admittedState source inputs index) :=
  .cross (slot source inputs index) (obligation source inputs index)
    (admitted_present source inputs index) (review source inputs index depth)

theorem unpaid_is_still_live (index : source.Slot) (depth : Nat)
    (unpaid : ¬ (ActualSlotPaid source inputs) (depth + 1) index) :
    (reviewEdge source inputs index depth).target.slots[0]? =
      some (.live (obligation source inputs index)) := by
  have target := NativeResponsibilityProcess.cross_target_slot (P := process source inputs)
    (slot source inputs index) (obligation source inputs index) (admitted_present source inputs index)
      (review source inputs index depth)
  simpa [reviewEdge, process, disposition, review, unpaid,
    BoundaryDisposition.targetSlot, ActiveCarryDisposition.target, slot] using target

theorem paid_has_terminal_receipt (index : source.Slot) (depth : Nat)
    (paid : (ActualSlotPaid source inputs) (depth + 1) index) :
    ∃ archive, (reviewEdge source inputs index depth).target.slots[0]? = some (.terminal archive) := by
  have target := NativeResponsibilityProcess.cross_target_slot (P := process source inputs)
    (slot source inputs index) (obligation source inputs index) (admitted_present source inputs index)
      (review source inputs index depth)
  simp only [process, disposition, review, dif_pos paid] at target
  exact ⟨_, target⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService

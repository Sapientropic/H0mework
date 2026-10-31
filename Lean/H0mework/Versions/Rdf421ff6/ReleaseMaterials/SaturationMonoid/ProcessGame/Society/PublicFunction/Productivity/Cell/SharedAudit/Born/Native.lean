import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Service

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root
open ComplementObservation
open Institutions.Capitalism.Universal.Source.Program

structure Event where
  kind : Kind
  ordinal : Nat

variable (birth : Birth)

structure AdmissionAt (event : Event) (kind : Kind) : Type where
  at_birth : event.ordinal = birth.ordinal
  own_kind : event.kind = kind
  original : birth.item ∈ Born.itemsAt birth.ordinal
  instruction : birth.instructionOrigin.instruction? source.input = some birth.item
  paid_seed : 0 < Institutions.Capitalism.Universal.Source.Program.flowAt
    (law.actualCredit birth.item.before birth.item.request) birth.child .seed
  write : ProgrammeLedger.transferReceiptOf source.input (source.taskWrite (birth.ordinal - 1)).2 =
    some (source.writtenReceipt (birth.ordinal - 1))

structure AssumptionAt (holder : Fin (ProgrammeSource.registrationSize source.input))
    (event : Event) (kind : Kind) extends AdmissionAt birth event kind where
  protocol : holder = OutstandingSource.NativeService.seat source

structure VisitReceipt (event : Event) : Type where
  after_birth : birth.ordinal ≤ event.ordinal
  write : ProgrammeLedger.transferReceiptOf source.input (source.taskWrite (event.ordinal - 1)).2 =
    some (source.writtenReceipt (event.ordinal - 1))
  next : (source.actualExecution (event.ordinal - 1)).after = source.currentAt (event.ordinal + 1)

def visitReceipt (kind : Kind) (elapsed : Nat) : VisitReceipt birth ⟨kind, birth.ordinal + elapsed⟩ where
  after_birth := Nat.le_add_right _ _
  write := source.receipt_is_in_original_task_write _
  next := by
    have positive := birth.running
    have same : birth.ordinal + elapsed - 1 + 2 = birth.ordinal + elapsed + 1 := by omega
    exact (source.actualExecution (birth.ordinal + elapsed - 1)).root_next_exact.trans
      (congrArg source.currentAt same)

structure FulfilledAt (event : Event) (content scope : Kind) where
  content_eq : content = event.kind
  scope_eq : scope = event.kind
  actual : VisitReceipt birth event
  payment : Payment birth event.kind event.ordinal

structure RetainedAt (event : Event) (content scope : Kind) where
  content_eq : content = event.kind
  scope_eq : scope = event.kind
  actual : VisitReceipt birth event
  unpaid : ¬ Paid birth event.kind event.ordinal

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event
  Content := Kind
  Residual := Bundle Good
  Bearer := Fin (ProgrammeSource.registrationSize source.input)
  ProtectedInterest := Party
  Scope := Kind
  Lineage := (Nat × Nat) × Kind
  Incidence := (Nat × Nat) × Kind
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical event.kind (birthKey birth, event.kind)
  sourceIncidence := fun event => (birthKey birth, event.kind)
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := AdmissionAt birth
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt birth
  AcceptedAt := AssumptionAt birth
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun content scope => PLift (content = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := RetainedAt birth
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := FulfilledAt birth
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

abbrev V := vocabulary birth

def admission (kind : Kind) : AdmissionAt birth ⟨kind, birth.ordinal⟩ kind :=
  ⟨rfl, rfl, birth.original, birth.instruction_decodes_the_original_item, birth.positive_credit, birth.original_row_and_next.1⟩

def admissionPayload (kind : Kind) : NativeAdmissionPayload (V birth) where
  sourceEvent := ⟨kind, birth.ordinal⟩
  content := kind
  residual := kind.goods
  bearer := OutstandingSource.NativeService.seat source
  beneficiary := birth.child
  scope := kind
  lineage := (birthKey birth, kind)
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask (admission birth kind)
  authority := admission birth kind
  assumption := .accepted ⟨admission birth kind, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (kind : Kind) := (admissionPayload birth kind).toObligation

structure Review (original : AdmittedObligation (V birth)) where
  kind : Kind
  elapsed : Nat
  content_eq : original.content = kind
  scope_eq : original.scope = kind
  admission_kind : original.admission.sourceEvent.kind = kind

def review (kind : Kind) (elapsed : Nat) : Review birth (obligation birth kind) :=
  ⟨kind, elapsed, rfl, rfl, rfl⟩

def reviewSource {original : AdmittedObligation (V birth)} (event : Review birth original) : Event :=
  ⟨event.kind, birth.ordinal + event.elapsed⟩

def disposition {original : AdmittedObligation (V birth)} (event : Review birth original) :
    BoundaryDisposition (V birth) original (reviewSource birth event) :=
  if paid : Paid birth event.kind (birth.ordinal + event.elapsed) then
    .terminal (.final (.fulfilled ⟨event.content_eq, event.scope_eq,
      visitReceipt birth event.kind event.elapsed, payment birth event.kind _ paid⟩))
  else .carry (.maintained ⟨event.content_eq, event.scope_eq,
    visitReceipt birth event.kind event.elapsed, paid⟩)

def process : NativeResponsibilityProcess (V birth) where
  AdmissionEvent := Kind
  admissionPayload := admissionPayload birth
  BoundaryEvent := Review birth
  boundarySource := reviewSource birth
  boundary_anchor_eq := by
    intro original event
    change MinimalRegistrableSourceAnchor.canonical event.kind (birthKey birth, event.kind) =
      MinimalRegistrableSourceAnchor.canonical original.admission.sourceEvent.kind (birthKey birth, original.admission.sourceEvent.kind)
    rw [event.admission_kind]
  boundary_incidence_eq := fun event => congrArg (fun kind => (birthKey birth, kind)) event.admission_kind.symm
  boundaryDisposition := disposition birth
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def admissionEdge (kind : Kind) : (process birth).Edge (ResponsibilityState.empty (V birth)) := .admit kind

def admittedState (kind : Kind) := (admissionEdge birth kind).target

def paidArchive (kind : Kind) (elapsed : Nat) (paid : Paid birth kind (birth.ordinal + elapsed)) :
    TerminalArchive (V birth) :=
  ⟨obligation birth kind, ⟨kind, birth.ordinal + elapsed⟩,
    .fulfilled ⟨rfl, rfl, visitReceipt birth kind elapsed, payment birth kind _ paid⟩⟩

inductive Shape (kind : Kind) (elapsed : Nat) (state : ResponsibilityState (V birth)) : Type where
  | live (unpaid : ∀ earlier < elapsed, ¬ Paid birth kind (birth.ordinal + earlier))
      (slots : state.slots = [.live (obligation birth kind)])
  | terminal (first : Nat) (before_cut : first < elapsed)
      (paid : Paid birth kind (birth.ordinal + first))
      (earliest : ∀ earlier < first, ¬ Paid birth kind (birth.ordinal + earlier))
      (slots : state.slots = [.terminal (paidArchive birth kind first paid)])

structure Prefix (kind : Kind) (elapsed : Nat) where
  state : ResponsibilityState (V birth)
  run : (process birth).Run (ResponsibilityState.empty (V birth)) state
  shape : Shape birth kind elapsed state

def initial (kind : Kind) : Prefix birth kind 0 where
  state := admittedState birth kind
  run := .step .nil (admissionEdge birth kind)
  shape := .live (by intro earlier bound; omega) rfl

def advance (kind : Kind) (elapsed : Nat) (prior : Prefix birth kind elapsed) : Prefix birth kind (elapsed + 1) := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
    let address : Fin state.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
    have present : state.slots.get address = .live (obligation birth kind) := by simp [slots, address]
    let edge : (process birth).Edge state :=
      .cross address (obligation birth kind) present (review birth kind elapsed)
    by_cases paid : Paid birth kind (birth.ordinal + elapsed)
    · exact {
        state := edge.target
        run := .step run edge
        shape := .terminal elapsed (by omega) paid unpaid (by
          simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, review, reviewSource,
            dif_pos paid, slots, address, BoundaryDisposition.targetSlot, paidArchive]) }
    · exact {
        state := edge.target
        run := .step run edge
        shape := .live (by
          intro earlier bound
          by_cases old : earlier < elapsed
          · exact unpaid earlier old
          · have same : earlier = elapsed := by omega
            simpa only [same] using paid) (by
          simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, review, reviewSource,
            dif_neg paid, slots, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target]) }
  | terminal first before_cut paid earliest slots =>
    exact {
      state := state
      run := run
      shape := .terminal first (by omega) paid earliest slots }

def historyAt (kind : Kind) : (elapsed : Nat) → Prefix birth kind elapsed
  | 0 => initial birth kind
  | elapsed + 1 => advance birth kind elapsed (historyAt kind elapsed)

theorem native_live_iff_unpaid (kind : Kind) (elapsed : Nat) :
    (historyAt birth kind elapsed).state.LiveAt 0 ↔
      ∀ earlier < elapsed, ¬ Paid birth kind (birth.ordinal + earlier) := by
  cases (historyAt birth kind elapsed).shape with
  | live unpaid slots => exact ⟨fun _ => unpaid, fun _ => ⟨obligation birth kind, by simp [slots]⟩⟩
  | terminal first before_cut paid earliest slots =>
    constructor
    · rintro ⟨other, live⟩; simp only [slots, List.getElem?_cons_zero] at live; cases live
    · intro unpaid; exact False.elim (unpaid first before_cut paid)

theorem native_terminal_iff_paid (kind : Kind) (elapsed : Nat) :
    (historyAt birth kind elapsed).state.TerminalAt 0 ↔
      ∃ earlier < elapsed, Paid birth kind (birth.ordinal + earlier) := by
  cases (historyAt birth kind elapsed).shape with
  | live unpaid slots =>
    constructor
    · rintro ⟨archive, terminal⟩; simp only [slots, List.getElem?_cons_zero] at terminal; cases terminal
    · rintro ⟨earlier, bound, paid⟩; exact False.elim (unpaid earlier bound paid)
  | terminal first before_cut paid earliest slots =>
    exact ⟨fun _ => ⟨first, before_cut, paid⟩,
      fun _ => ⟨paidArchive birth kind first paid, by simp [slots]⟩⟩

theorem terminal_has_the_first_original_payment (kind : Kind) (elapsed : Nat)
    (terminal : (historyAt birth kind elapsed).state.TerminalAt 0) :
    ∃ (first : Nat) (_before_cut : first < elapsed) (paid : Paid birth kind (birth.ordinal + first)),
      (∀ earlier < first, ¬ Paid birth kind (birth.ordinal + earlier)) ∧
      (historyAt birth kind elapsed).state.slots = [.terminal (paidArchive birth kind first paid)] := by
  cases (historyAt birth kind elapsed).shape with
  | live unpaid slots =>
    obtain ⟨first, bound, paid⟩ := (native_terminal_iff_paid birth kind elapsed).mp terminal
    exact False.elim (unpaid first bound paid)
  | terminal first before_cut paid earliest slots => exact ⟨first, before_cut, paid, earliest, slots⟩

theorem terminal_next_state_is_preserved (kind : Kind) (elapsed : Nat)
    (terminal : (historyAt birth kind elapsed).state.TerminalAt 0) :
    (historyAt birth kind (elapsed + 1)).state = (historyAt birth kind elapsed).state := by
  change (advance birth kind elapsed (historyAt birth kind elapsed)).state = _
  generalize historyAt birth kind elapsed = prior at *
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
    obtain ⟨archive, present⟩ := terminal
    simp only [slots, List.getElem?_cons_zero] at present
    cases present
  | terminal _first _before_cut _paid _earliest _slots => rfl

theorem terminal_state_is_preserved (kind : Kind) (elapsed later : Nat)
    (terminal : (historyAt birth kind elapsed).state.TerminalAt 0) :
    (historyAt birth kind (elapsed + later)).state = (historyAt birth kind elapsed).state := by
  induction later with
  | zero => rfl
  | succ later ih =>
    exact (terminal_next_state_is_preserved birth kind (elapsed + later) (by rw [ih]; exact terminal)).trans ih

theorem exact_native_history (kind : Kind) (elapsed : Nat) :
    (historyAt birth kind elapsed).state.history = (historyAt birth kind elapsed).run.events := by
  simpa [ResponsibilityState.empty] using NativeResponsibilityProcess.Run.history_eq (process birth)
    (historyAt birth kind elapsed).run

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Native

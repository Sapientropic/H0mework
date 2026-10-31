import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Messages

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
set_option maxErrors 5

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ComplementObservation
open Institutions.Capitalism.Universal.Source.Program

abbrev Key := Nat × Nat × Party

def key {shared : Bool} (message : Message shared) : Key := (message.ordinal, message.item.index, message.actor)

inductive Role where
  | sharedReview
  deriving DecidableEq

structure Event (shared : Bool) where
  origin : Key
  message : Message shared

variable (shared : Bool)

structure AdmissionAt (event : Event shared) (content : Role) : Type where
  actual : event.message = joining shared
  anchored : event.origin = key event.message
  content_eq : content = .sharedReview
  command : event.message.command = .accept
  accepted : law.Valid event.message.item.before event.message.item.request
  paid : flowAt (law.actualDebit event.message.item.before event.message.item.request) event.message.actor .labor = 1

structure AuthorityAt (event : Event shared) (scope : Party) : Type where
  admitted : AdmissionAt shared event .sharedReview
  scope_eq : scope = event.message.actor

structure AssumptionAt (bearer : Party) (event : Event shared) (scope : Party) extends AuthorityAt shared event scope where
  own : bearer = event.message.actor

structure ReviewAt (event : Event shared) (content : Role) (scope : Party) : Type where
  accepted : law.Valid event.message.item.before event.message.item.request
  command : event.message.command = .challenge ∨ event.message.command = .accept
  content_eq : content = .sharedReview
  actor_eq : event.message.actor = scope

structure RefusalAt (event : Event shared) (content : Role) (scope : Party) : Type where
  refused : ¬ law.Valid event.message.item.before event.message.item.request
  content_eq : content = .sharedReview
  actor_eq : event.message.actor = scope

structure ExitAt (event : Event shared) (content : Role) (scope : Party) : Type where
  accepted : law.Valid event.message.item.before event.message.item.request
  command : event.message.command = .exit
  content_eq : content = .sharedReview
  actor_eq : event.message.actor = scope
  released : update (registerBefore shared event.message.ordinal event.message.item)
    event.message.item event.message.actor = .released

open Institutions.Capitalism.Universal.Root

structure RouteAt (event : Event shared) (_content : Role) (_scope : Party) : Type where
  row : ProgrammeLedger.transferReceiptOf (source shared).input
    ((source shared).taskWrite (event.message.ordinal - 1)).2 =
      some ((source shared).writtenReceipt (event.message.ordinal - 1))
  next : ((source shared).actualExecution (event.message.ordinal - 1)).after =
    (source shared).currentAt (event.message.ordinal + 1)
  old_service : (slot : (source shared).Slot) →
    OutstandingSource.NativeService.Prefix (source shared) slot event.message.ordinal
  finance : (Financial.process (source shared).input).Run
    (Financial.accountAt (source shared).input 0).current
    (Financial.accountAt (source shared).input (event.message.ordinal + 1)).current

def routeAt (event : Event shared) (content : Role) (scope : Party) : RouteAt shared event content scope where
  row := (source shared).receipt_is_in_original_task_write _
  next := by
    have positive := event.message.later
    have same : event.message.ordinal - 1 + 2 = event.message.ordinal + 1 := by omega
    exact ((source shared).actualExecution _).root_next_exact.trans (congrArg (source shared).currentAt same)
  old_service := fun slot => OutstandingSource.NativeService.historyAt (source shared) slot event.message.ordinal
  finance := by
    simpa only [Nat.zero_add] using Financial.BalanceConservation.fromActualCut (source shared).input 0 (event.message.ordinal + 1)

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event shared
  Content := Role
  Residual := Bundle Good
  Bearer := Party
  ProtectedInterest := Party
  Scope := Party
  Lineage := Key
  Incidence := Key
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical event.message.actor event.origin
  sourceIncidence := Event.origin
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := AdmissionAt shared
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AuthorityAt shared
  AcceptedAt := AssumptionAt shared
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun _ scope => PLift (scope = (joining shared).actor)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := ReviewAt shared
  TypedDeferAt := RefusalAt shared
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := fun _ _ _ => Empty
  WaivedAt := fun _ _ _ => Empty
  InvalidatedAt := fun _ _ _ => Empty
  AbandonedAt := fun _ _ _ => Empty
  ImpossibleResidueAcceptedAt := fun _ _ _ => Empty
  SupersessionAt := fun _ _ _ _ _ _ _ => Empty
  ReopenAt := fun _ _ _ _ _ _ _ => Empty
  JurisdictionEndedAt := ExitAt shared
  ConsentRevokedAt := fun _ _ _ => Empty
  CapacityReleasedAt := fun _ _ _ => Empty
  UpperRouteAt := RouteAt shared
  NextActorSignal := Nat
  AgeSignal := Nat
  TransferOfferSignal := Empty

abbrev V := vocabulary shared

def admitted : AdmissionAt shared ⟨key (joining shared), joining shared⟩ .sharedReview where
  actual := rfl
  anchored := rfl
  content_eq := rfl
  command := (joining_is_an_actual_paid_choice shared).2.2.1
  accepted := (joining_is_an_actual_paid_choice shared).2.2.2.1
  paid := by
    rw [(joining_is_an_actual_paid_choice shared).2.1]
    exact (joining_is_an_actual_paid_choice shared).2.2.2.2

def admissionPayload : NativeAdmissionPayload (V shared) where
  sourceEvent := ⟨key (joining shared), joining shared⟩
  content := .sharedReview
  residual := []
  bearer := (joining shared).actor
  beneficiary := (joining shared).actor
  scope := (joining shared).actor
  lineage := key (joining shared)
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask (admitted shared)
  authority := ⟨admitted shared, rfl⟩
  assumption := .accepted ⟨⟨admitted shared, rfl⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation := (admissionPayload shared).toObligation

structure Boundary (original : AdmittedObligation (V shared)) where
  message : Message shared
  own : message.actor = (joining shared).actor
  kind : message.command = .challenge ∨ message.command = .exit ∨ message.command = .accept
  later : 12 < message.ordinal
  origin : original = obligation shared

def boundarySource {original : AdmittedObligation (V shared)} (event : Boundary shared original) : Event shared :=
  ⟨original.admission.sourceEvent.origin, event.message⟩

def disposition {original : AdmittedObligation (V shared)} (event : Boundary shared original) :
    BoundaryDisposition (V shared) original (boundarySource shared event) := by
  rcases event with ⟨message, own, kind, later, rfl⟩
  if accepted : law.Valid message.item.before message.item.request then
    if exited : message.command = .exit then
      exact .bearerRelease (.jurisdictionEndedWithResidue
        ⟨accepted, exited, rfl, own, by
          change update (registerBefore shared message.ordinal message.item) message.item message.actor = .released
          rw [accepted_message_updates_its_owner shared message accepted, exited]; rfl⟩ (routeAt shared _ _ _))
    else
      exact .carry (.maintained ⟨accepted, (by rcases kind with challenge | exit | accept; exact Or.inl challenge; exact False.elim (exited exit); exact Or.inr accept), rfl, own⟩)
  else exact .carry (.deferred ⟨accepted, rfl, own⟩)

theorem target_keeps_original_responsibility {original : AdmittedObligation (V shared)}
    (event : Boundary shared original) : (disposition shared event).targetSlot = .live original := by
  rcases event with ⟨message, own, kind, later, rfl⟩
  simp only [disposition]
  split_ifs <;> rfl

def process : NativeResponsibilityProcess (V shared) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => admissionPayload shared
  BoundaryEvent := Boundary shared
  boundarySource := boundarySource shared
  boundary_anchor_eq := by
    intro original event
    rcases event with ⟨message, own, kind, later, rfl⟩
    change MinimalRegistrableSourceAnchor.canonical message.actor _ =
      MinimalRegistrableSourceAnchor.canonical (joining shared).actor _
    rw [own]
    rfl
  boundary_incidence_eq := fun _ => rfl
  boundaryDisposition := disposition shared
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def admissionEdge : (process shared).Edge (ResponsibilityState.empty (V shared)) := .admit ()

structure History where
  state : ResponsibilityState (V shared)
  run : (process shared).Run (ResponsibilityState.empty (V shared)) state
  slots : state.slots = [.live (obligation shared)]

def initial : History shared :=
  ⟨(admissionEdge shared).target, .step .nil (admissionEdge shared), rfl⟩

def receive (prior : History shared) (message : Message shared) : History shared := by
  if checked : message.actor = (joining shared).actor ∧
      (message.command = .challenge ∨ message.command = .exit ∨ message.command = .accept) ∧ 12 < message.ordinal then
    let address : Fin prior.state.slots.length := ⟨0, by rw [prior.slots]; exact Nat.zero_lt_succ 0⟩
    have present : prior.state.slots.get address = .live (obligation shared) := by simp [prior.slots, address]
    let event : Boundary shared (obligation shared) := ⟨message, checked.1, checked.2.1, checked.2.2, rfl⟩
    let edge : (process shared).Edge prior.state := .cross address (obligation shared) present event
    exact ⟨edge.target, .step prior.run edge, by
      simp [edge, NativeResponsibilityProcess.Edge.target, process, prior.slots, address,
        target_keeps_original_responsibility, event]⟩
  else exact prior

def historyAt : Nat → History shared
  | 0 => initial shared
  | elapsed + 1 => (messagesAt shared (13 + elapsed)).foldl (receive shared) (historyAt elapsed)

theorem original_admission_and_residue_are_retained (elapsed : Nat) :
    (historyAt shared elapsed).state.slots = [.live (obligation shared)] := (historyAt shared elapsed).slots

theorem native_history_is_exact (elapsed : Nat) :
    (historyAt shared elapsed).state.history = (historyAt shared elapsed).run.events := by
  simpa [ResponsibilityState.empty] using NativeResponsibilityProcess.Run.history_eq (process shared)
    (historyAt shared elapsed).run

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Native

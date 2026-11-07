import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
theorem access_valid_iff {plan : Plan} (ready : Seed plan) (before : AuditCurrent) (actor : Party) (query : Query) :
    ready.law.Valid before (accessRequest actor query) ↔ before.technology.holder = some actor ∧
      ready.scope.task.earliest ≤ before.clock ∧ before.clock ≤ ready.scope.task.deadline ∧
      1 ≤ before.stock actor .energy ∧ (if actor = 0 then 2 else 1) ≤ before.stock 0 .energy :=
  Continuation.access_valid_iff ready.window before actor query

theorem stale_holder_cannot_access {plan : Plan} (seed : Seed plan) (current : AuditCurrent)
    (actor : Party) (query : Query) (different : current.technology.holder ≠ some actor) :
    ¬ seed.law.Valid current (accessRequest actor query) := by
  rw [access_valid_iff]
  exact fun paid => different paid.1

private abbrev operationDecidableEq : DecidableEq (Operation Party Good (Mandate.State Party Technology) Unit) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq Action := by
  letI := operationDecidableEq
  intro left right
  cases left
  cases right
  simp only [Institutions.Capitalism.Universal.Source.Program.Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

structure Delivery {plan : Plan} (ready : Seed plan) (actor : Party) (before : AuditCurrent) (word : List Action) (query : Query) where
  private mk ::
  access : {item // item ∈ ready.law.rawItems before word}
  accessRequest : access.val.request = EnergyRenewal.accessRequest actor query
  accessPaid : ready.law.Valid access.val.before access.val.request
  fee : {item // item ∈ ready.law.rawItems before word}
  feeRequest : fee.val.request = deliveryFee
  feePaid : ready.law.Valid fee.val.before fee.val.request
  consecutive : fee.val.index = access.val.index+1

def deliveries {plan : Plan} (ready : Seed plan) (actor : Party) (before : AuditCurrent) (word : List Action) (query : Query) :
    List (Delivery ready actor before word query) :=
  (ready.law.rawItems before word).attach.flatMap fun access =>
    (ready.law.rawItems before word).attach.filterMap fun fee =>
      if linked : access.val.request = accessRequest actor query ∧
          ready.law.Valid access.val.before access.val.request ∧
          fee.val.request = deliveryFee ∧ ready.law.Valid fee.val.before fee.val.request ∧
          fee.val.index = access.val.index+1 then
        some ⟨access,linked.1,linked.2.1,fee,linked.2.2.1,linked.2.2.2.1,linked.2.2.2.2⟩
      else none

namespace Delivery
variable {plan : Plan} {ready : Seed plan} {actor : Party} {before : AuditCurrent} {word : List Action} {query : Query}
  (receipt : Delivery ready actor before word query)

theorem authority_is_paid_and_within_the_new_window :
    receipt.access.val.before.technology.holder = some actor ∧
    ready.scope.task.earliest ≤ receipt.access.val.before.clock ∧
    receipt.access.val.before.clock ≤ ready.scope.task.deadline ∧
    1 ≤ receipt.access.val.before.stock actor .energy := by
  have paid := receipt.accessPaid
  rw [receipt.accessRequest,access_valid_iff] at paid
  exact ⟨paid.1,paid.2.1,paid.2.2.1,paid.2.2.2.1⟩

theorem service_really_debits_the_candidate :
    (ready.law.step receipt.access.val.before receipt.access.val.request).stock actor .energy+1 =
      receipt.access.val.before.stock actor .energy := by
  have balance := ready.law.material_step_balance receipt.access.val.before receipt.access.val.request actor .energy
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos receipt.accessPaid] at balance
  simpa [receipt.accessRequest,RawLaw.debit,RawLaw.credit,EnergyRenewal.accessRequest,flowAt,locate,amount] using balance

theorem delivery_really_debits_the_service :
    (ready.law.step receipt.fee.val.before receipt.fee.val.request).stock 0 .energy+1 = receipt.fee.val.before.stock 0 .energy := by
  have balance := ready.law.material_step_balance receipt.fee.val.before receipt.fee.val.request 0 .energy
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos receipt.feePaid] at balance
  simpa [receipt.feeRequest,RawLaw.debit,RawLaw.credit,deliveryFee,flowAt,locate,amount] using balance

def evidence (_receipt : Delivery ready actor before word query) : List (Slot × Evidence) :=
  (selected query).map fun slot => (slot,restrict (fields query) (originalEvidence slot))

theorem every_slice_has_original_service_origin (slot : Slot) (evidence : Evidence)
    (released : (slot,evidence) ∈ receipt.evidence) : Origin slot evidence := by
  obtain ⟨original,_,same⟩ := List.mem_map.mp released
  rcases Prod.mk.inj same with ⟨rfl,rfl⟩
  exact restrict_has_origin _ _ _ (original_evidence_has_origin _)

theorem both_independent_checks_consume_the_original_service (slot : Slot) (evidence : Evidence)
    (released : (slot,evidence) ∈ receipt.evidence) :
    (traceCheck slot evidence = .verified → source.ActualSlotPaid 1 (originalIndex slot)) ∧
    (lifecycleCheck slot evidence = .verified → source.ActualSlotPaid 1 (originalIndex slot)) :=
  ⟨trace_verifies_original _ _ (receipt.every_slice_has_original_service_origin _ _ released),
    lifecycle_verifies_original _ _ (receipt.every_slice_has_original_service_origin _ _ released)⟩
end Delivery

namespace Runtime
structure Result {plan : Plan} (seed : Seed plan) (requests : List Request) (ordinal : Nat) where
  commands : List (Mandate.ActualCommand energyBase seed.scope (seed.current requests ordinal)
    (if ordinal = 0 then [] else seed.emit requests (seed.current requests ordinal)))
  packets : List (Delivery seed (seed.requestActor (seed.requestAt requests ordinal) (seed.current requests ordinal))
    (seed.current requests ordinal) (if ordinal = 0 then [] else seed.emit requests (seed.current requests ordinal))
    (seed.requestAt requests ordinal).query)
  actualCommands : commands = Mandate.commandsAt energyBase seed.scope (seed.current requests ordinal)
    (if ordinal = 0 then [] else seed.emit requests (seed.current requests ordinal))
  actualPackets : packets = deliveries seed (seed.requestActor (seed.requestAt requests ordinal) (seed.current requests ordinal))
    (seed.current requests ordinal) (if ordinal = 0 then [] else seed.emit requests (seed.current requests ordinal))
    (seed.requestAt requests ordinal).query
  financeMatrix : (seed.current requests (ordinal+1)).claims = (before plan).claims

def result {plan : Plan} (seed : Seed plan) (requests : List Request) (ordinal : Nat) : Result seed requests ordinal :=
  ⟨Mandate.commandsAt energyBase seed.scope (seed.current requests ordinal)
      (if ordinal = 0 then [] else seed.emit requests (seed.current requests ordinal)),
    deliveries seed (seed.requestActor (seed.requestAt requests ordinal) (seed.current requests ordinal))
      (seed.current requests ordinal) (if ordinal = 0 then [] else seed.emit requests (seed.current requests ordinal))
      (seed.requestAt requests ordinal).query,rfl,rfl,seed.preserves_every_claim requests (ordinal+1)⟩
def projectionLaw {plan : Plan} (window : Seed plan) (requests : List Request) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (window.input requests)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current = (ProgrammeHistory.visitAt (window.input requests) ordinal).current →
      Result window requests ordinal
  project := fun _ {_} _ _ ordinal _canonical => result window requests ordinal

def root {plan : Plan} (window : Seed plan) (requests : List Request) :=
  (ProgrammeLiving.livingRoot (window.input requests)).withProjectionCoface (projectionLaw window requests)

theorem emitting_root_is_preserved {plan : Plan} (window : Seed plan) (requests : List Request) :
    (root window requests).toAuthoritativeRoot.toRoot = (ProgrammeLiving.livingRoot (window.input requests)).toAuthoritativeRoot.toRoot := rfl

def stateAt {plan : Plan} (window : Seed plan) (requests : List Request) (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (window.input requests)) :=
  ⟨ProgrammeSource.V (window.input requests),root window requests,ProgrammeHistory.temporalVisit (window.input requests) ordinal⟩

def process {plan : Plan} (window : Seed plan) (requests : List Request) : SourceNativeLivingRootProcess (ProgrammeSource.N (window.input requests)) where
  State := Nat
  stateAt := stateAt window requests
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (window.input requests)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (window.input requests) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | execution | continuation

def facade {plan : Plan} (window : Seed plan) (requests : List Request) : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (window.input requests)) where
  process := process window requests
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (window.input requests)
    | .continuation => projectionLaw window requests
  installationAt := by
    intro state face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource (window.input requests)) (projectionLaw window requests)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource (window.input requests)) (projectionLaw window requests)
  projectionAt := fun _ face => match face with | .execution => .execution | .continuation => ()

def activated {plan : Plan} (window : Seed plan) (requests : List Request) (ordinal : Nat) := (facade window requests).seed.advance ordinal

theorem activated_state {plan : Plan} (window : Seed plan) (requests : List Request) (ordinal : Nat) : (activated window requests ordinal).state = ordinal := by
  induction ordinal with | zero => rfl | succ ordinal ih => exact congrArg Nat.succ ih

theorem shares_actual_writeback_and_generated_next {plan : Plan} (window : Seed plan) (requests : List Request) (ordinal : Nat) :
    (activated window requests ordinal).tick.generated.occurrence =
      (activated window requests ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated window requests ordinal).current.visit.current ∧
    HEq (activated window requests ordinal).tick.generated.wholeLedgerWriteBack
      ((activated window requests ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated window requests ordinal).current.visit.current) ∧
    HEq ((facade window requests).readoutAt (activated window requests ordinal) .continuation)
      ((activated window requests ordinal).tick.generated.projectionOutcome
        (((facade window requests).installationAt (activated window requests ordinal) .continuation).embed
          ((facade window requests).projectionAt (activated window requests ordinal) .continuation))) ∧
    (activated window requests ordinal).tick.nextCurrent =
      (process window requests).stateAt ((process window requests).successor (activated window requests ordinal).state) :=
  ((facade window requests).readoutAt_factorizes (activated window requests ordinal) .continuation).2

def consume {plan : Plan} (window : Seed plan) (requests : List Request) (ordinal : Nat)
    : Result window requests ordinal :=
  match (facade window requests).readoutAt (activated window requests ordinal) .continuation with
  | .inl ⟨_,payload⟩ => payload ordinal (by
      change (ProgrammeHistory.visitAt (window.input requests) (activated window requests ordinal).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

end Runtime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff

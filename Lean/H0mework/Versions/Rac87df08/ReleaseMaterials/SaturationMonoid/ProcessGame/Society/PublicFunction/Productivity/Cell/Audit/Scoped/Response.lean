import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- A submitted claim, not an authenticated observation or a verdict of misconduct. -/
structure Objection where
  challenger : Party
  observedCut : Nat
  snapshot : Mandate.State Party Technology
  alleged : Option Record

def submission (objection : Objection) : Action :=
  ⟨objection.challenger,[],scope.challenge,[scope.challenge],.present⟩

inductive Review where
  | incomplete | stale | noDifference | unauthorized | actionable
  deriving DecidableEq, Repr

def Complete (record : Record) : Prop :=
  record.access = .admitted → ∀ slot ∈ selected record.query,
    ∃ pair ∈ record.evidence,pair.1 = slot ∧
      (.admission ∈ fields record.query → pair.2.admission.isSome = true) ∧
      (.payment ∈ fields record.query → pair.2.payment.isSome = true)

instance (record : Record) : Decidable (Complete record) := by unfold Complete; infer_instance

/-- The comparison is a source decision; neither a caller's PASS bit nor a
network owner's identity grants native standing. -/
def review (before : AuditCurrent) (expected : Record) (objection : Objection) : Review :=
  match objection.alleged with
  | none => .incomplete
  | some alleged =>
    if ¬ Complete alleged then .incomplete
    else if objection.snapshot ≠ before.technology ∨ ¬ expected.cut < before.round - initial.round ∨
        alleged.cut ≠ expected.cut ∨
        alleged.actor ≠ expected.actor ∨ alleged.query ≠ expected.query then .stale
    else if alleged = expected then .noDifference
    else if objection.challenger ∉ Delegation.members scope.task ∨
        ¬ auditLaw.Valid before (submission objection) then .unauthorized
    else .actionable

def replacement (before : AuditCurrent) (challenger : Party) : Option Party :=
  (Delegation.members scope.task).find? fun actor =>
    actor ≠ challenger && before.technology.holder ≠ some actor

def fund (before : AuditCurrent) (challenger : Party) : List Party → List Action
  | [] => []
  | donor :: rest =>
    let quantity := min (max 0 (1 - before.stock challenger .labor))
      (max 0 (before.stock donor .labor))
    if donor ≠ challenger ∧ before.technology.holder ≠ some donor ∧ 0 < quantity then
      let transfer : Action := ⟨donor,[],native .common,[],.transfer donor challenger [(.labor,quantity)]⟩
      transfer :: fund (auditLaw.step before transfer) challenger rest
    else fund before challenger rest

/-- Preserve the first actually refused request, and never skip it to run
later authorization or service steps. -/
def attempt (before : AuditCurrent) : List (AuditCurrent → Action) → List Action
  | [] => []
  | stage :: rest =>
    let action := stage before
    if auditLaw.Valid before action then action :: attempt (auditLaw.step before action) rest
    else [action]

def stages (challenger candidate : Party) (query : Query) : List (AuditCurrent → Action) :=
  [fun before => command before challenger .revoke,
   fun before => command before challenger (.propose candidate),
   fun before => command before candidate .accept,
   fun _ => accessRequest candidate query,
   fun _ => deliveryFee]

def word (before : AuditCurrent) (expected : Record) (objection : Objection) : List Action :=
  if review before expected objection = .actionable then
    let first := submission objection
    let supplies := fund (auditLaw.step before first) objection.challenger (Delegation.members scope.task)
    let funded := (auditLaw.execute (auditLaw.step before first) 0 supplies).final
    first :: supplies ++ match replacement funded objection.challenger with
      | none => [command funded objection.challenger .revoke]
      | some candidate => attempt funded
          (stages objection.challenger candidate expected.query)
  else []

abbrev Item := ExecutionItem Party Good AuditPort (Mandate.State Party Technology) Unit

structure Failure (before : AuditCurrent) (actions : List Action) where
  item : { item // item ∈ auditLaw.rawItems before actions }
  refused : ¬ auditLaw.Valid item.val.before item.val.request

def failures (before : AuditCurrent) (actions : List Action) : List (Failure before actions) :=
  (auditLaw.rawItems before actions).attach.filterMap fun item =>
    if accepted : auditLaw.Valid item.val.before item.val.request then none
    else some ⟨item,accepted⟩

def laborGap {before : AuditCurrent} {actions : List Action}
    (failure : Failure before actions) (actor : Party) : ℚ :=
  max 0 (flowAt (auditLaw.debit failure.item.val.before failure.item.val.request) actor .labor -
    failure.item.val.before.stock actor .labor)

def expectedAt (queries : Nat → Query) (larger : Bool) (cut : Nat) : Option Record :=
  (recordsAt queries larger cut).head?

def emitted (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection)
    (before : AuditCurrent) : List Action :=
  if before.round = initial.round + cut then
    match expectedAt queries larger objection.observedCut with
    | none => []
    | some expected => word before expected objection
  else emit queries larger before

/-- A lawful source extension keeps the original initial World and original
law; only the submitted response occurrence changes. -/
def input (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) :
    ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { Scoped.input queries larger with emission? := some (emitted queries larger cut objection) }

def current (queries : Nat → Query) (larger : Bool) (cut : Nat) (objection : Objection) : Nat → AuditCurrent :=
  Nat.rec initial (fun n before => auditLaw.next before
    (if n = 0 then [] else emitted queries larger cut objection before))

theorem current_succ (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (objection : Objection) (n : Nat) :
    current queries larger cut objection (n + 1) =
      auditLaw.next (current queries larger cut objection n)
        (if n = 0 then [] else emitted queries larger cut objection
          (current queries larger cut objection n)) := rfl

attribute [irreducible] current

theorem original_prefix_is_preserved (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (objection : Objection) (ordinal : Nat) (earlier : ordinal ≤ cut) :
    current queries larger cut objection ordinal = Scoped.current queries larger ordinal := by
  induction ordinal with
  | zero => rw [Scoped.current_zero]; unfold current; rfl
  | succ ordinal ih =>
    have earlier' : ordinal ≤ cut := by omega
    rw [current_succ,Scoped.current_succ,ih earlier']
    congr 1
    split
    · rfl
    · unfold emitted
      rw [Scoped.current_round]
      simp only [if_neg (by omega : ¬ initial.round + ordinal = initial.round + cut)]

theorem current_is_own_root_current (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (objection : Objection) (ordinal : Nat) :
    ProgrammeSource.rawCurrent (input queries larger cut objection)
      (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current =
      current queries larger cut objection ordinal := by
  induction ordinal with
  | zero => unfold current; rfl
  | succ ordinal ih =>
    change ProgrammeSource.rawCurrent (input queries larger cut objection)
      (ProgrammeSource.next (input queries larger cut objection)
        (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current) = _
    rw [ProgrammeSource.actual_raw_next,ih,current_succ]
    cases ordinal with
    | zero => rfl
    | succ ordinal =>
      congr 1
      simp only [Nat.succ_ne_zero,if_false]
      rw [← ih]
      change ProgrammeSource.rawEvent (input queries larger cut objection)
        (ProgrammeSource.next (input queries larger cut objection)
          (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current) =
        emitted queries larger cut objection (ProgrammeSource.rawCurrent (input queries larger cut objection)
          (ProgrammeSource.next (input queries larger cut objection)
            (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current))
      generalize (ProgrammeHistory.visitAt (input queries larger cut objection) ordinal).current = prior
      cases prior <;> rfl

theorem response_is_actual_next (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (objection : Objection) (positive : 0 < cut) :
    current queries larger cut objection (cut + 1) =
      auditLaw.next (Scoped.current queries larger cut)
        (match expectedAt queries larger objection.observedCut with
        | none => []
        | some expected => word (Scoped.current queries larger cut) expected objection) := by
  rw [current_succ]
  rw [original_prefix_is_preserved _ _ _ _ _ (by omega)]
  simp only [if_neg (by omega : ¬ cut = 0),emitted,Scoped.current_round,ite_true]

structure Delivery (before : AuditCurrent) (actions : List Action) (query : Query) where
  private mk ::
  withdrawal : Mandate.ActualCommand baseLaw scope before actions
  withdrawn : withdrawal.command = .revoke
  grant : Mandate.Grant baseLaw scope before actions
  supported : grant.candidate = 1 ∨ grant.candidate = 2
  replacement : withdrawal.item.val.before.technology.holder ≠ some grant.candidate
  sameMember : withdrawal.item.val.request.signer = grant.proposal.item.val.request.signer
  afterWithdrawal : withdrawal.after.technology = grant.proposal.item.val.before.technology
  revokeBeforeGrant : withdrawal.item.val.index < grant.proposal.item.val.index
  access : { item // item ∈ auditLaw.rawItems before actions }
  accessRequest : access.val.request = Scoped.accessRequest grant.candidate query
  accessPaid : auditLaw.Valid access.val.before access.val.request
  afterGrant : grant.acceptance.after.technology = access.val.before.technology
  grantBeforeService : grant.acceptance.item.val.index < access.val.index
  fee : { item // item ∈ auditLaw.rawItems before actions }
  feeRequest : fee.val.request = deliveryFee
  feePaid : auditLaw.Valid fee.val.before fee.val.request
  consecutive : fee.val.index = access.val.index + 1

private abbrev operationDecidableEq : DecidableEq (Operation Party Good (Mandate.State Party Technology) Unit) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq Action := by
  letI := operationDecidableEq
  intro left right
  cases left
  cases right
  simp only [Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

/-- An independent consumer enumerates original accepted commands, both
grant signatures, the actual service debit and its following delivery fee. -/
def deliveries (before : AuditCurrent) (actions : List Action) (query : Query) :
    List (Delivery before actions query) :=
  (Mandate.commandsAt baseLaw scope before actions).flatMap fun withdrawal =>
    (Mandate.grantsAt baseLaw scope before actions).flatMap fun grant =>
      (auditLaw.rawItems before actions).attach.flatMap fun access =>
        (auditLaw.rawItems before actions).attach.filterMap fun fee =>
          if linked : withdrawal.command = .revoke ∧
              (grant.candidate = 1 ∨ grant.candidate = 2) ∧
              withdrawal.item.val.before.technology.holder ≠ some grant.candidate ∧
              withdrawal.item.val.request.signer = grant.proposal.item.val.request.signer ∧
              withdrawal.after.technology = grant.proposal.item.val.before.technology ∧
              withdrawal.item.val.index < grant.proposal.item.val.index ∧
              access.val.request = Scoped.accessRequest grant.candidate query ∧
              auditLaw.Valid access.val.before access.val.request ∧
              grant.acceptance.after.technology = access.val.before.technology ∧
              grant.acceptance.item.val.index < access.val.index ∧
              fee.val.request = deliveryFee ∧ auditLaw.Valid fee.val.before fee.val.request ∧
              fee.val.index = access.val.index + 1 then
            some ⟨withdrawal,linked.1,grant,linked.2.1,linked.2.2.1,linked.2.2.2.1,
              linked.2.2.2.2.1,linked.2.2.2.2.2.1,access,linked.2.2.2.2.2.2.1,
              linked.2.2.2.2.2.2.2.1,linked.2.2.2.2.2.2.2.2.1,
              linked.2.2.2.2.2.2.2.2.2.1,fee,linked.2.2.2.2.2.2.2.2.2.2.1,
              linked.2.2.2.2.2.2.2.2.2.2.2.1,linked.2.2.2.2.2.2.2.2.2.2.2.2⟩
          else none

namespace Delivery
variable {before : AuditCurrent} {actions : List Action} {query : Query}
  (receipt : Delivery before actions query)

theorem withdrawal_is_real : receipt.withdrawal.after.technology.holder = none ∧
    receipt.withdrawal.after.technology.offered = none ∧
    receipt.withdrawal.after.technology.version =
      receipt.withdrawal.item.val.before.technology.version + 1 := by
  rw [receipt.withdrawal.actual_effect.1,receipt.withdrawn]
  simp [Mandate.advance]

theorem withdrawal_costs_labor :
    receipt.withdrawal.after.stock receipt.withdrawal.operator .labor + 1 =
      receipt.withdrawal.item.val.before.stock receipt.withdrawal.operator .labor := by
  have balance := receipt.withdrawal.actual_cost receipt.withdrawal.operator .labor
  simpa [RawLaw.debit,receipt.withdrawal.operation,auditLaw,Mandate.law,scope,
    flowAt,locate,amount] using balance

theorem replacement_has_native_authority :
    receipt.access.val.before.technology.holder = some receipt.grant.candidate ∧
    auditTask.earliest ≤ receipt.access.val.before.clock ∧
    receipt.access.val.before.clock ≤ auditTask.deadline := by
  have paid := receipt.accessPaid
  rw [receipt.accessRequest,access_valid_iff] at paid
  exact ⟨paid.1,paid.2.1,paid.2.2.1⟩

theorem replacement_pays_for_service :
    (auditLaw.step receipt.access.val.before receipt.access.val.request).stock receipt.grant.candidate .labor + 1 =
      receipt.access.val.before.stock receipt.grant.candidate .labor := by
  have balance := auditLaw.material_step_balance receipt.access.val.before
    receipt.access.val.request receipt.grant.candidate .labor
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos receipt.accessPaid] at balance
  simpa [receipt.accessRequest,
    RawLaw.debit,RawLaw.credit,Scoped.accessRequest,flowAt,locate,amount] using balance

theorem delivery_is_separately_paid :
    (auditLaw.step receipt.fee.val.before receipt.fee.val.request).stock 0 .labor + 1 =
      receipt.fee.val.before.stock 0 .labor := by
  have balance := auditLaw.material_step_balance receipt.fee.val.before receipt.fee.val.request 0 .labor
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos receipt.feePaid] at balance
  simpa [receipt.feeRequest,
    RawLaw.debit,RawLaw.credit,deliveryFee,flowAt,locate,amount] using balance

def record : Record := serve (permittedView receipt.access.val.before)
  (receipt.access.val.before.round - initial.round) receipt.grant.candidate query

theorem record_is_admitted : receipt.record.access = .admitted := by
  have paid := receipt.accessPaid
  rw [receipt.accessRequest,access_valid_iff] at paid
  rcases receipt.supported with candidate | candidate
  all_goals
    rcases paid with ⟨holder,earliest,deadline,labor,owner⟩
    simp only [candidate] at holder labor owner ⊢
    simp only [record,serve,decision,permittedView,BoundedDisclosure.accessDecision]
    simp only [candidate] at *
    have window : BoundedDisclosure.auditTask.earliest ≤ receipt.access.val.before.clock ∧
        receipt.access.val.before.clock ≤ BoundedDisclosure.auditTask.deadline := ⟨earliest,deadline⟩
    simp_all

theorem disclosed_evidence_keeps_original_service (slot : Slot) (evidence : Evidence)
    (released : (slot,evidence) ∈ receipt.record.evidence)
    (verified : lifecycleCheck slot evidence = .verified) : source.ActualSlotPaid 1 (originalIndex slot) :=
  lifecycle_acceptance_is_the_original_whole_slot _ _ _ _ _ _ released verified

end Delivery

structure Packet where
  accessIndex : Nat
  payload : Record
  deriving DecidableEq

/-- The producer discloses only the current raw access, with its actual
following fee. The old six-slot archive supplies the requested contents. -/
def release (before : AuditCurrent) (actions : List Action) : List Packet :=
  (auditLaw.rawItems before actions).flatMap fun access =>
    match access.request.purpose.query with
    | none => []
    | some query =>
      (auditLaw.rawItems before actions).filterMap fun fee =>
        if access.request = Scoped.accessRequest access.request.signer query ∧
            auditLaw.Valid access.before access.request ∧
            fee.index = access.index + 1 ∧ fee.request = deliveryFee ∧ auditLaw.Valid fee.before fee.request then
          some ⟨access.index,serve (permittedView access.before) (access.before.round - initial.round)
            access.request.signer query⟩
        else none

/-- The consumer receives the delivered bytes as data and independently
reconstructs authority, both costs and the exact source projection. -/
def verify (before : AuditCurrent) (actions : List Action) (packet : Packet) : Bool :=
  (deliveries before actions packet.payload.query).any fun receipt =>
    decide (receipt.access.val.index = packet.accessIndex ∧ receipt.record = packet.payload)

theorem verified_packet_has_actual_delivery (before : AuditCurrent) (actions : List Action) (packet : Packet)
    (accepted : verify before actions packet = true) :
    ∃ receipt ∈ deliveries before actions packet.payload.query,
      receipt.access.val.index = packet.accessIndex ∧ receipt.record = packet.payload := by
  simpa only [verify,List.any_eq_true,decide_eq_true_eq] using accepted

private theorem silent_step (before : AuditCurrent) (action : Action) (silent : Silent action) :
    (auditLaw.step before action).claims = before.claims := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims before action = before.claims
    rcases action with ⟨signer,consents,purpose,gates,operation⟩
    cases operation <;> simp_all [Silent,RawLaw.nextClaims]
  · rfl

private theorem silent_execute (before : AuditCurrent) (index : Nat) (actions : List Action)
    (silent : ∀ action ∈ actions,Silent action) :
    (auditLaw.execute before index actions).final.claims = before.claims := by
  induction actions generalizing before index with
  | nil => rfl
  | cons head tail ih =>
    change (auditLaw.execute (auditLaw.step before head) (index + 1) tail).final.claims = _
    rw [ih _ _ (fun action inside => silent action (List.mem_cons_of_mem _ inside)),
      silent_step before head (silent head List.mem_cons_self)]

private theorem attempt_silent (before : AuditCurrent) (stages : List (AuditCurrent → Action))
    (silent : ∀ stage ∈ stages,∀ current,Silent (stage current)) :
    ∀ action ∈ attempt before stages,Silent action := by
  induction stages generalizing before with
  | nil => simp [attempt]
  | cons stage rest ih =>
    simp only [attempt]
    split
    · intro action inside
      rcases List.mem_cons.mp inside with rfl | inside
      · exact silent stage List.mem_cons_self before
      · exact ih _ (fun stage inside => silent stage (List.mem_cons_of_mem _ inside)) action inside
    · intro action inside
      exact List.mem_singleton.mp inside ▸ silent stage List.mem_cons_self before

private theorem fund_silent (before : AuditCurrent) (challenger : Party) (donors : List Party) :
    ∀ action ∈ fund before challenger donors,Silent action := by
  induction donors generalizing before with
  | nil => simp [fund]
  | cons donor rest ih =>
    simp only [fund]
    split
    · intro action inside
      rcases List.mem_cons.mp inside with rfl | inside
      · trivial
      · exact ih _ action inside
    · exact ih _

theorem response_preserves_all_original_claims (before : AuditCurrent) (expected : Record) (objection : Objection) :
    (auditLaw.next before (word before expected objection)).claims = before.claims := by
  apply silent_execute
  unfold word
  split
  · intro action inside
    rcases List.mem_cons.mp inside with rfl | inside
    · trivial
    · rcases List.mem_append.mp inside with inside | inside
      · exact fund_silent _ _ _ action inside
      · split at inside
        · exact List.mem_singleton.mp inside ▸ (show Silent (command _ _ .revoke) from True.intro)
        · apply attempt_silent _ _ _ action inside
          intro stage member current
          simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Response

import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Source
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Origin

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
open Institutions.Capitalism.Universal.Source.Program

/-- Fixed by the task and permission mechanism before any verifier output. -/
structure PublicView where
  permission : Mandate.State Party Technology
  clock : ℚ
  ownerLabor : ℚ
  firstLabor : ℚ
  secondLabor : ℚ
  deriving DecidableEq

def permittedView (state : AuditCurrent) : PublicView :=
  ⟨state.technology,state.clock,state.stock 0 .labor,state.stock 1 .labor,state.stock 2 .labor⟩

inductive Access where
  | admitted | unauthorized | expired | unfunded
  deriving DecidableEq

structure Record where
  requester : Party
  requested : List Field
  access : Access
  released : List Field
  evidence : Evidence
  trace : Verdict
  lifecycle : Verdict
  version : Nat
  clock : ℚ
  laborCost : ℚ
  originalSlot : Nat
  deriving DecidableEq

def emptyEvidence : Evidence := ⟨none,none⟩
def authorizedFields : List Field := [.admission,.payment]

def accessDecision (view : PublicView) (actor : Party) : Access :=
  if actor ≠ 1 ∧ actor ≠ 2 ∨ view.permission.holder ≠ some actor then .unauthorized
  else if ¬ (auditTask.earliest ≤ view.clock ∧ view.clock ≤ auditTask.deadline) then .expired
  else if view.ownerLabor < 1 ∨ (if actor = 1 then view.firstLabor else view.secondLabor) < 1 then .unfunded
  else .admitted

def serve (view : PublicView) (actor : Party) (fields : List Field) : Record :=
  let access := accessDecision view actor
  let released := if access = .admitted then fields.filter (· ∈ authorizedFields) else []
  let evidence := restrict released originalEvidence
  ⟨actor,fields,access,released,evidence,traceCheck evidence,lifecycleCheck evidence,
    view.permission.version,view.clock,if access = .admitted then 2 else 0,0⟩

theorem raw_access_iff (before : AuditCurrent) (actor : Party) :
    auditLaw.Valid before (accessRequest actor) ↔
      before.technology.holder = some actor ∧ auditTask.earliest ≤ before.clock ∧
      before.clock ≤ auditTask.deadline ∧ 1 ≤ before.stock actor .labor := by
  simp [auditLaw,accessRequest,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Cell.law,
    scope,NonnegativeBundle,locate,flowAt,amount]
  tauto

def actualLaborDebit (larger : Bool) (ordinal : Nat) : ℚ :=
  ([0,1,2,3].map fun actor =>
    auditLaw.totalDebit (auditLaw.rawItems (current larger ordinal) (emit larger (current larger ordinal)))
      actor .labor).sum

theorem actual_query_debits (larger : Bool) :
    [actualLaborDebit larger 4,actualLaborDebit larger 6,
     actualLaborDebit larger 7,actualLaborDebit larger 8] = [2,0,2,2] := by
  cases larger <;> decide +kernel

def actualQueryActors (word : List AuditRequest) : List Party :=
  word.filterMap fun request => if request.gates = [.machine] then some request.signer else none

/-- Strategies see the pooled access log, never a private state or its input bit. -/
abbrev Strategy := List Record → Nat → List Field

def journal (larger : Bool) (strategy : Strategy) : Nat → List Record
  | 0 => []
  | n + 1 =>
    let past := journal larger strategy n
    match (actualQueryActors (emit larger (current larger n))).head? with
    | none => past
    | some actor => past ++ [serve (permittedView (current larger n)) actor (strategy past n)]

def defaultStrategy : Strategy := fun _ ordinal => if ordinal = 7 then [.admission] else authorizedFields

def missingFields (evidence : Evidence) : List Field :=
  (if evidence.admission.isNone then [.admission] else []) ++
    (if evidence.payment.isNone then [.payment] else [])

inductive Followup where
  | permissionReview (originalSlot member requester : Nat)
  | evidence (originalSlot requester : Nat) (needed : List Field)
  deriving DecidableEq

def nextRequest (record : Record) : Option Followup :=
  if record.access ≠ .admitted then some (.permissionReview record.originalSlot 0 record.requester)
  else if record.trace = .verified ∧ record.lifecycle = .verified then none
  else some (.evidence record.originalSlot record.requester
    (if (missingFields record.evidence).isEmpty then authorizedFields else missingFields record.evidence))

theorem insufficient_evidence_names_the_missing_category (larger : Bool) :
    nextRequest (serve (permittedView (current larger 7)) 2 [.admission]) =
      some (.evidence 0 2 [.payment]) ∧
    nextRequest (serve (permittedView (current larger 8)) 2 authorizedFields) = none := by
  cases larger <;> decide +kernel

theorem permission_projection_is_private_input_independent (ordinal : Fin 10) :
    permittedView (current false ordinal.val) = permittedView (current true ordinal.val) := by
  rcases ordinal with ⟨ordinal,bound⟩
  interval_cases ordinal <;> decide +kernel +revert

theorem query_actors_are_private_input_independent (ordinal : Fin 10) :
    actualQueryActors (emit false (current false ordinal.val)) =
      actualQueryActors (emit true (current true ordinal.val)) := by
  rcases ordinal with ⟨ordinal,bound⟩
  interval_cases ordinal <;> decide +kernel +revert

theorem cumulative_disclosure_is_private_input_independent (strategy : Strategy)
    (count : Nat) (within : count ≤ 10) : journal false strategy count = journal true strategy count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have prior := ih (by omega)
      have same := permission_projection_is_private_input_independent ⟨count,by omega⟩
      have query := query_actors_are_private_input_independent ⟨count,by omega⟩
      simp only [journal,prior,same,query]

theorem actual_default_delivery_and_handoff (larger : Bool) :
    ((journal larger defaultStrategy 9).map Record.access) =
      [.admitted,.unauthorized,.admitted,.admitted] ∧
    ((journal larger defaultStrategy 9).map Record.trace) =
      [.verified,.insufficient,.insufficient,.verified] ∧
    ((journal larger defaultStrategy 9).map Record.lifecycle) =
      [.verified,.insufficient,.insufficient,.verified] ∧
    ((journal larger defaultStrategy 9).map Record.requester) = [1,1,2,2] ∧
    ((journal larger defaultStrategy 9).map Record.laborCost).sum = 6 := by
  cases larger <;> decide +kernel

theorem denial_does_not_disclose (view : PublicView) (actor : Party) (fields : List Field)
    (denied : accessDecision view actor ≠ .admitted) :
    (serve view actor fields).released = [] ∧ (serve view actor fields).evidence = emptyEvidence := by
  simp [serve,denied,restrict,emptyEvidence]

theorem served_evidence_has_source_origin (view : PublicView) (actor : Party) (fields : List Field) :
    Origin (serve view actor fields).evidence :=
  restrict_has_origin _ _ original_evidence_has_origin

theorem every_successful_trace_is_original (view : PublicView) (actor : Party) (fields : List Field)
    (accepted : (serve view actor fields).trace = .verified) : Cell.source.ActualSlotPaid 1 originalSlot :=
  trace_verifies_original_delivery _ (served_evidence_has_source_origin view actor fields) accepted

theorem every_successful_lifecycle_is_original (view : PublicView) (actor : Party) (fields : List Field)
    (accepted : (serve view actor fields).lifecycle = .verified) : Cell.source.ActualSlotPaid 1 originalSlot :=
  lifecycle_verifies_original_delivery _ (served_evidence_has_source_origin view actor fields) accepted

/-- A similar-looking actor has no audit admission, even with the complete field request. -/
theorem non_auditor_is_denied :
    (serve (permittedView (current false 4)) 0 authorizedFields).access = .unauthorized := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure

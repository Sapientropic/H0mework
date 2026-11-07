import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Service
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Actual

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
open Institutions.Capitalism.Universal.Source.Program

/-- Select the first responsibility from the original generated directory. -/
def originalSlot : Cell.source.Slot :=
  (List.finRange Cell.source.seed.task.slots.length).head (by decide +kernel)

def originalPayment := Audit.actualPayment 2 (by decide) originalSlot

def paidAfter : Cell.Current := (Cell.source.frameAt 2).raw

abbrev AuditCurrent := RawCurrent Party Good (Mandate.State Party Technology) Unit
abbrev AuditRequest := Request Party Good Port (Mandate.State Party Technology) Unit

def inherit (current : Cell.Current) : AuditCurrent :=
  ⟨current.stock,current.claims,⟨current.technology,0,none,none,none⟩,current.clock,current.round⟩

def initial : AuditCurrent := inherit paidAfter

theorem erase_inherit (current : Cell.Current) : Mandate.eraseCurrent (inherit current) = current := by
  cases current
  rfl

theorem starts_after_the_original_payment :
    Mandate.eraseCurrent initial = (Cell.source.actualExecution 0).after :=
  (erase_inherit _).trans (Cell.source.actual_execution_after 0).symm

theorem original_delivery_has_its_original_occurrence :
    originalPayment.visit = Audit.visitData 1 ∧
    originalPayment.item ∈ (Cell.source.actualExecution 0).interpreted.items ∧
    Cell.source.ActualSlotPaid 1 originalSlot :=
  Audit.actual_payment_is_the_original_occurrence 2 (by decide) originalSlot

/-- The audit has its own window; the original delivery window is unchanged. -/
def auditTask : PublicTaskSpec Party Good :=
  ⟨[⟨(Cell.source.seed.slot originalSlot).bearer,[(.labor,1)],.contribution⟩],
    initial.clock,initial.clock+20,by decide +kernel⟩

def scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port) :=
  ⟨auditTask,.machine,.revision,by decide,[(.labor,1)]⟩

def auditLaw := Mandate.law Cell.law scope

def command (current : AuditCurrent) (actor : Party) (kind : Mandate.Command Party) : AuditRequest :=
  Mandate.request scope current actor kind

def transferLabor (actor : Party) : AuditRequest :=
  ⟨3,[],.common,[],.transfer 3 actor [(.labor,3)]⟩

def preparation : List AuditRequest := [transferLabor 1,transferLabor 2]

def prepared := auditLaw.next initial preparation

def authorization (current : AuditCurrent) (actor : Party) : List AuditRequest :=
  let first := command current (Cell.source.seed.slot originalSlot).bearer (.propose actor)
  [first,command (auditLaw.step current first) actor .accept]

def firstAuthorization := authorization prepared 1

def firstAuthorized := auditLaw.next prepared firstAuthorization

def handoff (current : AuditCurrent) : List AuditRequest :=
  let withdrawal := command current (Cell.source.seed.slot originalSlot).bearer .revoke
  withdrawal :: authorization (auditLaw.step current withdrawal) 2

def secondAuthorized := auditLaw.next firstAuthorized (handoff firstAuthorized)

def accessRequest (actor : Party) : AuditRequest :=
  ⟨actor,[],.machine,[.machine],.use actor [(.labor,1)] .external⟩

def ClaimSilent (action : AuditRequest) : Prop := match action.operation with
  | .issue .. | .assign .. | .settle .. => False
  | _ => True

theorem silent_step (current : AuditCurrent) (action : AuditRequest) (silent : ClaimSilent action) :
    (auditLaw.step current action).claims = current.claims := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims current action = current.claims
    rcases action with ⟨signer, consents, purpose, gates, operation⟩
    cases operation <;> simp_all [ClaimSilent, RawLaw.nextClaims]
  · rfl

theorem silent_execute (current : AuditCurrent) (index : Nat) (word : List AuditRequest)
    (silent : ∀ action ∈ word, ClaimSilent action) :
    (auditLaw.execute current index word).final.claims = current.claims := by
  induction word generalizing current index with
  | nil => rfl
  | cons action tail ih =>
      change (auditLaw.execute (auditLaw.step current action) (index + 1) tail).final.claims = _
      rw [ih _ _ (fun next inside => silent next (List.mem_cons_of_mem _ inside)),
        silent_step current action (silent action List.mem_cons_self)]

theorem authorization_silent (current : AuditCurrent) (actor : Party) :
    ∀ action ∈ authorization current actor, ClaimSilent action := by
  intro action inside
  simp only [authorization, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> trivial

theorem preparation_preserves_claims : prepared.claims = initial.claims :=
  silent_execute _ _ _ (by simp [preparation, transferLabor, ClaimSilent])

theorem first_authorization_preserves_claims : firstAuthorized.claims = initial.claims :=
  (silent_execute _ _ _ (authorization_silent _ _)).trans preparation_preserves_claims

theorem handoff_preserves_claims : secondAuthorized.claims = initial.claims := by
  apply Eq.trans (silent_execute _ _ _ ?_) first_authorization_preserves_claims
  intro action inside
  rcases List.mem_cons.mp inside with rfl | rest
  · trivial
  · exact authorization_silent _ _ action rest

theorem preparation_is_actually_affordable :
    ∀ item ∈ auditLaw.rawItems initial preparation, auditLaw.Valid item.before item.request := by
  decide +kernel

theorem first_authorization_is_actually_paid :
    (∀ item ∈ auditLaw.rawItems prepared firstAuthorization, auditLaw.Valid item.before item.request) ∧
    firstAuthorized.technology.holder = some 1 ∧ firstAuthorized.technology.version = 2 ∧
    firstAuthorized.claims = initial.claims := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  exact first_authorization_preserves_claims

def firstGrant : Mandate.Grant Cell.law scope prepared firstAuthorization :=
  (Mandate.grantsAt Cell.law scope prepared firstAuthorization).head (by decide +kernel)

theorem first_grant_is_generated_from_two_actual_commands :
    firstGrant ∈ Mandate.grantsAt Cell.law scope prepared firstAuthorization := firstGrant.is_enumerated

theorem handoff_is_actually_paid :
    (∀ item ∈ auditLaw.rawItems firstAuthorized (handoff firstAuthorized), auditLaw.Valid item.before item.request) ∧
    secondAuthorized.technology.holder = some 2 ∧ secondAuthorized.technology.version = 5 ∧
    secondAuthorized.claims = initial.claims := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  exact handoff_preserves_claims

def secondGrant : Mandate.Grant Cell.law scope firstAuthorized (handoff firstAuthorized) :=
  (Mandate.grantsAt Cell.law scope firstAuthorized (handoff firstAuthorized)).head (by decide +kernel)

theorem access_follows_actual_authorization :
    auditLaw.Valid firstAuthorized (accessRequest 1) ∧
    ¬ auditLaw.Valid secondAuthorized (accessRequest 1) ∧
    auditLaw.Valid secondAuthorized (accessRequest 2) := by
  decide +kernel

theorem authorization_keeps_the_original_debt (instrument : Unit) (debtor creditor : Party) :
    secondAuthorized.claims instrument debtor creditor = paidAfter.claims instrument debtor creditor :=
  congrFun (congrFun (congrFun handoff_preserves_claims instrument) debtor) creditor

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure

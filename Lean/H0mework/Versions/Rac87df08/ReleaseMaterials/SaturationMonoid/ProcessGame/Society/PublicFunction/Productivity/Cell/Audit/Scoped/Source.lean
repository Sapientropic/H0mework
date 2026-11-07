import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Evidence
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Carrier

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- Query masks travel in the actual request port, not a parallel request log. -/
structure AuditPort where
  base : Cell.Port
  query : Option Query := none
  deriving DecidableEq

def native (port : Cell.Port) : AuditPort := ⟨port,none⟩
abbrev AuditCurrent := BoundedDisclosure.AuditCurrent
abbrev Action := Request Party Good AuditPort (Mandate.State Party Technology) Unit
def initial : AuditCurrent := BoundedDisclosure.initial

def erasePort (request : Request Party Good AuditPort Technology Unit) : RequestAt :=
  ⟨request.signer,request.consents,request.purpose.base,request.gates.map AuditPort.base,request.operation⟩

def baseLaw : RawLaw Party Good AuditPort Technology Unit where
  technique := fun technology actor =>
    let technique := Cell.law.technique technology actor
    ⟨technique.inputs,technique.outputs,technique.maintenance,technique.requiredPorts.map native⟩
  controller := fun technology port => Cell.law.controller technology port.base
  allowed := fun technology port actor => Cell.law.allowed technology port.base actor
  stockPort := fun technology actor good => native (Cell.law.stockPort technology actor good)
  revisionPort := fun technology => native (Cell.law.revisionPort technology)
  revisionCost := Cell.law.revisionCost
  settlementUnit := Cell.law.settlementUnit
  settlementRate := Cell.law.settlementRate
  issuerPort := fun instrument => native (Cell.law.issuerPort instrument)
  necessities := Cell.law.necessities
  mandatoryMaintenance := Cell.law.mandatoryMaintenance
  policy := .opaque (fun current request => Cell.law.operationAllowed current (erasePort request) &&
    decide (request.purpose.query.isSome →
      (if request.signer = 0 then 2 else 1) ≤ current.stock 0 .labor))
  duration := Cell.law.duration

def auditTask : PublicTaskSpec Party Good :=
  ⟨Cell.source.seed.task.slots.map (fun slot => ⟨slot.bearer,[(.labor,1)],.contribution⟩),
    initial.clock,initial.clock + 20,by decide +kernel⟩

def scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort) :=
  ⟨auditTask,native .machine,native .revision,by decide,[(.labor,1)]⟩
def auditLaw := Mandate.law baseLaw scope

def command (before : AuditCurrent) (actor : Party) (kind : Mandate.Command Party) : Action :=
  Mandate.request scope before actor kind
def transferLabor (recipient : Party) (quantity : ℚ) : Action :=
  ⟨3,[],native .common,[],.transfer 3 recipient [(.labor,quantity)]⟩
def preparation : List Action := [transferLabor 1 3,transferLabor 2 3]
def refill : List Action := [transferLabor 0 2,transferLabor 2 4]
def authorization (before : AuditCurrent) (actor : Party) : List Action :=
  let proposal := command before 0 (.propose actor)
  [proposal,command (auditLaw.step before proposal) actor .accept]
def handoff (before : AuditCurrent) : List Action :=
  let withdrawal := command before 0 .revoke
  withdrawal :: authorization (auditLaw.step before withdrawal) 2
def privateUse (larger : Bool) : Action :=
  ⟨3,[],native .common,[],.use 3 [(.feed,if larger then 2 else 1)] .external⟩
def accessRequest (actor : Party) (query : Query) : Action :=
  ⟨actor,[],⟨.common,some query⟩,[native .machine],.use actor [(.labor,1)] .external⟩
def deliveryFee : Action := ⟨0,[],native .common,[],.use 0 [(.labor,1)] .external⟩

theorem access_valid_iff (before : AuditCurrent) (actor : Party) (query : Query) :
    auditLaw.Valid before (accessRequest actor query) ↔ before.technology.holder = some actor ∧
      auditTask.earliest ≤ before.clock ∧ before.clock ≤ auditTask.deadline ∧
      1 ≤ before.stock actor .labor ∧ (if actor = 0 then 2 else 1) ≤ before.stock 0 .labor := by
  simp [auditLaw,accessRequest,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,
    baseLaw,erasePort,Cell.law,scope,native,NonnegativeBundle,locate,flowAt,amount]
  tauto

def readWord (before : AuditCurrent) (actor : Party) (query : Query) : List Action :=
  let access := accessRequest actor query
  if auditLaw.Valid before access ∧ auditLaw.Valid (auditLaw.step before access) deliveryFee
  then [access,deliveryFee] else [access]

def defaultQuery (ordinal : Nat) : Query := ⟨63,if ordinal = 7 then 1 else 3⟩

def emit (queries : Nat → Query) (larger : Bool) (before : AuditCurrent) : List Action :=
  let phase := before.round - initial.round
  match phase with
  | 1 => preparation
  | 2 => authorization before 1
  | 3 => [privateUse larger]
  | 4 => readWord before 1 (queries phase)
  | 5 => handoff before
  | 6 => readWord before 1 (queries phase)
  | 7 | 8 => readWord before 2 (queries phase)
  | 9 => refill
  | _ => if 10 ≤ phase then readWord before 2 (queries phase) else []

def input (queries : Nat → Query) (larger : Bool) :
    ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { law := auditLaw,initial := initial,instructions := [],emission? := some (emit queries larger) }

def current (queries : Nat → Query) (larger : Bool) : Nat → AuditCurrent :=
  Nat.rec initial (fun n before => auditLaw.next before (if n = 0 then [] else emit queries larger before))

theorem current_zero (queries : Nat → Query) (larger : Bool) : current queries larger 0 = initial := rfl
theorem current_succ (queries : Nat → Query) (larger : Bool) (n : Nat) :
    current queries larger (n + 1) =
      auditLaw.next (current queries larger n) (if n = 0 then [] else emit queries larger (current queries larger n)) := rfl

theorem current_is_own_root_current (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    ProgrammeSource.rawCurrent (input queries larger) (ProgrammeHistory.visitAt (input queries larger) ordinal).current =
      current queries larger ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      change ProgrammeSource.rawCurrent (input queries larger)
        (ProgrammeSource.next (input queries larger) (ProgrammeHistory.visitAt (input queries larger) ordinal).current) = _
      rw [ProgrammeSource.actual_raw_next,ih]
      cases ordinal with
      | zero => rfl
      | succ ordinal =>
          have word : ProgrammeSource.rawEvent (input queries larger)
              (ProgrammeHistory.visitAt (input queries larger) (ordinal + 1)).current =
              emit queries larger (current queries larger (ordinal + 1)) := by
            rw [← ih]
            change ProgrammeSource.rawEvent (input queries larger) (ProgrammeSource.next (input queries larger)
              (ProgrammeHistory.visitAt (input queries larger) ordinal).current) =
                emit queries larger (ProgrammeSource.rawCurrent (input queries larger)
                  (ProgrammeSource.next (input queries larger) (ProgrammeHistory.visitAt (input queries larger) ordinal).current))
            generalize (ProgrammeHistory.visitAt (input queries larger) ordinal).current = prior
            cases prior <;> rfl
          exact congrArg (auditLaw.next _) word

-- Rewrites use the recurrence explicitly; unification must not replay a long prefix.
attribute [irreducible] current

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped

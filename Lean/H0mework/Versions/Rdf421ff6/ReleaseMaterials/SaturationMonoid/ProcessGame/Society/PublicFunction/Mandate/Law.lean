import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.Law

/-! Task authority is issued by two real revisions: a task member proposes,
then the proposed holder signs acceptance. Revision targets are checked
against the current state and a fresh version, never trusted as mandates. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate

open Institutions.Capitalism.Universal.Source.Program

inductive Command (Party : Type)
  | propose (candidate : Party)
  | accept | renew | exit | revoke | review
  deriving DecidableEq

structure State (Party Technology : Type) where
  technology : Technology
  version : Nat
  holder : Option Party
  offered : Option Party
  last : Option (Command Party)
  deriving DecidableEq

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

abbrev Scope := Delegation.Jurisdiction Party Good Port

def eraseCurrent (current : RawCurrent Party Good (State Party Technology) Instrument) :
    RawCurrent Party Good Technology Instrument :=
  ⟨current.stock, current.claims, current.technology.technology, current.clock, current.round⟩

def eraseOperation : Operation Party Good (State Party Technology) Instrument →
    Operation Party Good Technology Instrument
  | .produce actor => .produce actor
  | .transfer sender recipient goods => .transfer sender recipient goods
  | .use bearer goods purpose => .use bearer goods purpose
  | .issue code debtor creditor quantity => .issue code debtor creditor quantity
  | .assign code debtor sender recipient quantity => .assign code debtor sender recipient quantity
  | .settle code debtor creditor quantity => .settle code debtor creditor quantity
  | .revise actor target => .revise actor target.technology
  | .present => .present

def eraseRequest (request : Request Party Good Port (State Party Technology) Instrument) :
    Request Party Good Port Technology Instrument :=
  ⟨request.signer, request.consents, request.purpose, request.gates, eraseOperation request.operation⟩

def TaskUse (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (request : Request Party Good Port (State Party Technology) Instrument) : Prop :=
  match request.operation with
  | .use bearer _ purpose => ∃ slot ∈ scope.task.slots,
      slot.bearer = bearer ∧ slot.purpose = purpose
  | _ => False

instance (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (request : Request Party Good Port (State Party Technology) Instrument) : Decidable (TaskUse scope request) := by
  unfold TaskUse
  cases request.operation <;> infer_instance

def CanRun (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) : Command Party → Prop
  | .propose _ => signer ∈ Delegation.members scope.task ∧ current.clock ≤ scope.task.deadline
  | .accept => current.technology.offered = some signer ∧ current.clock ≤ scope.task.deadline
  | .renew => current.technology.offered = some signer ∧
      current.technology.holder = some signer ∧ current.clock ≤ scope.task.deadline
  | .exit => current.technology.holder = some signer
  | .revoke => signer ∈ Delegation.members scope.task ∧
      (current.technology.holder.isSome = true ∨ current.technology.offered.isSome = true)
  | .review => signer ∈ Delegation.members scope.task

instance (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) (command : Command Party) : Decidable (CanRun scope current signer command) := by
  cases command <;> unfold CanRun <;> infer_instance

def advance (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (current : RawCurrent Party Good (State Party Technology) Instrument) (command : Command Party) :
    State Party Technology :=
  let marked := {current.technology with version := current.technology.version + 1, last := some command}
  match command with
  | .propose candidate => {marked with offered := some candidate}
  | .accept => {marked with holder := current.technology.offered, offered := none}
  | .renew => {marked with offered := none}
  | .exit | .revoke => {marked with holder := none, offered := none}
  | .review => if scope.task.deadline < current.clock then
      {marked with holder := none, offered := none} else marked

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem advance_version (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (current : RawCurrent Party Good (State Party Technology) Instrument) (command : Command Party) :
    (advance scope current command).version = current.technology.version + 1 := by
  cases command <;> simp [advance]
  split <;> rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem advance_last (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (current : RawCurrent Party Good (State Party Technology) Instrument) (command : Command Party) :
    (advance scope current command).last = some command := by
  cases command <;> simp [advance]
  split <;> rfl

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))

def law : RawLaw Party Good Port (State Party Technology) Instrument where
  technique := fun state => base.technique state.technology
  controller := fun state port => if port = scope.service then
      state.holder.getD (base.controller state.technology port) else base.controller state.technology port
  allowed := fun state port signer =>
    if port = scope.challenge then decide (signer ∈ Delegation.members scope.task ∨
      state.holder = some signer ∨ state.offered = some signer)
    else if port = scope.service then decide (state.holder = some signer)
    else base.allowed state.technology port signer
  stockPort := fun state => base.stockPort state.technology
  revisionPort := fun _ => scope.challenge
  revisionCost := fun _ _ => scope.revisionCost
  settlementUnit := base.settlementUnit
  settlementRate := base.settlementRate
  issuerPort := base.issuerPort
  necessities := fun current => base.necessities (eraseCurrent current)
  mandatoryMaintenance := fun current => base.mandatoryMaintenance (eraseCurrent current)
  policy := .opaque (fun current request => match request.operation with
    | .revise operator target => match target.last with
      | none => false
      | some command => decide (operator = request.signer ∧ request.consents = [] ∧
          request.purpose = scope.challenge ∧ request.gates = [scope.challenge] ∧
          target = advance scope current command ∧ CanRun scope current request.signer command)
    | _ => base.operationAllowed (eraseCurrent current) (eraseRequest request) &&
        decide (scope.service ∈ base.requiredPorts (eraseCurrent current) (eraseRequest request) ∨ TaskUse scope request →
          current.technology.holder = some request.signer ∧
          scope.task.earliest ≤ current.clock ∧ current.clock ≤ scope.task.deadline))
  duration := fun current => base.duration (eraseCurrent current)

def request (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) (command : Command Party) : Request Party Good Port (State Party Technology) Instrument :=
  ⟨signer, [], scope.challenge, [scope.challenge], .revise signer (advance scope current command)⟩

structure Resources (current : RawCurrent Party Good (State Party Technology) Instrument) (signer : Party) : Prop where
  nonnegative : NonnegativeBundle (Party × Good) (locate signer scope.revisionCost)
  independent : ∀ item ∈ locate signer scope.revisionCost,
    base.stockPort current.technology.technology item.1.1 item.1.2 ≠ scope.service ∧
    base.stockPort current.technology.technology item.1.1 item.1.2 ≠ scope.challenge ∧
    base.allowed current.technology.technology
      (base.stockPort current.technology.technology item.1.1 item.1.2) signer = true
  affordable : ∀ item ∈ locate signer scope.revisionCost,
    flowAt (locate signer scope.revisionCost) item.1.1 item.1.2 ≤ current.stock item.1.1 item.1.2

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem command_policy (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) (command : Command Party) :
    (law base scope).operationAllowed current (request scope current signer command) = true ↔
      CanRun scope current signer command := by
  simp [law, RawLaw.operationAllowed, RawPolicy.eval, request, advance_last scope current command]

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem independent_command_permission (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) (command : Command Party) (admitted : CanRun scope current signer command) :
    (law base scope).allowed current.technology scope.challenge signer = true := by
  have standing : signer ∈ Delegation.members scope.task ∨
      current.technology.holder = some signer ∨ current.technology.offered = some signer := by
    cases command with
    | propose _ => exact Or.inl admitted.1
    | accept => exact Or.inr (Or.inr admitted.1)
    | renew => exact Or.inr (Or.inl admitted.2.1)
    | exit => exact Or.inr (Or.inl admitted)
    | revoke => exact Or.inl admitted.1
    | review => exact Or.inl admitted
  simp [law, standing]

omit [DecidableEq Instrument] in
theorem generate_paid_command (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) (command : Command Party) (admitted : CanRun scope current signer command)
    (resources : Resources base scope current signer) :
    (law base scope).Valid current (request scope current signer command) := by
  refine ⟨⟨True.intro, (command_policy base scope current signer command).mpr admitted⟩,
    ?_, True.intro, resources.nonnegative, ?_, resources.affordable⟩
  · intro port inside
    change port ∈ [scope.challenge] ++ (locate signer scope.revisionCost).map
      (fun item => base.stockPort current.technology.technology item.1.1 item.1.2) ++ [scope.challenge] at inside
    simp only [List.mem_append, List.mem_singleton] at inside
    rcases inside with (rfl | cost) | rfl
    · exact Or.inl (independent_command_permission base scope current signer command admitted)
    · obtain ⟨item, present, rfl⟩ := List.mem_map.mp cost
      have independent := resources.independent item present
      simp only [law, if_neg independent.2.1, if_neg independent.1]
      exact Or.inl independent.2.2
    · exact Or.inl (independent_command_permission base scope current signer command admitted)
  · intro item impossible
    exact False.elim (List.not_mem_nil impossible)

theorem paid_command_effect (current : RawCurrent Party Good (State Party Technology) Instrument)
    (signer : Party) (command : Command Party)
    (accepted : (law base scope).Valid current (request scope current signer command)) :
    ((law base scope).step current (request scope current signer command)).technology = advance scope current command ∧
      ((law base scope).step current (request scope current signer command)).claims = current.claims := by
  simp only [RawLaw.step, if_pos accepted]
  exact ⟨rfl, rfl⟩

omit [DecidableEq Instrument] in
theorem protected_use_requires_current_holder
    (current : RawCurrent Party Good (State Party Technology) Instrument)
    (action : Request Party Good Port (State Party Technology) Instrument)
    (bearer : Party) (goods : Bundle Good) (purpose : Use)
    (operation : action.operation = .use bearer goods purpose) (taskUse : TaskUse scope action)
    (accepted : (law base scope).Valid current action) :
    current.technology.holder = some action.signer ∧
      scope.task.earliest ≤ current.clock ∧ current.clock ≤ scope.task.deadline := by
  have policy := accepted.1.2
  simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation,
    Bool.and_eq_true, decide_eq_true_eq] at policy
  exact policy.2 (Or.inr taskUse)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate

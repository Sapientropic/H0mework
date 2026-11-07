import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Origin

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.AuditLaw
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def Safe (action : Action) : Prop := match action.operation with
  | .transfer _ _ goods | .use _ goods .external => ∀ entry ∈ goods,entry.1 ≠ .feed
  | .revise _ _ | .present => True
  | _ => False

theorem debit {left right : AuditCurrent} (same : Twin left right) (action : Action) :
    auditLaw.debit left action = auditLaw.debit right action := by
  cases action.operation <;> simp only [RawLaw.debit,same.technology]
theorem credit {left right : AuditCurrent} (same : Twin left right) (action : Action) :
    auditLaw.credit left action = auditLaw.credit right action := by
  cases action.operation <;> simp only [RawLaw.credit,same.technology]

theorem policy {left right : AuditCurrent} (same : Twin left right) (action : Action) :
    auditLaw.operationAllowed left action = auditLaw.operationAllowed right action := by
  have labor := same.stock 0 .labor (by decide)
  cases operation : action.operation <;>
    simp [auditLaw,Mandate.law,RawLaw.operationAllowed,RawPolicy.eval,operation,
      baseLaw,Cell.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,
      erasePort,RawLaw.requiredPorts,RawLaw.debit,same.technology,same.clock,labor,
      Mandate.advance,same.canRun Scoped.scope]

theorem guard {left right : AuditCurrent} (same : Twin left right) (action : Action) :
    auditLaw.ClaimGuard left action ↔ auditLaw.ClaimGuard right action := by
  cases operation : action.operation with
  | use actor goods purpose =>
    cases purpose <;> simp [RawLaw.ClaimGuard,operation,auditLaw,Mandate.law,baseLaw,Cell.law,Mandate.eraseCurrent]
  | _ => simp [RawLaw.ClaimGuard,operation,same.claims]

theorem public_debit (current : AuditCurrent) (action : Action) (safe : Safe action) :
    ∀ entry ∈ auditLaw.debit current action,entry.1.2 ≠ .feed := by
  intro entry inside
  cases operation : action.operation <;> simp only [Safe,operation] at safe
  case transfer sender recipient goods =>
    simp only [RawLaw.debit,operation,locate,List.mem_map] at inside
    obtain ⟨item,member,rfl⟩ := inside
    exact safe item member
  case use actor goods purpose =>
    cases purpose <;> try contradiction
    simp only [RawLaw.debit,operation,locate,List.mem_map] at inside
    obtain ⟨item,member,rfl⟩ := inside
    exact safe item member
  case revise actor target =>
    simp only [auditLaw,RawLaw.debit,operation,Mandate.law,Scoped.scope,locate,List.map_cons,List.map_nil,List.mem_singleton] at inside
    subst entry
    simp
  case present => simp [RawLaw.debit,operation] at inside

theorem valid {left right : AuditCurrent} (same : Twin left right) (action : Action) (safe : Safe action) :
    auditLaw.Valid left action ↔ auditLaw.Valid right action := by
  have debits := debit same action
  have ports : auditLaw.requiredPorts left action = auditLaw.requiredPorts right action := by
    simp only [RawLaw.requiredPorts,debits,same.technology]
  have funded : (∀ entry ∈ auditLaw.debit left action,
      flowAt (auditLaw.debit left action) entry.1.1 entry.1.2 ≤ left.stock entry.1.1 entry.1.2) ↔
      (∀ entry ∈ auditLaw.debit right action,
      flowAt (auditLaw.debit right action) entry.1.1 entry.1.2 ≤ right.stock entry.1.1 entry.1.2) := by
    rw [← debits]
    constructor <;> intro paid entry member
    · rw [← same.stock entry.1.1 entry.1.2 (public_debit left action safe entry member)]
      exact paid entry member
    · rw [same.stock entry.1.1 entry.1.2 (public_debit left action safe entry member)]
      exact paid entry member
  unfold RawLaw.Valid
  rw [funded]
  simp only [policy same action,ports,same.technology,guard same action,debits,credit same action]

theorem paidStep {left right : AuditCurrent} (same : Twin left right) (action : Action) :
    Twin (auditLaw.paidStep left action) (auditLaw.paidStep right action) := by
  refine ⟨?_,same.clock,same.round,?_,?_⟩
  · cases action.operation <;> simp only [RawLaw.paidStep,same.technology]
  · cases action.operation <;> simp only [RawLaw.paidStep,RawLaw.nextClaims,same.claims]
  · intro actor good visible
    simp only [RawLaw.paidStep,same.stock actor good visible,debit same action,credit same action]

theorem step {left right : AuditCurrent} (same : Twin left right) (action : Action) (safe : Safe action) :
    Twin (auditLaw.step left action) (auditLaw.step right action) := by
  simp only [RawLaw.step,propext (valid same action safe)]
  split
  · exact paidStep same action
  · exact same

theorem execute {left right : AuditCurrent} (same : Twin left right) (word : List Action)
    (safe : ∀ action ∈ word,Safe action) (index : Nat) :
    Twin (auditLaw.execute left index word).final (auditLaw.execute right index word).final := by
  induction word generalizing left right index with
  | nil => exact same
  | cons action rest ih =>
    exact ih (step same action (safe _ (by simp)))
      (fun action member => safe _ (List.mem_cons_of_mem _ member)) (index+1)

theorem next {left right : AuditCurrent} (same : Twin left right) (word : List Action)
    (safe : ∀ action ∈ word,Safe action) : Twin (auditLaw.next left word) (auditLaw.next right word) := by
  have after := execute same word safe 0
  exact ⟨after.technology,congrArg (·+1) same.clock,congrArg Nat.succ same.round,after.claims,after.stock⟩

def Stable (stage : AuditCurrent → Action) : Prop :=
  (∀ left right,Twin left right → stage left = stage right) ∧ ∀ current,Safe (stage current)

theorem attempt_safe (current : AuditCurrent) (stages : List (AuditCurrent → Action))
    (stable : ∀ stage ∈ stages,Stable stage) : ∀ action ∈ EnergyRenewal.attempt auditLaw current stages,Safe action := by
  induction stages generalizing current with
  | nil => simp [EnergyRenewal.attempt]
  | cons stage rest ih =>
    simp only [EnergyRenewal.attempt]
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | member
      · exact (stable _ (by simp)).2 current
      · exact ih _ (fun stage member => stable _ (List.mem_cons_of_mem _ member)) _ member
    · intro action member
      cases List.mem_singleton.mp member
      exact (stable _ (by simp)).2 current

theorem attempt {left right : AuditCurrent} (same : Twin left right) (stages : List (AuditCurrent → Action))
    (stable : ∀ stage ∈ stages,Stable stage) :
    EnergyRenewal.attempt auditLaw left stages = EnergyRenewal.attempt auditLaw right stages := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage rest ih =>
    have head := stable stage (by simp)
    have equal := head.1 left right same
    simp only [EnergyRenewal.attempt,← equal,propext (valid same _ (head.2 left))]
    split
    · congr 1
      exact ih (step same _ (head.2 left)) (fun stage member => stable _ (List.mem_cons_of_mem _ member))
    · rfl

theorem all_valid {left right : AuditCurrent} (same : Twin left right) (word : List Action)
    (safe : ∀ action ∈ word,Safe action) (index : Nat) :
    (∀ item ∈ (auditLaw.execute left index word).items,auditLaw.Valid item.before item.request) ↔
      (∀ item ∈ (auditLaw.execute right index word).items,auditLaw.Valid item.before item.request) := by
  induction word generalizing left right index with
  | nil => simp [RawLaw.execute]
  | cons action rest ih =>
    simp only [RawLaw.execute,List.mem_cons,forall_eq_or_imp]
    rw [valid same _ (safe _ (by simp)),ih (step same _ (safe _ (by simp)))
      (fun action member => safe _ (List.mem_cons_of_mem _ member)) (index+1)]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.AuditLaw

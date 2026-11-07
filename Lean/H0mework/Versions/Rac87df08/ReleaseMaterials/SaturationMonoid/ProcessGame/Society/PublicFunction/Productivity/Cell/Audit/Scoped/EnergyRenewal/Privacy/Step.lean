import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- Permission is fixed before observing an output; private feed is retained in each source. -/
structure Twin (left right : AuditCurrent) : Prop where
  technology : left.technology = right.technology
  clock : left.clock = right.clock
  round : left.round = right.round
  claims : left.claims = right.claims
  stock : ∀ actor good, good ≠ .feed → left.stock actor good = right.stock actor good

abbrev Scope := Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)
def law (scope : Scope) := Mandate.law energyBase scope

theorem Twin.refl (current : AuditCurrent) : Twin current current := ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩

theorem Twin.advance {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (command : Mandate.Command Party) :
    Mandate.advance scope left command = Mandate.advance scope right command := by
  cases command <;> simp [Mandate.advance,same.technology,same.clock]

theorem Twin.command {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (actor : Party) (command : Mandate.Command Party) :
    Mandate.request scope left actor command = Mandate.request scope right actor command := by
  simp only [Mandate.request,same.advance scope command]

theorem Twin.debit {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) : (law scope).debit left action = (law scope).debit right action := by
  cases action.operation <;> simp only [RawLaw.debit,same.technology]

theorem Twin.credit {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) : (law scope).credit left action = (law scope).credit right action := by
  cases action.operation <;> simp only [RawLaw.credit,same.technology]

theorem Twin.canRun {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (actor : Party) (command : Mandate.Command Party) :
    Mandate.CanRun scope left actor command ↔ Mandate.CanRun scope right actor command := by
  cases command <;> simp only [Mandate.CanRun,same.technology,same.clock]

theorem Twin.policy {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) :
    (law scope).operationAllowed left action = (law scope).operationAllowed right action := by
  have energy := same.stock 0 .energy (by decide)
  cases operation : action.operation <;>
    simp [law,Mandate.law,RawLaw.operationAllowed,RawPolicy.eval,operation,
      energyBase,baseLaw,Cell.law,Mandate.eraseCurrent,Mandate.eraseRequest,
      Mandate.eraseOperation,erasePort,RawLaw.requiredPorts,RawLaw.debit,
      same.technology,same.clock,energy,Mandate.advance,same.canRun scope]

theorem Twin.guard {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) :
    (law scope).ClaimGuard left action ↔ (law scope).ClaimGuard right action := by
  cases operation : action.operation with
  | use actor goods purpose =>
    cases purpose <;> simp [RawLaw.ClaimGuard,operation,law,Mandate.law,energyBase,baseLaw,
      Cell.law,Mandate.eraseCurrent]
  | _ => simp [RawLaw.ClaimGuard,operation,same.claims]

/-- Funding is read only at actual debit entries, never at hidden inventory coordinates. -/
def PublicDebit (scope : Scope) (current : AuditCurrent) (action : Action) : Prop :=
  ∀ item ∈ (law scope).debit current action,item.1.2 ≠ .feed

theorem Twin.valid {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) (visible : PublicDebit scope left action) :
    (law scope).Valid left action ↔ (law scope).Valid right action := by
  have debit := same.debit scope action
  have credit := same.credit scope action
  have ports : (law scope).requiredPorts left action = (law scope).requiredPorts right action := by
    simp only [RawLaw.requiredPorts,debit,same.technology]
  have funded : (∀ item ∈ (law scope).debit left action,
      flowAt ((law scope).debit left action) item.1.1 item.1.2 ≤ left.stock item.1.1 item.1.2) ↔
      (∀ item ∈ (law scope).debit right action,
      flowAt ((law scope).debit right action) item.1.1 item.1.2 ≤ right.stock item.1.1 item.1.2) := by
    rw [← debit]
    constructor <;> intro paid item member
    · rw [← same.stock item.1.1 item.1.2 (visible item member)]
      exact paid item member
    · rw [same.stock item.1.1 item.1.2 (visible item member)]
      exact paid item member
  unfold RawLaw.Valid
  rw [funded]
  simp only [same.policy scope action,ports,same.technology,same.guard scope action,debit,credit]

theorem Twin.paidStep {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) :
    Twin ((law scope).paidStep left action) ((law scope).paidStep right action) := by
  refine ⟨?_,same.clock,same.round,?_,?_⟩
  · cases action.operation <;> simp only [RawLaw.paidStep,same.technology]
  · cases action.operation <;> simp only [RawLaw.paidStep,RawLaw.nextClaims,same.claims]
  · intro actor good visible
    simp only [RawLaw.paidStep,same.stock actor good visible,same.debit scope action,same.credit scope action]

theorem Twin.step {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (action : Action) (visible : PublicDebit scope left action) :
    Twin ((law scope).step left action) ((law scope).step right action) := by
  simp only [RawLaw.step,propext (same.valid scope action visible)]
  split
  · exact same.paidStep scope action
  · exact same

/-- The generated vocabulary is checked at its source, before execution. -/
def EnergyAction (action : Action) : Prop :=
  match action.operation with
  | .use _ goods .external | .transfer _ _ goods => ∀ entry ∈ goods,entry.1 = .energy
  | .revise _ _ => True
  | _ => False

theorem energy_public (scope : Scope) (cost : scope.revisionCost = [(.energy,1)])
    (current : AuditCurrent) (action : Action) (energy : EnergyAction action) : PublicDebit scope current action := by
  intro item member
  cases operation : action.operation <;> simp only [EnergyAction,operation] at energy
  case transfer sender recipient goods =>
    simp only [RawLaw.debit,operation,locate,List.mem_map] at member
    obtain ⟨entry,inside,rfl⟩ := member
    rw [energy entry inside]; simp
  case use actor goods purpose =>
    cases purpose <;> try contradiction
    simp only [RawLaw.debit,operation,locate,List.mem_map] at member
    obtain ⟨entry,inside,rfl⟩ := member
    rw [energy entry inside]; simp
  case revise actor target =>
    simp only [law,RawLaw.debit,operation,Mandate.law,cost,locate,List.map_cons,List.map_nil,
      List.mem_singleton] at member
    subst item
    simp


theorem Twin.execute {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (cost : scope.revisionCost = [(.energy,1)]) (word : List Action)
    (energy : ∀ action ∈ word, EnergyAction action) (index : Nat) :
    Twin ((law scope).execute left index word).final ((law scope).execute right index word).final := by
  induction word generalizing left right index with
  | nil => exact same
  | cons action rest ih =>
    apply ih (same.step scope action (energy_public scope cost left action (energy _ (by simp))))
    intro action inside
    exact energy action (List.mem_cons_of_mem _ inside)

theorem Twin.next {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (cost : scope.revisionCost = [(.energy,1)]) (word : List Action)
    (energy : ∀ action ∈ word, EnergyAction action) :
    Twin ((law scope).next left word) ((law scope).next right word) := by
  have executed := same.execute scope cost word energy 0
  exact ⟨executed.technology,congrArg (·+1) same.clock,congrArg Nat.succ same.round,
    executed.claims,executed.stock⟩

def StableStage (stage : AuditCurrent → Action) : Prop :=
  (∀ left right,Twin left right → stage left = stage right) ∧ ∀ current,EnergyAction (stage current)

theorem attempt_energy (scope : Scope) (current : AuditCurrent) (stages : List (AuditCurrent → Action))
    (stable : ∀ stage ∈ stages, StableStage stage) :
    ∀ action ∈ attempt (law scope) current stages, EnergyAction action := by
  induction stages generalizing current with
  | nil => simp [attempt]
  | cons stage rest ih =>
    simp only [attempt]
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | member
      · exact (stable _ (by simp)).2 current
      · exact ih _ (fun stage inside => stable stage (by simp [inside])) _ member
    · intro action member
      cases List.mem_singleton.mp member
      exact (stable _ (by simp)).2 current

theorem Twin.attempt {left right : AuditCurrent} (same : Twin left right)
    (scope : Scope) (cost : scope.revisionCost = [(.energy,1)]) (stages : List (AuditCurrent → Action))
    (stable : ∀ stage ∈ stages, StableStage stage) :
    attempt (law scope) left stages = attempt (law scope) right stages := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage rest ih =>
    have head := stable stage (by simp)
    have action := head.1 left right same
    have visible := energy_public scope cost left (stage left) (head.2 left)
    simp only [EnergyRenewal.attempt,← action,propext (same.valid scope (stage left) visible)]
    split
    · congr 1
      exact ih (same.step scope (stage left) visible) (fun stage inside => stable stage (by simp [inside]))
    · rfl

theorem stable_access (actor : Party) (query : Query) : StableStage (fun _ => accessRequest actor query) :=
  ⟨fun _ _ _ => rfl,fun _ => by simp [EnergyAction,accessRequest]⟩
theorem stable_fee : StableStage (fun _ => deliveryFee) :=
  ⟨fun _ _ _ => rfl,fun _ => by simp [EnergyAction,deliveryFee]⟩
theorem stable_application : StableStage (fun _ => applicationFee) :=
  ⟨fun _ _ _ => rfl,fun _ => by simp [EnergyAction,applicationFee]⟩
theorem stable_transfer (actor : Party) (quantity : ℚ) : StableStage (fun _ => transfer actor quantity) :=
  ⟨fun _ _ _ => rfl,fun _ => by simp [EnergyAction,transfer]⟩
theorem stable_command (scope : Scope) (actor : Party) (command : Mandate.Command Party) :
    StableStage (fun current => Mandate.request scope current actor command) :=
  ⟨fun _ _ same => same.command scope actor command,fun _ => True.intro⟩
theorem stable_topUp (actor : Party) (quantity : ℚ) : StableStage (Handoff.topUp actor quantity) := by
  refine ⟨?_,?_⟩
  · intro left right same
    simp only [Handoff.topUp,same.stock actor .energy (by decide)]
  · intro current
    simp [EnergyAction,Handoff.topUp,transfer]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy

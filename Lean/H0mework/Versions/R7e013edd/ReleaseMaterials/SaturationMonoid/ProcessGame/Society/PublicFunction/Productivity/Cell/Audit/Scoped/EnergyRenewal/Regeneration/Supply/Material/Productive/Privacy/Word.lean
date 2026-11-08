import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Protocol.SymbolicAuthentication
abbrev Twin := Supply.Privacy.Twin

def Safe (action : JointAction) : Prop :=
  Supply.Privacy.Safe action ∨ action.operation=transport.operation ∧ action.purpose=.exchange

theorem policy_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (action : JointAction) (safe : Safe action) :
    (law scope).operationAllowed left action=(law scope).operationAllowed right action := by
  have old : (Supply.law scope).operationAllowed left action=(Supply.law scope).operationAllowed right action := by
    rcases safe with old | extra
    · exact same.policy scope cost action old
    · simp [RawLaw.operationAllowed,Supply.law,RawPolicy.eval,extra.2,exchangeAllowed,same.claims]
  change ((Supply.law scope).operationAllowed left action || decide (action=transport ∧ 0<left.claims .delivery supplier receiver)) =
    ((Supply.law scope).operationAllowed right action || decide (action=transport ∧ 0<right.claims .delivery supplier receiver))
  rw [old,same.claims]

theorem safe_flows (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (current : Current) (action : JointAction) (safe : Safe action) :
    (∀ item∈(law scope).debit current action,item.1≠(receiver,Good.feed)) ∧
    (∀ item∈(law scope).credit current action,item.1≠(receiver,Good.feed)) := by
  rcases safe with old | extra
  · exact Supply.Privacy.safe_flows scope cost current action old
  · simp [RawLaw.debit,RawLaw.credit,extra.1,transport,locate,customer,factory,receiver]

theorem valid_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (action : JointAction) (safe : Safe action) :
    (law scope).Valid left action ↔ (law scope).Valid right action := by
  have debit : (law scope).debit left action=(law scope).debit right action := same.debit scope action
  have credit : (law scope).credit left action=(law scope).credit right action := same.credit scope action
  have ports : (law scope).requiredPorts left action=(law scope).requiredPorts right action := by
    simp only [RawLaw.requiredPorts,debit,same.technology]
  have funded : (∀ item∈(law scope).debit left action,
      flowAt ((law scope).debit left action) item.1.1 item.1.2≤left.stock item.1.1 item.1.2) ↔
      (∀ item∈(law scope).debit right action,
      flowAt ((law scope).debit right action) item.1.1 item.1.2≤right.stock item.1.1 item.1.2) := by
    rw [←debit]
    constructor <;> intro paid item member
    · rw [←same.stock _ _ ((safe_flows scope cost left action safe).1 item member)]
      exact paid item member
    · rw [same.stock _ _ ((safe_flows scope cost left action safe).1 item member)]
      exact paid item member
  have guard : (law scope).ClaimGuard left action ↔ (law scope).ClaimGuard right action := same.guard scope action
  unfold RawLaw.Valid
  rw [funded]
  simp only [policy_public same scope cost action safe,ports,same.technology,guard,debit,credit]

theorem step_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (action : JointAction) (safe : Safe action) :
    Twin ((law scope).step left action) ((law scope).step right action) := by
  simp only [RawLaw.step,propext (valid_public same scope cost action safe)]
  split
  · exact same.paidStep scope action
  · exact same

theorem execute_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) (index : Nat) :
    Twin ((law scope).execute left index actions).final ((law scope).execute right index actions).final := by
  induction actions generalizing left right index with
  | nil => exact same
  | cons action rest ih =>
    exact ih (step_public same scope cost action (safe action (by simp)))
      (fun action inside => safe action (List.mem_cons_of_mem _ inside)) (index+1)

theorem next_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) :
    Twin ((law scope).next left actions) ((law scope).next right actions) := by
  have done := execute_public same scope cost actions safe 0
  exact ⟨done.technology,congrArg (·+1) same.clock,congrArg Nat.succ same.round,done.claims,done.stock⟩

def Stable (stage : Current → JointAction) : Prop :=
  (∀ left right,Twin left right → stage left=stage right) ∧ ∀ current,Safe (stage current)

theorem stages_stable (current : Current) (mode : Mode) : ∀ stage∈stages current mode,Stable stage := by
  unfold stages
  dsimp only
  repeat' split
  all_goals simp [Stable,Safe,Supply.Privacy.Safe,Supply.Privacy.Energy,Supply.Privacy.ProviderOnly,
    transport,feed,obligation,production,shipment,liftProvider,liftProviderOperation,
    RenewedQuorumMaterial.give,RecycledQuorumMaterial.production,Refeed.fund,Refeed.collect,
    Refeed.recycle,Refeed.transport,WorkerInputLaw.energyLabor,WorkerInputLaw.waste,
    RecycledQuorumMaterial.recycle,RecycledQuorumMaterial.waste,UpstreamFeedLaw.request,FuelMandateLaw.give]
  all_goals intro left right same;exact congrFun (congrFun (congrFun same.claims .delivery) supplier) receiver

theorem stages_public {left right : Current} (same : Twin left right) (mode : Mode) :
    stages left mode=stages right mode := by
  have supplierFeed := same.stock supplier .feed (by decide)
  have supplierEnergy := same.stock supplier .energy (by decide)
  have factoryFeed := same.stock factory .feed (by decide)
  have factoryEnergy := same.stock factory .energy (by decide)
  have factoryLabor := same.stock factory .labor (by decide)
  have donorEnergy := same.stock Refeed.donor .energy (by decide)
  have donorLabor := same.stock Refeed.donor .labor (by decide)
  simp only [stages,same.claims,supplierFeed,supplierEnergy,factoryFeed,factoryEnergy,factoryLabor,donorEnergy,donorLabor]

theorem attempt_safe (scope : Scope) (current : Current) (stages : List (Current → JointAction))
    (stable : ∀ stage∈stages,Stable stage) : ∀ action∈attempt scope current stages,Safe action := by
  induction stages generalizing current with
  | nil => simp [attempt]
  | cons stage rest ih =>
    simp only [attempt]
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | tail
      · exact (stable stage (by simp)).2 _
      · exact ih _ (fun stage member => stable stage (List.mem_cons_of_mem _ member)) _ tail
    · intro action member
      cases List.mem_singleton.mp member
      exact (stable stage (by simp)).2 _

theorem attempt_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (stages : List (Current → JointAction))
    (stable : ∀ stage∈stages,Stable stage) : attempt scope left stages=attempt scope right stages := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage rest ih =>
    have head := stable stage (by simp)
    have equal := head.1 left right same
    have safe := head.2 left
    simp only [attempt,←equal,propext (valid_public same scope cost (stage left) safe),memo_exact]
    split
    · congr 1
      exact ih (step_public same scope cost _ safe) (fun stage member => stable stage (List.mem_cons_of_mem _ member))
    · rfl

theorem word_safe (scope : Scope) (mode : Mode) (current : Current) :
    ∀ action∈word scope mode current,Safe action := attempt_safe scope current _ (stages_stable current mode)

theorem word_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (mode : Mode) : word scope mode left=word scope mode right := by
  unfold word
  rw [←stages_public same mode]
  exact attempt_public same scope cost _ (stages_stable left mode)

theorem related_actual_successors {lp rp : Plan} (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (mode : Mode) :
    Supply.Privacy.Source.SessionTwin (next left mode).session (next right mode).session := by
  refine ⟨?_,same.scope,same.target,by simpa [next] using same.history⟩
  change Twin (Runtime.current left mode) (Runtime.current right mode)
  rw [Runtime.current_is_own_root_next,Runtime.current_is_own_root_next]
  change Twin ((law left.session.window.scope).next ((law left.session.window.scope).next left.session.current [])
      (word left.session.window.scope mode ((law left.session.window.scope).next left.session.current [])))
    ((law right.session.window.scope).next ((law right.session.window.scope).next right.session.current [])
      (word right.session.window.scope mode ((law right.session.window.scope).next right.session.current [])))
  rw [←same.scope]
  have prepared := next_public same.current left.session.window.scope rfl [] (by simp)
  rw [←word_public prepared left.session.window.scope rfl mode]
  exact next_public prepared _ rfl _ (word_safe _ _ _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive

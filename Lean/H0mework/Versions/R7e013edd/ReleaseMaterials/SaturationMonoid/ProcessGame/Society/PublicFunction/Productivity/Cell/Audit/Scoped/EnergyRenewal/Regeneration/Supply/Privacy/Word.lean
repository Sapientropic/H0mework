import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
namespace Old
export EnergyRenewal.Privacy (Twin EnergyAction energy_public)
end Old
abbrev Scope := Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)

/-- Only this original receiver coordinate is private. Source fuel remains public. -/
structure Twin (left right : Current) : Prop where
  technology : left.technology=right.technology
  clock : left.clock=right.clock
  round : left.round=right.round
  claims : left.claims=right.claims
  stock : ∀ actor good,(actor,good)≠(receiver,Good.feed) → left.stock actor good=right.stock actor good

theorem Twin.refl (current : Current) : Twin current current := ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩

theorem Twin.audit {left right : Current} (same : Twin left right) : Old.Twin (audit left) (audit right) := by
  refine ⟨congrArg Technology.audit same.technology,same.clock,same.round,?_,?_⟩
  · unfold Supply.audit;rw [same.claims]
  · intro actor good visible
    exact same.stock _ _ (fun equal => visible (congrArg Prod.snd equal))

theorem Twin.provider {left right : Current} (same : Twin left right) : provider left=provider right := by
  apply RawCurrent.ext
  · funext actor good
    exact same.stock _ _ (by simp [receiver])
  · unfold Supply.provider;rw [same.claims]
  · exact congrArg Technology.provider same.technology
  · simp only [Supply.provider,same.clock,same.technology]
  · simp only [Supply.provider,same.round,same.technology]

theorem Twin.debit {left right : Current} (same : Twin left right) (scope : Scope) (action : JointAction) :
    (law scope).debit left action=(law scope).debit right action := by
  cases action.operation <;> simp only [RawLaw.debit,same.technology]
theorem Twin.credit {left right : Current} (same : Twin left right) (scope : Scope) (action : JointAction) :
    (law scope).credit left action=(law scope).credit right action := by
  cases action.operation <;> simp only [RawLaw.credit,same.technology]

theorem Twin.decode {left right : Current} (same : Twin left right) (action : JointAction) :
    auditAction left action=auditAction right action ∧ providerAction left action=providerAction right action := by
  simp [auditAction,providerAction,auditOperation,providerOperation,same.technology]

def Energy (action : JointAction) : Prop := match action.operation with
  | .transfer _ _ goods | .use _ goods .external => ∀ entry∈goods,entry.1=Good.energy
  | .revise _ _ => True
  | _ => False

/-- This is the actual producer vocabulary, including malformed signers used for accurate refusals. -/
def ProviderOnly (action : JointAction) : Prop := match action.operation with
  | .produce (.inr _) | .transfer (.inr _) (.inr _) _ => True
  | _ => False

def Safe (action : JointAction) : Prop :=
  Energy action ∨ action.operation=feed.operation ∨ action.operation=obligation.operation ∨
    (∃ q,action.operation=(shipment q).operation) ∨ action.operation=.produce supplier ∨ ProviderOnly action

theorem audit_decoded_energy (current : Current) (action : JointAction) (safe : Safe action)
    (original : Action) (decoded : auditAction current action=some original) : Old.EnergyAction original := by
  simp only [auditAction,bind,Option.bind_eq_some_iff] at decoded
  obtain ⟨signer,_,consents,_,purpose,_,gates,_,operation,decoded,originalEqual⟩ := decoded
  rw [←Option.some.inj originalEqual]
  dsimp only [Old.EnergyAction]
  rcases safe with energy | fuel | issue | ⟨quantity,settle⟩ | produce | provider
  · cases op : action.operation <;> simp only [Energy,op] at energy
    case transfer p q goods =>
      cases p <;> cases q <;> simp [auditOperation,auditParty,op] at decoded
      all_goals cases decoded;exact energy
    case use p goods kind =>
      cases kind <;> try contradiction
      cases p <;> simp [auditOperation,auditParty,op] at decoded
      all_goals cases decoded;exact energy
    case revise p target =>
      cases p <;> simp [auditOperation,auditParty,op] at decoded
      all_goals rw [←decoded.2];trivial
  · simp only [fuel,feed,auditOperation,auditParty,supplier,customer,Option.bind_none] at decoded
    contradiction
  · simp [issue,obligation,auditOperation] at decoded
  · simp [settle,shipment,auditOperation] at decoded
  · simp [produce,auditOperation,auditParty,supplier] at decoded
  · cases op : action.operation <;> simp only [ProviderOnly,op] at provider
    case produce p => cases p <;> simp_all [auditOperation,auditParty]
    case transfer p q goods => cases p <;> cases q <;> simp_all [auditOperation,auditParty]

theorem Twin.policy {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (action : JointAction) (safe : Safe action) :
    (law scope).operationAllowed left action=(law scope).operationAllowed right action := by
  have decodes := same.decode action
  simp only [RawLaw.operationAllowed,law,RawPolicy.eval]
  cases purpose : action.purpose with
  | audit port =>
    change (auditAction left action).any _=(auditAction right action).any _
    rw [←decodes.1]
    cases decoded : auditAction left action with
    | none => rfl
    | some original =>
      have valid := same.audit.valid scope original (Old.energy_public scope cost (Supply.audit left) original
        (audit_decoded_energy left action safe original decoded))
      change decide ((EnergyRenewal.Privacy.law scope).Valid (Supply.audit left) original)=_
      simp only [Option.any]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact valid
  | provider port =>
    change (providerAction left action).any _=(providerAction right action).any _
    rw [decodes.2,same.provider]
  | exchange =>
    change exchangeAllowed left action=exchangeAllowed right action
    simp only [exchangeAllowed,same.claims]

theorem safe_flows (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (current : Current) (action : JointAction) (safe : Safe action) :
    (∀ item∈(law scope).debit current action,item.1≠(receiver,Good.feed)) ∧
    (∀ item∈(law scope).credit current action,item.1≠(receiver,Good.feed)) := by
  rcases safe with energy | fuel | issue | ⟨quantity,settle⟩ | produce | provider
  · cases op : action.operation <;> simp only [Energy,op] at energy
    case transfer p q goods =>
      constructor <;> intro item inside
      all_goals simp only [RawLaw.debit,RawLaw.credit,op,locate,List.mem_map] at inside
      all_goals obtain ⟨entry,member,rfl⟩ := inside
      all_goals simp [energy entry member]
    case use p goods kind =>
      cases kind <;> try contradiction
      constructor
      · intro item inside
        simp only [RawLaw.debit,op,locate,List.mem_map] at inside
        obtain ⟨entry,member,rfl⟩ := inside
        simp [energy entry member]
      · simp [RawLaw.credit,op]
    case revise p target =>
      constructor
      · intro item inside
        simp only [RawLaw.debit,op,law] at inside
        split at inside
        · simp [providerLaw,Protocol.SymbolicAuthentication.WorkerInputLaw.law,
            Protocol.SymbolicAuthentication.FuelMandateLaw.law,Mandate.law,
            Repayment.Recovery.scope,material,locate] at inside
          subst item;simp
        · simp [cost,locate] at inside
          subst item;simp
      · simp [RawLaw.credit,op]
  · simp [RawLaw.debit,RawLaw.credit,fuel,feed,locate,customer,supplier,receiver]
  · simp [RawLaw.debit,RawLaw.credit,issue,obligation]
  · simp [RawLaw.debit,RawLaw.credit,settle,shipment,law,locate,supplier,receiver]
  · simp [RawLaw.debit,RawLaw.credit,produce,locate,supplier,receiver]
  · cases op : action.operation <;> simp only [ProviderOnly,op] at provider
    case produce p =>
      cases p <;> simp_all [RawLaw.debit,RawLaw.credit,locate,receiver]
    case transfer p q goods =>
      cases p <;> cases q <;> simp_all [RawLaw.debit,RawLaw.credit,locate,receiver]

theorem Twin.guard {left right : Current} (same : Twin left right) (scope : Scope) (action : JointAction) :
    (law scope).ClaimGuard left action ↔ (law scope).ClaimGuard right action := by
  cases op : action.operation with
  | use actor goods kind =>
    cases actor <;> cases kind <;> simp [RawLaw.ClaimGuard,op,law,Mandate.law,energyBase,baseLaw,
      Cell.law,Mandate.eraseCurrent,providerLaw,Protocol.SymbolicAuthentication.WorkerInputLaw.law,
      Protocol.SymbolicAuthentication.FuelMandateLaw.law,Protocol.SymbolicAuthentication.FuelMandateLaw.base,
      Protocol.SymbolicAuthentication.RenewedQuorumMaterial.base,Repayment.Recovery.base]
  | _ => simp [RawLaw.ClaimGuard,op,same.claims]

theorem Twin.valid {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (action : JointAction) (safe : Safe action) :
    (law scope).Valid left action ↔ (law scope).Valid right action := by
  have debit := same.debit scope action
  have credit := same.credit scope action
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
  unfold RawLaw.Valid
  rw [funded]
  simp only [same.policy scope cost action safe,ports,same.technology,same.guard scope action,debit,credit]

theorem Twin.paidStep {left right : Current} (same : Twin left right) (scope : Scope) (action : JointAction) :
    Twin ((law scope).paidStep left action) ((law scope).paidStep right action) := by
  refine ⟨?_,same.clock,same.round,?_,?_⟩
  · cases action.operation <;> simp only [RawLaw.paidStep,same.technology]
  · cases action.operation <;> simp only [RawLaw.paidStep,RawLaw.nextClaims,same.claims]
  · intro actor good visible
    simp only [RawLaw.paidStep,same.stock actor good visible,same.debit scope action,same.credit scope action]

theorem Twin.step {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (action : JointAction) (safe : Safe action) :
    Twin ((law scope).step left action) ((law scope).step right action) := by
  simp only [RawLaw.step,propext (same.valid scope cost action safe)]
  split
  · exact same.paidStep scope action
  · exact same

theorem Twin.execute {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) (index : Nat) :
    Twin ((law scope).execute left index actions).final ((law scope).execute right index actions).final := by
  induction actions generalizing left right index with
  | nil => exact same
  | cons action rest ih =>
    exact ih (same.step scope cost action (safe action (by simp)))
      (fun action inside => safe action (List.mem_cons_of_mem _ inside)) (index+1)

theorem Twin.next {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) :
    Twin ((law scope).next left actions) ((law scope).next right actions) := by
  have done := same.execute scope cost actions safe 0
  exact ⟨done.technology,congrArg (·+1) same.clock,congrArg Nat.succ same.round,done.claims,done.stock⟩

def Stable (stage : Current → JointAction) : Prop :=
  (∀ left right,Twin left right → stage left=stage right) ∧ ∀ current,Safe (stage current)

theorem lift_energy (current : Current) (action : Action) (energy : Old.EnergyAction action) : Safe (liftAudit current action) := by
  apply Or.inl
  cases op : action.operation <;> simp only [Energy,Old.EnergyAction,liftAudit,liftAuditOperation,op] at *
  all_goals try trivial
  case use p goods kind => cases kind <;> simp_all; exact energy

theorem lift_stable (stage : AuditCurrent → Action) (stable : EnergyRenewal.Privacy.StableStage stage) :
    Stable (fun current => liftAudit current (stage (audit current))) := by
  refine ⟨?_,fun current => lift_energy current _ (stable.2 _)⟩
  intro left right same
  simp only [stable.1 _ _ same.audit,liftAudit,liftAuditOperation,same.technology]

theorem attempt_safe (scope : Scope) (before : Current) (stages : List (Current → JointAction))
    (stable : ∀ stage∈stages,Stable stage) : ∀ action∈Supply.attempt scope before stages,Safe action := by
  induction stages generalizing before with
  | nil => simp [Supply.attempt]
  | cons stage rest ih =>
    simp only [Supply.attempt]
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | tail
      · exact (stable stage (by simp)).2 _
      · exact ih _ (fun stage member => stable stage (List.mem_cons_of_mem _ member)) _ tail
    · intro action member
      cases List.mem_singleton.mp member
      exact (stable stage (by simp)).2 _

theorem Twin.attempt {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (stages : List (Current → JointAction))
    (stable : ∀ stage∈stages,Stable stage) : Supply.attempt scope left stages=Supply.attempt scope right stages := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage rest ih =>
    have head := stable stage (by simp)
    have equal := head.1 left right same
    have safe := head.2 left
    simp only [Supply.attempt,←equal,propext (same.valid scope cost (stage left) safe),memo_exact]
    split
    · congr 1
      exact ih (same.step scope cost _ safe) (fun stage member => stable stage (List.mem_cons_of_mem _ member))
    · rfl

theorem Twin.allPaid {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) : Supply.allPaid scope left actions=Supply.allPaid scope right actions := by
  unfold Supply.allPaid
  simp only [cachedItems_exact,RawLaw.rawItems]
  have go : ∀ (actions : List JointAction) (left right : Current) (index : Nat),Twin left right →
      (∀ action∈actions,Safe action) →
      (((law scope).execute left index actions).items.all fun item => decide ((law scope).Valid item.before item.request))=
      (((law scope).execute right index actions).items.all fun item => decide ((law scope).Valid item.before item.request)) := by
    intro actions
    induction actions with
    | nil => intros;rfl
    | cons action rest ih =>
      intro left right index same safe
      simp only [RawLaw.execute,List.all_cons]
      have valid := same.valid scope cost action (safe action (by simp))
      have head : decide ((law scope).Valid left action)=decide ((law scope).Valid right action) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using valid
      rw [head,ih _ _ (index+1) (same.step scope cost action (safe action (by simp)))
        (fun action inside => safe action (List.mem_cons_of_mem _ inside))]
  exact go actions left right 0 same safe

theorem refeed_stable (before : Current) (deny : Bool) : ∀ stage∈Refeed.stages before deny,Stable stage := by
  unfold Refeed.stages
  dsimp only
  repeat' split
  all_goals simp [Stable,Safe,Energy,ProviderOnly,feed,production,liftProvider,liftProviderOperation,
    Refeed.fund,Refeed.collect,Refeed.recycle,Refeed.transport,
    Protocol.SymbolicAuthentication.WorkerInputLaw.energyLabor,Protocol.SymbolicAuthentication.WorkerInputLaw.waste,
    Protocol.SymbolicAuthentication.RenewedQuorumMaterial.give,
    Protocol.SymbolicAuthentication.RecycledQuorumMaterial.waste,
    Protocol.SymbolicAuthentication.RecycledQuorumMaterial.recycle,
    Protocol.SymbolicAuthentication.UpstreamFeedLaw.request,Protocol.SymbolicAuthentication.FuelMandateLaw.give]

theorem Twin.refeedStages {left right : Current} (same : Twin left right) (deny : Bool) :
    Refeed.stages left deny=Refeed.stages right deny := by
  simp only [Refeed.stages,
    same.stock Refeed.donor .feed (by simp [Refeed.donor,receiver]),
    same.stock Refeed.donor .energy (by simp [Refeed.donor,receiver]),
    same.stock Refeed.donor .labor (by simp [Refeed.donor,receiver]),
    same.stock Refeed.donor .waste (by simp [Refeed.donor,receiver]),
    same.stock supplier .energy (by simp [supplier,receiver]),
    same.stock supplier .feed (by simp [supplier,receiver])]

theorem dispatch_stable (before : Current) (mode : Mode) : ∀ stage∈Supply.dispatch before mode,Stable stage := by
  unfold Supply.dispatch
  dsimp only
  split
  · intro stage member
    rcases List.mem_append.mp member with original | rest
    · exact refeed_stable _ _ stage original
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at rest
      rcases rest with rfl | rfl
      all_goals simp [Stable,Safe,Energy,shipment,production,liftProvider,liftProviderOperation]
  · repeat' split
    all_goals simp [Stable,Safe,Energy,feed,shipment,production,liftProvider,liftProviderOperation]

theorem Twin.dispatch {left right : Current} (same : Twin left right) (mode : Mode) :
    Supply.dispatch left mode=Supply.dispatch right mode := by
  simp only [Supply.dispatch,same.claims,same.stock supplier .energy (by simp [supplier,receiver]),
    same.stock supplier .feed (by simp [supplier,receiver]),same.refeedStages]

theorem lot_safe (scope : Scope) (before : Current) (mode : Mode) : ∀ action∈Supply.lot scope before mode,Safe action := by
  unfold Supply.lot
  split
  all_goals dsimp only
  all_goals split
  all_goals try (simp [Safe,obligation])
  all_goals intro action member
  all_goals exact attempt_safe scope _ _ (dispatch_stable _ mode) action member

theorem Twin.lot {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (mode : Mode) : Supply.lot scope left mode=Supply.lot scope right mode := by
  unfold Supply.lot
  rw [←same.claims]
  let first : List JointAction := if left.claims .delivery supplier receiver=0 then [obligation] else []
  have safe : ∀ action∈first,Safe action := by
    unfold first
    split <;> simp [Safe]
  have after := same.execute scope cost first safe 0
  simp only [cachedExecute_exact]
  change (if Supply.allPaid scope left first then first++Supply.attempt scope ((law scope).execute left 0 first).final
    (Supply.dispatch ((law scope).execute left 0 first).final mode) else first)=_
  rw [same.allPaid scope cost first safe]
  split
  · rw [after.dispatch mode]
    rw [after.attempt scope cost _ (dispatch_stable _ mode)]
  · rfl

theorem fill_safe (scope : Scope) (required : ℚ) (mode : Mode) (count : Nat) (before : Current) :
    ∀ action∈Supply.fill scope required mode count before,Safe action := by
  induction count generalizing before with
  | zero => simp [Supply.fill]
  | succ n ih =>
    simp only [Supply.fill]
    split
    · simp
    · split
      · intro action member
        rcases List.mem_append.mp member with front | back
        · exact lot_safe _ _ _ action front
        · exact ih _ action back
      · exact lot_safe _ _ _

theorem Twin.fill {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (required : ℚ) (mode : Mode) (count : Nat) :
    Supply.fill scope required mode count left=Supply.fill scope required mode count right := by
  induction count generalizing left right with
  | zero => rfl
  | succ n ih =>
    simp only [Supply.fill,←same.claims,←same.stock receiver .energy (by simp)]
    split
    · rfl
    · rw [←same.lot scope cost mode,←same.allPaid scope cost _ (lot_safe _ _ _)]
      split
      · congr 1
        rw [cachedExecute_exact,cachedExecute_exact]
        exact ih (same.execute scope cost _ (lot_safe _ _ _) 0)
      · rfl

theorem stable_topup (actor : Party) (required : ℚ) : Stable (topup actor required) := by
  refine ⟨?_,?_⟩
  · intro left right same
    simp only [topup,same.stock (.inl actor) .energy (by simp),liftAudit,liftAuditOperation,same.technology]
  · intro current
    apply lift_energy
    simp [Old.EnergyAction,transfer]

theorem stable_command (scope : Scope) (actor : Party) (command : Mandate.Command Party) :
    Stable (fun state => liftAudit state (Mandate.request scope (audit state) actor command)) :=
  lift_stable _ (EnergyRenewal.Privacy.stable_command _ _ _)
theorem stable_access (actor : Party) (query : Query) :
    Stable (fun state => liftAudit state (accessRequest actor query)) :=
  lift_stable _ (EnergyRenewal.Privacy.stable_access _ _)
theorem stable_fee : Stable (fun state => liftAudit state deliveryFee) :=
  lift_stable _ EnergyRenewal.Privacy.stable_fee
theorem stable_application : Stable (fun state => liftAudit state applicationFee) :=
  lift_stable _ EnergyRenewal.Privacy.stable_application

theorem renewal_stable (scope : Scope) (target : Party) : ∀ stage∈
    [topup 0 (requiredOwner scope),topup target (requiredCandidate scope),
     fun state => liftAudit state (Mandate.request scope (audit state) 0 .revoke),
     fun state => liftAudit state applicationFee],Stable stage := by
  intro stage member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact stable_topup _ _
  · exact stable_topup _ _
  · exact stable_command _ _ _
  · exact stable_application

theorem renewal_safe (scope : Scope) (current : Current) (mode : Mode) :
    ∀ action∈Supply.renewal scope current mode,Safe action := by
  unfold renewal
  dsimp only
  split
  · intro action member
    rcases List.mem_append.mp member with first | second
    · exact fill_safe _ _ _ _ _ action first
    · exact attempt_safe scope _ _ (renewal_stable _ _) action second
  · exact fill_safe _ _ _ _ _

theorem Twin.replacement {left right : Current} (same : Twin left right) (scope : Scope) :
    Supply.replacement scope left=Supply.replacement scope right := by
  simp only [Supply.replacement,members,same.technology]

theorem Twin.renewal {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (mode : Mode) : Supply.renewal scope left mode=Supply.renewal scope right mode := by
  have owner := same.stock customer .energy (by simp)
  have candidate := same.stock (.inl (Supply.replacement scope left)) .energy (by simp)
  unfold Supply.renewal
  rw [←same.replacement scope]
  dsimp only
  rw [←owner,←candidate]
  rw [←same.fill scope cost,←same.allPaid scope cost _ (fill_safe _ _ _ _ _)]
  split
  · congr 1
    rw [cachedExecute_exact,cachedExecute_exact]
    exact (same.execute scope cost _ (fill_safe _ _ _ _ _) 0).attempt scope cost _ (renewal_stable _ _)
  · rfl

theorem serve_stable (scope : Scope) (target : Party) (query : Query) (current : Current) :
    ∀ stage∈((if current.technology.audit.offered=some target then [] else
      [fun state => liftAudit state (Mandate.request scope (audit state) 0 (.propose target))]) ++
     [fun state => liftAudit state (Mandate.request scope (audit state) target .accept),
      fun state => liftAudit state (accessRequest target query),fun state => liftAudit state deliveryFee]),Stable stage := by
  intro stage member
  split at member
  · simp only [List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact stable_command _ _ _
    · exact stable_access _ _
    · exact stable_fee
  · simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact stable_command _ _ _
    · exact stable_command _ _ _
    · exact stable_access _ _
    · exact stable_fee

theorem serve_safe (scope : Scope) (target : Party) (query : Query) (current : Current) :
    ∀ action∈Supply.serve scope target query current,Safe action :=
  attempt_safe scope _ _ (serve_stable _ _ _ _)

theorem Twin.serve {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (target : Party) (query : Query) :
    Supply.serve scope target query left=Supply.serve scope target query right := by
  unfold Supply.serve
  rw [←same.technology]
  exact same.attempt scope cost _ (serve_stable _ _ _ _)

theorem read_stable (actor : Party) (query : Query) : ∀ stage∈
    [fun state => liftAudit state (accessRequest actor query),fun state => liftAudit state deliveryFee],Stable stage := by
  intro stage member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact stable_access _ _
  · exact stable_fee

theorem Twin.word {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (target : Party) (query : Query) (mode : Mode) :
    Supply.word scope target query mode left=Supply.word scope target query mode right := by
  unfold Supply.word
  rw [←same.clock,←same.technology]
  split
  · exact same.renewal scope cost mode
  · split
    · exact same.serve scope cost target query
    · exact same.attempt scope cost _ (read_stable _ _)

theorem word_safe (scope : Scope) (target : Party) (query : Query) (mode : Mode) (current : Current) :
    ∀ action∈Supply.word scope target query mode current,Safe action := by
  unfold Supply.word
  split
  · exact renewal_safe _ _ _
  · split
    · exact serve_safe _ _ _ _
    · exact attempt_safe scope _ _ (read_stable _ _)

/-- It includes both accepted and rejected requests; neither branch borrows the other's next. -/
theorem source_word_generates_related_own_next {left right : Current} (same : Twin left right)
    (scope : Scope) (cost : scope.revisionCost=[(.energy,1)]) (target : Party) (query : Query) (mode : Mode) :
    Supply.word scope target query mode left=Supply.word scope target query mode right ∧
    Twin ((law scope).next left (Supply.word scope target query mode left))
      ((law scope).next right (Supply.word scope target query mode right)) := by
  refine ⟨same.word scope cost target query mode,?_⟩
  rw [←same.word scope cost target query mode]
  exact same.next scope cost _ (word_safe _ _ _ _ _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy

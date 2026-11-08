import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Privacy.Word

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Protocol.SymbolicAuthentication
def publicItems (scope : Scope) (before : Current) (actions : List JointAction) (index : Nat) : List Supply.Privacy.PublicItem :=
  (execute scope before index actions).items.map fun item =>
    ⟨item.index,Supply.Privacy.publicize item.before,item.request,decide ((law scope).Valid item.before item.request),
      (law scope).actualDebit item.before item.request,(law scope).actualCredit item.before item.request,
      Supply.Privacy.publicize ((law scope).step item.before item.request)⟩

theorem publicItems_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) (index : Nat) :
    publicItems scope left actions index=publicItems scope right actions index := by
  induction actions generalizing left right index with
  | nil => simp [publicItems,execute]
  | cons action rest ih =>
    have front := safe action (by simp)
    have valid := valid_public same scope cost action front
    have paid : decide ((law scope).Valid left action)=decide ((law scope).Valid right action) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using valid
    have debit : (law scope).actualDebit left action=(law scope).actualDebit right action := by
      simp only [RawLaw.actualDebit,propext valid]
      split
      · exact same.debit scope action
      · rfl
    have credit : (law scope).actualCredit left action=(law scope).actualCredit right action := by
      simp only [RawLaw.actualCredit,propext valid]
      split
      · exact same.credit scope action
      · rfl
    simp only [publicItems,execute,memo_exact,List.map_cons]
    change Supply.Privacy.PublicItem.mk _ (Supply.Privacy.publicize left) action _ _ _ _ :: publicItems scope ((law scope).step left action) rest (index+1)=
      Supply.Privacy.PublicItem.mk _ (Supply.Privacy.publicize right) action _ _ _ _ :: publicItems scope ((law scope).step right action) rest (index+1)
    rw [same.publicize,paid,debit,credit,(step_public same scope cost action front).publicize,
      ih (step_public same scope cost action front) (fun action member => safe action (List.mem_cons_of_mem _ member)) (index+1)]

structure Observation where
  before : Current
  actions : List Supply.Privacy.PublicItem
  next : Current

def observe (scope : Scope) (mode : Mode) (current : Current) : Observation :=
  let before := (law scope).next current []
  let actions := word scope mode before
  ⟨Supply.Privacy.publicize before,publicItems scope before actions 0,
    Supply.Privacy.publicize ((law scope).next before actions)⟩

theorem observe_public {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (mode : Mode) : observe scope mode left=observe scope mode right := by
  have prepared := next_public same scope cost [] (by simp)
  dsimp only [observe]
  rw [←word_public prepared scope cost mode,prepared.publicize,
    publicItems_public prepared scope cost _ (word_safe _ _ _) 0,
    (next_public prepared scope cost _ (word_safe _ _ _)).publicize]

theorem observation_uses_own_generated_next {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    (observe state.session.window.scope mode state.session.current).next=
      Supply.Privacy.publicize (next state mode).session.current := by
  change _=Supply.Privacy.publicize (Runtime.current state mode)
  rw [Runtime.current_is_own_root_next]
  rfl

structure Command where
  request : Except String (Mode ⊕ (Query×Supply.Mode))
  metadata : Lean.Json
abbrev Reply := (Nat×Observation) ⊕ Supply.Privacy.Reply
abbrev Render := Command → Except String Reply → Lean.Json
abbrev Strategy := List Lean.Json → Nat → Command

def advance {plan : Plan} (state : Finance.State plan) (command : Command) : Finance.State plan :=
  match command.request with
  | .error _ => state
  | .ok (.inl mode) => next state mode
  | .ok (.inr (query,mode)) => state.next query mode

def answer {plan : Plan} (state : Finance.State plan) (command : Command) : Except String Reply :=
  command.request.map fun request => match request with
  | .inl mode => .inl (state.session.history.length+1,observe state.session.window.scope mode state.session.current)
  | .inr (query,mode) => .inr (Supply.Privacy.reply state query mode)

theorem advance_public {lp rp : Plan} (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (command : Command) :
    Supply.Privacy.Source.SessionTwin (advance left command).session (advance right command).session := by
  cases requested : command.request with
  | error _ => simpa only [advance,requested] using same
  | ok request =>
    cases request with
    | inl mode => simpa only [advance,requested] using related_actual_successors left right same mode
    | inr request => simpa only [advance,requested,Finance.State.next] using same.next request.1 request.2

theorem answer_public {lp rp : Plan} (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (command : Command) :
    answer left command=answer right command := by
  unfold answer
  cases requested : command.request with
  | error _ => rfl
  | ok request =>
    cases request with
    | inl mode =>
      change Except.ok (Sum.inl (_,_))=Except.ok (Sum.inl (_,_))
      rw [←same.scope,same.history,observe_public same.current left.session.window.scope rfl mode]
    | inr request =>
      change Except.ok (Sum.inr (Supply.Privacy.reply left request.1 request.2))=Except.ok (Sum.inr _)
      rw [same.reply request.1 request.2]

def play {plan : Plan} (initial : Finance.State plan) (render : Render) (strategy : Strategy) :
    Nat → Finance.State plan × List Lean.Json
  | 0 => (initial,[])
  | n+1 =>
    let (state,past) := play initial render strategy n
    let command := strategy past n
    (advance state command,past++[render command (answer state command)])

theorem cumulative_related_own_states_and_complete_output {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session)
    (render : Render) (strategy : Strategy) (count : Nat) :
    Supply.Privacy.Source.SessionTwin (play left render strategy count).1.session (play right render strategy count).1.session ∧
      (play left render strategy count).2=(play right render strategy count).2 := by
  induction count with
  | zero => exact ⟨same,rfl⟩
  | succ n ih =>
    simp only [play,←ih.2]
    exact ⟨advance_public _ _ ih.1 _,by rw [answer_public _ _ ih.1]⟩

theorem every_adaptive_prefix_keeps_original_financial_admissions {plan : Plan}
    (initial : Finance.State plan) (render : Render) (strategy : Strategy) (count : Nat) :
    initial.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (play initial render strategy count).1.account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial render strategy n).2 n).request with
    | error _ => simpa only [advance,requested] using ih
    | ok request =>
      cases request with
      | inl mode => simpa only [advance,requested] using ih.trans (original_financial_admissions_keep_their_identity (play initial render strategy n).1 mode)
      | inr request => simpa only [advance,requested] using ih.trans (Finance.State.every_original_issued_claim_keeps_its_identity (play initial render strategy n).1 request.1 request.2)

private theorem flow_zero (flow : Flow Actor Good)
    (absent : ∀ entry∈flow,entry.1≠(receiver,Good.feed)) : flowAt flow receiver .feed=0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  simp only [if_neg (absent entry inside)]

theorem private_step_keeps_own_frame (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (current : Current) (action : JointAction) (safe : Safe action) :
    Supply.Privacy.ownFrame ((law scope).step current action)=Supply.Privacy.ownFrame current := by
  have flows := safe_flows scope cost current action safe
  unfold RawLaw.step
  split
  · simp only [Supply.Privacy.ownFrame,RawLaw.paidStep,flow_zero _ flows.1,flow_zero _ flows.2,sub_zero,add_zero]
  · rfl

theorem private_execute_keeps_own_frame (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (current : Current) (actions : List JointAction) (safe : ∀ action∈actions,Safe action) (index : Nat) :
    Supply.Privacy.ownFrame ((law scope).execute current index actions).final=Supply.Privacy.ownFrame current := by
  induction actions generalizing current index with
  | nil => rfl
  | cons action rest ih =>
    change Supply.Privacy.ownFrame ((law scope).execute ((law scope).step current action) (index+1) rest).final=_
    rw [ih _ (fun action member => safe action (List.mem_cons_of_mem _ member)) (index+1),
      private_step_keeps_own_frame scope cost _ _ (safe action (by simp))]

theorem own_private_frame_survives {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    Supply.Privacy.ownFrame (next state mode).session.current=Supply.Privacy.ownFrame state.session.current := by
  change Supply.Privacy.ownFrame (Runtime.current state mode)=_
  rw [Runtime.current_is_own_root_next]
  change Supply.Privacy.ownFrame
    ((law state.session.window.scope).execute ((law state.session.window.scope).next state.session.current []) 0
      (word state.session.window.scope mode ((law state.session.window.scope).next state.session.current []))).final=_
  rw [private_execute_keeps_own_frame _ rfl _ _ (word_safe _ _ _) 0]
  rfl

theorem every_adaptive_prefix_keeps_its_own_private_frame {plan : Plan}
    (initial : Finance.State plan) (render : Render) (strategy : Strategy) (count : Nat) :
    Supply.Privacy.ownFrame (play initial render strategy count).1.session.current=Supply.Privacy.ownFrame initial.session.current := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial render strategy n).2 n).request with
    | error _ => simpa only [advance,requested] using ih
    | ok request =>
      cases request with
      | inl mode => simpa only [advance,requested] using (own_private_frame_survives (play initial render strategy n).1 mode).trans ih
      | inr request => simpa only [advance,requested,Finance.State.next] using (Supply.Privacy.Session.own_private_frame_survives (play initial render strategy n).1.session request.1 request.2).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive

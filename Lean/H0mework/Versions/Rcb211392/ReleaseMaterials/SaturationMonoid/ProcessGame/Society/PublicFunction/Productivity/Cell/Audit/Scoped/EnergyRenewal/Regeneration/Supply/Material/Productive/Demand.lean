import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Wire

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Demand
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
abbrev Item := Supply.Privacy.PublicItem

structure Rejected (items : List Item) where
  item : Item
  inside : item ∈ items
  refused : item.accepted = false

def firstRejected : (items : List Item) → Option (Rejected items)
  | [] => none
  | item::rest =>
    if accepted : item.accepted=true then
      (firstRejected rest).map fun later =>
        ⟨later.item,List.mem_cons_of_mem item later.inside,later.refused⟩
    else some ⟨item,by simp,by cases value : item.accepted <;> simp_all⟩

structure Gap where
  index : Nat
  actor : Actor
  good : Good
  required : ℚ
  available : ℚ
  deriving DecidableEq

def Gap.shortfall (gap : Gap) : ℚ := gap.required-gap.available

def coordinates : List (Actor × Good) :=
  [(customer,.feed),(supplier,.feed),(factory,.feed),(Refeed.donor,.feed),
   (customer,.waste),(supplier,.waste),(factory,.waste),(Refeed.donor,.waste)]

theorem coordinates_are_public (point : Actor × Good) (inside : point ∈ coordinates) :
    point ≠ (receiver,.feed) := by
  simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def gapAt (scope : Scope) (item : Item) (point : Actor × Good) : Option Gap :=
  if ((law scope).debit item.before item.request).any (fun entry => decide (entry.1=point)) then
    let required := flowAt ((law scope).debit item.before item.request) point.1 point.2
    let available := item.before.stock point.1 point.2
    if available < required then some ⟨item.index,point.1,point.2,required,available⟩ else none
  else none

theorem gapAt_exact (scope : Scope) (item : Item) (point : Actor × Good) (gap : Gap)
    (generated : gapAt scope item point = some gap) :
    gap.index=item.index ∧ (gap.actor,gap.good)=point ∧
    point ∈ ((law scope).debit item.before item.request).map Prod.fst ∧
    gap.required=flowAt ((law scope).debit item.before item.request) point.1 point.2 ∧
    gap.available=item.before.stock point.1 point.2 ∧ 0<gap.shortfall := by
  unfold gapAt at generated
  split at generated
  · rename_i used
    have present : point ∈ ((law scope).debit item.before item.request).map Prod.fst := by
      obtain ⟨entry,inside,equal⟩ := List.any_eq_true.mp used
      exact List.mem_map.mpr ⟨entry,inside,of_decide_eq_true equal⟩
    dsimp only at generated
    split at generated
    · rename_i shortage
      cases Option.some.inj generated
      exact ⟨rfl,Prod.eta _,present,rfl,rfl,by unfold Gap.shortfall;dsimp;linarith⟩
    · contradiction
  · contradiction

def gaps (scope : Scope) (item : Item) : List Gap := coordinates.filterMap (gapAt scope item)

structure Report where
  index : Nat
  request : JointAction
  gaps : List Gap

def diagnose (scope : Scope) (observation : Observation) : Option Report :=
  (firstRejected observation.actions).map fun rejected =>
    ⟨rejected.item.index,rejected.item.request,gaps scope rejected.item⟩

def inspect {plan : Plan} (state : Finance.State plan) (mode : Mode) : Option Report :=
  diagnose state.session.window.scope (observe state.session.window.scope mode state.session.current)

def sourceItems {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    List (ExecutionItem Actor Good Port Technology Instrument) :=
  match (Runtime.facade state mode).readoutAt (Runtime.activated state mode) .execution with
  | .inl ⟨_,result⟩ => result.interpreted.items
  | .inr impossible => nomatch impossible

theorem sourceItems_exact {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    sourceItems state mode=(law state.session.window.scope).rawItems
      ((law state.session.window.scope).next state.session.current [])
      (word state.session.window.scope mode ((law state.session.window.scope).next state.session.current [])) := rfl

def publicItem (scope : Scope) (item : ExecutionItem Actor Good Port Technology Instrument) : Item :=
  ⟨item.index,Supply.Privacy.publicize item.before,item.request,decide ((law scope).Valid item.before item.request),
    (law scope).actualDebit item.before item.request,(law scope).actualCredit item.before item.request,
    Supply.Privacy.publicize ((law scope).step item.before item.request)⟩

theorem observed_items_are_the_same_root_execution {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    (observe state.session.window.scope mode state.session.current).actions=
      (sourceItems state mode).map (publicItem state.session.window.scope) := by
  rw [sourceItems_exact]
  dsimp only [observe,publicItems]
  rw [execute_exact]
  rfl

theorem every_gap_is_from_the_rejected_source_item (scope : Scope) (observation : Observation)
    (report : Report) (generated : diagnose scope observation=some report)
    (gap : Gap) (present : gap ∈ report.gaps) :
    ∃ item ∈ observation.actions, item.accepted=false ∧ report.index=item.index ∧
      report.request=item.request ∧ gap.index=item.index ∧
      (gap.actor,gap.good) ∈ coordinates ∧
      (gap.actor,gap.good) ∈ ((law scope).debit item.before item.request).map Prod.fst ∧
      gap.required=flowAt ((law scope).debit item.before item.request) gap.actor gap.good ∧
      gap.available=item.before.stock gap.actor gap.good ∧ 0<gap.shortfall := by
  unfold diagnose at generated
  cases found : firstRejected observation.actions with
  | none => simp [found] at generated
  | some rejected =>
    simp only [found,Option.map_some,Option.some.injEq] at generated
    cases generated
    obtain ⟨point,inside,produced⟩ := List.mem_filterMap.mp present
    obtain ⟨index,location,used,required,available,positive⟩ := gapAt_exact scope rejected.item point gap produced
    cases location
    exact ⟨rejected.item,rejected.inside,rejected.refused,rfl,rfl,index,inside,used,required,available,positive⟩

theorem nominal_debit_ignores_the_private_frame (scope : Scope) (current : Current) (request : JointAction) :
    (law scope).debit (Supply.Privacy.publicize current) request=(law scope).debit current request := by
  cases request.operation <;> rfl

theorem every_demand_is_the_original_root_material_gap {plan : Plan}
    (state : Finance.State plan) (mode : Mode) (report : Report)
    (generated : inspect state mode=some report) (gap : Gap) (present : gap ∈ report.gaps) :
    ∃ item ∈ sourceItems state mode,
      ¬ (law state.session.window.scope).Valid item.before item.request ∧
      report.index=item.index ∧ report.request=item.request ∧ gap.index=item.index ∧
      (gap.actor,gap.good)≠(receiver,Good.feed) ∧
      gap.required=flowAt ((law state.session.window.scope).debit item.before item.request) gap.actor gap.good ∧
      gap.available=item.before.stock gap.actor gap.good ∧ 0<gap.shortfall := by
  obtain ⟨item,inside,refused,index,request,gapIndex,coordinate,used,required,available,positive⟩ :=
    every_gap_is_from_the_rejected_source_item _ _ report generated gap present
  rw [observed_items_are_the_same_root_execution] at inside
  obtain ⟨original,originalInside,rfl⟩ := List.mem_map.mp inside
  dsimp only [publicItem] at refused index request gapIndex used required available
  have visiblePoint := coordinates_are_public (gap.actor,gap.good) coordinate
  rw [nominal_debit_ignores_the_private_frame] at required
  have own : (Supply.Privacy.publicize original.before).stock gap.actor gap.good=
      original.before.stock gap.actor gap.good := by
    simp only [Supply.Privacy.publicize,Supply.Privacy.rebuild,if_neg visiblePoint]
  rw [own] at available
  exact ⟨original,originalInside,by simpa using refused,index,request,gapIndex,visiblePoint,required,available,positive⟩

theorem raw_gap_really_prevents_payment (scope : Scope)
    (item : ExecutionItem Actor Good Port Technology Instrument) (point : Actor × Good)
    (present : point ∈ ((law scope).debit item.before item.request).map Prod.fst)
    (missing : item.before.stock point.1 point.2 < flowAt ((law scope).debit item.before item.request) point.1 point.2) :
    ¬ (law scope).Valid item.before item.request ∧
      (law scope).actualDebit item.before item.request=[] ∧
      (law scope).actualCredit item.before item.request=[] ∧
      (law scope).step item.before item.request=item.before := by
  have refused : ¬ (law scope).Valid item.before item.request := by
    intro paid
    obtain ⟨_,_,_,_,_,stock⟩ := paid
    obtain ⟨entry,inside,same⟩ := List.mem_map.mp present
    have available := stock entry inside
    rw [same] at available
    exact (not_lt_of_ge available) missing
  exact ⟨refused,by simp [RawLaw.actualDebit,refused],by simp [RawLaw.actualCredit,refused],
    by simp [RawLaw.step,refused]⟩

theorem exact_demand_keeps_cumulative_privacy {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (mode : Mode) :
    inspect left mode=inspect right mode := by
  unfold inspect
  rw [←same.scope,observe_public same.current left.session.window.scope rfl mode]

theorem demand_continues_with_the_original_account {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (Productive.next state mode).account.current.slots.map (Financial.Family.slotClaim Finance.sources) :=
  original_financial_admissions_keep_their_identity state mode

def render : Option Report → Lean.Json
  | none => .null
  | some report => Lean.Json.mkObj [
    ("status",Lean.toJson (if report.gaps.isEmpty then "OTHER_ADMISSION_REFUSAL" else "MATERIAL_INPUT_REQUIRED")),
    ("index",Lean.toJson report.index),("request",Supply.Privacy.Wire.actionJson report.request),
    ("gaps",Lean.toJson (report.gaps.map fun gap => Lean.Json.mkObj [
      ("index",Lean.toJson gap.index),("actor",Supply.Privacy.Wire.actorJson gap.actor),
      ("good",Lean.toJson (Supply.Privacy.Wire.goodName gap.good)),
      ("required",Lean.toJson (toString gap.required)),("available",Lean.toJson (toString gap.available)),
      ("shortfall",Lean.toJson (toString gap.shortfall))]))]

def answer {plan : Plan} (state : Finance.State plan) (command : Command) : Lean.Json :=
  Lean.Json.mkObj [("reply",Wire.render command (Productive.answer state command)),
    ("materialDemand",match command.request with | .ok (.inl mode) => render (inspect state mode) | _ => .null)]

theorem complete_answer_is_public {lp rp : Plan} (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (command : Command) :
    answer left command=answer right command := by
  unfold answer
  rw [Productive.answer_public left right same command]
  cases requested : command.request with
  | error _ => rfl
  | ok request =>
    cases request with
    | inl mode => dsimp only;rw [exact_demand_keeps_cumulative_privacy left right same mode]
    | inr _ => rfl

def play {plan : Plan} (initial : Finance.State plan) (strategy : Strategy) : Nat → Finance.State plan × List Lean.Json
  | 0 => (initial,[])
  | n+1 =>
    let (state,past) := play initial strategy n
    let command := strategy past n
    (Productive.advance state command,past++[answer state command])

theorem every_adaptive_prefix_keeps_complete_demand_output {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (strategy : Strategy) (count : Nat) :
    Supply.Privacy.Source.SessionTwin (play left strategy count).1.session (play right strategy count).1.session ∧
      (play left strategy count).2=(play right strategy count).2 := by
  induction count with
  | zero => exact ⟨same,rfl⟩
  | succ n ih =>
    simp only [play,←ih.2]
    exact ⟨advance_public _ _ ih.1 _,by rw [complete_answer_is_public _ _ ih.1]⟩

theorem every_adaptive_prefix_keeps_original_claim_identity {plan : Plan}
    (initial : Finance.State plan) (strategy : Strategy) (count : Nat) :
    initial.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (play initial strategy count).1.account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial strategy n).2 n).request with
    | error _ => simpa only [Productive.advance,requested] using ih
    | ok request =>
      cases request with
      | inl mode => simpa only [Productive.advance,requested] using ih.trans (original_financial_admissions_keep_their_identity (play initial strategy n).1 mode)
      | inr request => simpa only [Productive.advance,requested] using ih.trans ((play initial strategy n).1.every_original_issued_claim_keeps_its_identity request.1 request.2)

theorem every_adaptive_prefix_keeps_own_private_frame {plan : Plan}
    (initial : Finance.State plan) (strategy : Strategy) (count : Nat) :
    Supply.Privacy.ownFrame (play initial strategy count).1.session.current=Supply.Privacy.ownFrame initial.session.current := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [play]
    cases requested : (strategy (play initial strategy n).2 n).request with
    | error _ => simpa only [Productive.advance,requested] using ih
    | ok request =>
      cases request with
      | inl mode => simpa only [Productive.advance,requested] using (own_private_frame_survives (play initial strategy n).1 mode).trans ih
      | inr request => simpa only [Productive.advance,requested,Finance.State.next] using (Supply.Privacy.Session.own_private_frame_survives (play initial strategy n).1.session request.1 request.2).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Demand

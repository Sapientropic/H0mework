import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Word

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Lean

def rebuild (visible : Current) (frame : ℚ) : Current :=
  {visible with stock:=fun actor good => if (actor,good)=(receiver,Good.feed) then frame else visible.stock actor good}
def ownFrame (current : Current) : ℚ := current.stock receiver .feed
def publicize (current : Current) : Current := rebuild current 0

theorem rebuild_twin (visible : Current) (frame : ℚ) : Twin visible (rebuild visible frame) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro actor good visible
  simp only [rebuild,if_neg visible]

theorem rebuild_from_twin {visible own : Current} (same : Twin visible own) : rebuild visible (ownFrame own)=own := by
  apply RawCurrent.ext
  · funext actor good
    by_cases hidden : (actor,good)=(receiver,Good.feed)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hidden
      simp [rebuild,ownFrame]
    · simp only [rebuild,if_neg hidden]
      exact same.stock actor good hidden
  · exact same.claims
  · exact same.technology
  · exact same.clock
  · exact same.round

theorem Twin.publicize {left right : Current} (same : Twin left right) : Supply.Privacy.publicize left=Supply.Privacy.publicize right := by
  apply RawCurrent.ext
  · funext actor good
    by_cases hidden : (actor,good)=(receiver,Good.feed)
    · simp only [Supply.Privacy.publicize,rebuild,if_pos hidden]
    · simp only [Supply.Privacy.publicize,rebuild,if_neg hidden,same.stock actor good hidden]
  · exact same.claims
  · exact same.technology
  · exact same.clock
  · exact same.round

private theorem flow_zero (flow : Flow Actor Good)
    (absent : ∀ entry∈flow,entry.1≠(receiver,Good.feed)) : flowAt flow receiver .feed=0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  simp only [if_neg (absent entry inside)]

theorem private_step_is_its_own_frame (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (current : Current) (action : JointAction) (safe : Safe action) :
    ownFrame ((law scope).step current action)=ownFrame current := by
  have flows := safe_flows scope cost current action safe
  unfold RawLaw.step
  split
  · simp only [ownFrame,RawLaw.paidStep,flow_zero _ flows.1,flow_zero _ flows.2,sub_zero,add_zero]
  · rfl

theorem private_execute_is_its_own_frame (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (current : Current) (actions : List JointAction) (safe : ∀ action∈actions,Safe action) (index : Nat) :
    ownFrame ((law scope).execute current index actions).final=ownFrame current := by
  induction actions generalizing current index with
  | nil => rfl
  | cons action rest ih =>
    change ownFrame ((law scope).execute ((law scope).step current action) (index+1) rest).final=_
    rw [ih _ (fun action member => safe action (List.mem_cons_of_mem _ member)) (index+1),
      private_step_is_its_own_frame scope cost _ _ (safe action (by simp))]

theorem rebuild_commutes_with_actual_generated_word (scope : Scope) (cost : scope.revisionCost=[(.energy,1)])
    (visible : Current) (frame : ℚ) (target : Party) (query : Query) (mode : Mode) :
    rebuild ((law scope).next visible (word scope target query mode visible)) frame=
      (law scope).next (rebuild visible frame) (word scope target query mode (rebuild visible frame)) := by
  have same := source_word_generates_related_own_next (rebuild_twin visible frame) scope cost target query mode
  have own : ownFrame ((law scope).next (rebuild visible frame)
      (word scope target query mode (rebuild visible frame)))=frame := by
    change ownFrame ((law scope).execute (rebuild visible frame) 0
      (word scope target query mode (rebuild visible frame))).final=frame
    rw [private_execute_is_its_own_frame scope cost _ _ (word_safe _ _ _ _ _) 0]
    simp [ownFrame,rebuild]
  simpa only [own] using rebuild_from_twin same.2

/-- Full original roots, not a replacement endpoint, supply each side's successor. -/
theorem original_session_roots_have_related_successors {lp rp : Plan} (left : Session lp) (right : Session rp)
    (scope : left.window.scope=right.window.scope) (target : left.target=right.target)
    (same : Twin left.current right.current) (query : Query) (mode : Mode) :
    Twin (ProgrammeSource.rawCurrent (left.input query mode) (ProgrammeHistory.visitAt (left.input query mode) 2).current)
      (ProgrammeSource.rawCurrent (right.input query mode) (ProgrammeHistory.visitAt (right.input query mode) 2).current) := by
  rw [left.after_is_own_root_next,right.after_is_own_root_next]
  unfold Session.after Session.actions Session.prepared
  rw [cachedNext_exact,cachedNext_exact,←scope,←target]
  have prepared := same.next left.window.scope rfl [] (by simp)
  exact (source_word_generates_related_own_next prepared left.window.scope rfl left.target query mode).2

structure PublicItem where
  index : Nat
  before : Current
  request : JointAction
  accepted : Bool
  debit : Flow Actor Good
  credit : Flow Actor Good
  after : Current

def publicItems (scope : Scope) (before : Current) (actions : List JointAction) (index : Nat) : List PublicItem :=
  ((law scope).execute before index actions).items.map fun item =>
    ⟨item.index,publicize item.before,item.request,decide ((law scope).Valid item.before item.request),
      (law scope).actualDebit item.before item.request,(law scope).actualCredit item.before item.request,
      publicize ((law scope).step item.before item.request)⟩

theorem Twin.publicItems {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (actions : List JointAction)
    (safe : ∀ action∈actions,Safe action) (index : Nat) :
    Supply.Privacy.publicItems scope left actions index=Supply.Privacy.publicItems scope right actions index := by
  induction actions generalizing left right index with
  | nil => rfl
  | cons action rest ih =>
    have front := safe action (by simp)
    have valid := same.valid scope cost action front
    have paid : decide ((law scope).Valid left action)=decide ((law scope).Valid right action) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using valid
    have debit : (law scope).actualDebit left action=(law scope).actualDebit right action := by
      simp only [RawLaw.actualDebit,propext valid,same.debit scope action]
    have credit : (law scope).actualCredit left action=(law scope).actualCredit right action := by
      simp only [RawLaw.actualCredit,propext valid,same.credit scope action]
    simp only [Supply.Privacy.publicItems,RawLaw.execute,List.map_cons]
    change PublicItem.mk _ (Supply.Privacy.publicize left) action _ _ _ _ :: Supply.Privacy.publicItems scope ((law scope).step left action) rest (index+1)=
      PublicItem.mk _ (Supply.Privacy.publicize right) action _ _ _ _ :: Supply.Privacy.publicItems scope ((law scope).step right action) rest (index+1)
    rw [same.publicize,paid,debit,credit,(same.step scope cost action front).publicize,
      ih (same.step scope cost action front) (fun action member => safe action (List.mem_cons_of_mem _ member)) (index+1)]

/-- Every public action field, actual fee/debit, failure and full public successor belongs to the observation. -/
structure Observation where
  actions : List PublicItem
  next : Current

def observe (scope : Scope) (target : Party) (query : Query) (mode : Mode) (current : Current) : Observation :=
  ⟨Supply.Privacy.publicItems scope current (word scope target query mode current) 0,
   publicize ((law scope).next current (word scope target query mode current))⟩

theorem Twin.observe {left right : Current} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)]) (target : Party) (query : Query) (mode : Mode) :
    observe scope target query mode left=observe scope target query mode right := by
  unfold Supply.Privacy.observe
  rw [←same.word scope cost target query mode]
  rw [same.publicItems scope cost _ (word_safe _ _ _ _ _) 0,
    (same.next scope cost _ (word_safe _ _ _ _ _)).publicize]

theorem private_feed_spending_cannot_enter_the_generated_vocabulary (actor : Actor) :
    ¬ Safe (⟨actor,[],.exchange,[],.use receiver [(.feed,1)] .external⟩ : JointAction) := by
  simp [Safe,Energy,ProviderOnly,feed,obligation,shipment]

theorem provider_fuel_is_public {left right : Current} (same : Twin left right) :
    left.stock supplier .feed=right.stock supplier .feed := same.stock _ _ (by simp [supplier,receiver])

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy

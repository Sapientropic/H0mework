import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderDispatch
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev model := ProductiveHeaderSource.model
abbrev start := ProductiveHeaderSource.start
abbrev vocabulary := ProductiveHeaderSource.vocabulary
abbrev law := ProductiveHeaderSource.law
abbrev scope := ProductiveHeaderSource.scope
abbrev zero := ProductiveHeaderSource.zero
abbrev one := ProductiveHeaderSource.one
abbrev State := LocalCommandRun.State model start

def work := ProductiveMandateSource.body.take 4
-- A refused attempt does not mark a production instruction as performed.
def performed (state : State) (request : ProductiveMandateSource.Action) : Bool :=
  (StageTrace.records start state.stages).any fun row =>
    (StageTrace.items row).any fun item => decide (item.request = request ∧ model.source.code.law.Valid item.before item.request)
def nextWork (state : State) := work.find? (fun request => !performed state request)
def workingFor (state : State) (expected : Option ProductiveMandateSource.Action) (input : LocalCommandSource.Input) : Bool :=
  match input with
  | .command index =>
    if model.source.code.actions[index]? = expected then
      match expected with
      | none => false
      | some request =>
        let row := HeaderDispatch.row model start state input
        decide (row.submitted = [request] ∧ ∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request)
    else false
  | _ => false
def working (state : State) := workingFor state (nextWork state)
def offers (state : State) : List LocalCommandSource.Input :=
  let menu := DynamicCommandSource.menu model start 0 state
  let expected := nextWork state
  menu.filter (HeaderDispatch.delivery model start vocabulary law state) ++
    menu.filter (workingFor state expected) ++
    menu.filter (HeaderDispatch.sending model start vocabulary law state) ++ menu
def choose (state : State) : LocalCommandSource.Input :=
  let menu := DynamicCommandSource.menu model start 0 state
  ((menu.find? (HeaderDispatch.delivery model start vocabulary law state)).orElse fun _ =>
    (menu.find? (workingFor state (nextWork state))).orElse fun _ =>
      (menu.find? (HeaderDispatch.sending model start vocabulary law state)).orElse fun _ => menu.head?).getD .idle

theorem choose_is_the_first_offer (state : State) : choose state = (offers state).headD .idle := by
  simp [choose,offers,List.headD_eq_head?_getD,List.head?_append]

theorem every_offer_is_in_the_actual_dynamic_domain
    (state : State) (input : LocalCommandSource.Input) (inside : input ∈ offers state) :
    input ∈ DynamicCommandSource.menu model start 0 state := by
  simp only [offers,List.mem_append] at inside
  rcases inside with ((first | second) | third) | fourth
  · exact (List.mem_filter.mp first).1
  · exact (List.mem_filter.mp second).1
  · exact (List.mem_filter.mp third).1
  · exact fourth

theorem every_choice_is_in_the_original_source_menu (state : State) :
    choose state ∈ CommandWindowSource.menu model := by
  cases actual : offers state with
  | nil => simp only [choose_is_the_first_offer,actual,List.headD_nil]; exact List.mem_cons_self
  | cons input rest =>
    have inside : input ∈ offers state := by rw [actual]; exact List.mem_cons_self
    simpa only [choose_is_the_first_offer,actual,List.headD_cons] using
      (List.mem_filter.mp (every_offer_is_in_the_actual_dynamic_domain state input inside)).1

theorem positive_actual_fuel_admits_the_generated_choice
    (state : State) (live : 0 < (EventStep.seed (state.current model start)).remaining) :
    choose state ∈ DynamicCommandSource.menu model start 0 state := by
  have menu := LiveDynamicCommandDomain.positive_actual_fuel_generates_a_nonempty_dynamic_domain model start 0 state live
  have nonempty : offers state ≠ [] := by
    intro empty
    have count := congrArg List.length empty
    simp only [offers,List.length_append,List.length_nil] at count
    have zero : (DynamicCommandSource.menu model start 0 state).length = 0 := by omega
    exact menu (List.eq_nil_of_length_eq_zero zero)
  exact every_offer_is_in_the_actual_dynamic_domain state _
    (by cases actual : offers state with
        | nil => exact False.elim (nonempty actual)
        | cons input rest => simp only [choose_is_the_first_offer,actual,List.headD_cons]; exact List.mem_cons_self)

def journey (state : State) : Nat → State × List LocalCommandSource.Input :=
  Nat.rec (state,[]) (fun _ previous =>
    let input := choose previous.1
    (LocalCommandRun.step model start previous.1 input,previous.2 ++ [input]))
def admitted (state : State) : Nat → DynamicCommandSource.Outcome model start 0 :=
  DynamicCommandSource.actual model start 0 (fun _ before => choose before) state

theorem every_generated_prefix_spends_its_original_invocation_account
    (state : State) (count : Nat) :
    (EventStep.seed ((journey state count).1.current model start)).remaining =
      (EventStep.seed (state.current model start)).remaining-count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (EventStep.seed ((LocalCommandRun.step model start (journey state count).1
      (choose (journey state count).1)).current model start)).remaining = _
    rw [HeaderDispatch.every_actual_dispatch_step_spends_its_original_invocation model start _ _,ih]
    omega

theorem original_fuel_generates_the_entire_admitted_productive_dispatch
    (state : State) (count : Nat) (funded : count ≤ (EventStep.seed (state.current model start)).remaining) :
    admitted state count = .running (journey state count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have before := ih (by omega)
    have live : 0 < (EventStep.seed ((journey state count).1.current model start)).remaining := by
      rw [every_generated_prefix_spends_its_original_invocation_account]
      omega
    have allowed := (List.mem_filter.mp (positive_actual_fuel_admits_the_generated_choice _ live)).2
    change DynamicCommandSource.tick model start 0 (fun _ previous => choose previous) count (admitted state count) = _
    rw [before]
    simp only [DynamicCommandSource.tick,DynamicCommandSource.submit,allowed,dif_pos]
    rfl

theorem resuming_the_actual_state_is_the_same_generated_execution
    (state : State) (before after : Nat) :
    (journey state (before+after)).1 = (journey (journey state before).1 after).1 := by
  induction after with
  | zero => rfl
  | succ after ih => exact congrArg (fun current => LocalCommandRun.step model start current (choose current)) ih

theorem the_generated_transcript_executes_the_same_actual_state (state : State) (count : Nat) :
    (journey state count).1 = (journey state count).2.foldl (LocalCommandRun.step model start) state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change LocalCommandRun.step model start (journey state count).1 _ = ((journey state count).2 ++ [_]).foldl _ state
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,← ih]
def initial : State := LocalCommandRun.initial model start
def actual := (journey initial 21).1
def observed (state : State) (receiver : Fin model.source.code.sites) :=
  HeaderReception.run vocabulary law start state.stages receiver state.stages.length
def decideAt (state : State) (receiver : Fin model.source.code.sites) :=
  HeaderQuorum.produce start vocabulary law state.stages receiver scope 2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchSource

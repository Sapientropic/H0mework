import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderDispatch

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkDispatch
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (law : StageReception.Law model.source.code)
  (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))
abbrev State := LocalCommandRun.State model start

-- A refused attempt does not mark a production instruction as performed.
def performed (state : State model start) (request : Request Party Good Port (Mandate.State Party Technology) Instrument) : Bool :=
  (StageTrace.records start state.stages).any fun row =>
    (StageTrace.items row).any fun item => decide (item.request = request ∧ model.source.code.law.Valid item.before item.request)
def nextWork (state : State model start) := work.find? (fun request => !performed model start state request)
def workingFor (state : State model start) (expected : Option (Request Party Good Port (Mandate.State Party Technology) Instrument)) (input : LocalCommandSource.Input) : Bool :=
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
def working (state : State model start) := workingFor model start state (nextWork model start work state)
def offers (state : State model start) : List LocalCommandSource.Input :=
  let menu := DynamicCommandSource.menu model start 0 state
  let expected := nextWork model start work state
  menu.filter (HeaderDispatch.delivery model start vocabulary law state) ++
    menu.filter (workingFor model start state expected) ++
    menu.filter (HeaderDispatch.sending model start vocabulary law state) ++ menu
def choose (state : State model start) : LocalCommandSource.Input :=
  let menu := DynamicCommandSource.menu model start 0 state
  ((menu.find? (HeaderDispatch.delivery model start vocabulary law state)).orElse fun _ =>
    (menu.find? (workingFor model start state (nextWork model start work state))).orElse fun _ =>
      (menu.find? (HeaderDispatch.sending model start vocabulary law state)).orElse fun _ => menu.head?).getD .idle

theorem choose_is_the_first_offer (state : State model start) : choose model start vocabulary law work state = (offers model start vocabulary law work state).headD .idle := by
  simp [choose,offers,List.headD_eq_head?_getD,List.head?_append]

theorem every_offer_is_in_the_actual_dynamic_domain
    (state : State model start) (input : LocalCommandSource.Input) (inside : input ∈ offers model start vocabulary law work state) :
    input ∈ DynamicCommandSource.menu model start 0 state := by
  simp only [offers,List.mem_append] at inside
  rcases inside with ((first | second) | third) | fourth
  · exact (List.mem_filter.mp first).1
  · exact (List.mem_filter.mp second).1
  · exact (List.mem_filter.mp third).1
  · exact fourth

theorem every_choice_is_in_the_original_source_menu (state : State model start) :
    choose model start vocabulary law work state ∈ CommandWindowSource.menu model := by
  cases actual : offers model start vocabulary law work state with
  | nil => simp only [choose_is_the_first_offer,actual,List.headD_nil]; exact List.mem_cons_self
  | cons input rest =>
    have inside : input ∈ offers model start vocabulary law work state := by rw [actual]; exact List.mem_cons_self
    simpa only [choose_is_the_first_offer,actual,List.headD_cons] using
      (List.mem_filter.mp (every_offer_is_in_the_actual_dynamic_domain model start vocabulary law work state input inside)).1

theorem positive_actual_fuel_admits_the_generated_choice
    (state : State model start) (live : 0 < (EventStep.seed (state.current model start)).remaining) :
    choose model start vocabulary law work state ∈ DynamicCommandSource.menu model start 0 state := by
  have menu := LiveDynamicCommandDomain.positive_actual_fuel_generates_a_nonempty_dynamic_domain model start 0 state live
  have nonempty : offers model start vocabulary law work state ≠ [] := by
    intro empty
    have count := congrArg List.length empty
    simp only [offers,List.length_append,List.length_nil] at count
    have zero : (DynamicCommandSource.menu model start 0 state).length = 0 := by omega
    exact menu (List.eq_nil_of_length_eq_zero zero)
  exact every_offer_is_in_the_actual_dynamic_domain model start vocabulary law work state _
    (by cases actual : offers model start vocabulary law work state with
        | nil => exact False.elim (nonempty actual)
        | cons input rest => simp only [choose_is_the_first_offer,actual,List.headD_cons]; exact List.mem_cons_self)

def journey (state : State model start) : Nat → State model start × List LocalCommandSource.Input :=
  Nat.rec (state,[]) (fun _ previous =>
    let input := choose model start vocabulary law work previous.1
    (LocalCommandRun.step model start previous.1 input,previous.2 ++ [input]))
def admitted (state : State model start) : Nat → DynamicCommandSource.Outcome model start 0 :=
  DynamicCommandSource.actual model start 0 (fun _ before => choose model start vocabulary law work before) state

theorem every_generated_prefix_spends_its_original_invocation_account
    (state : State model start) (count : Nat) :
    (EventStep.seed ((journey model start vocabulary law work state count).1.current model start)).remaining =
      (EventStep.seed (state.current model start)).remaining-count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (EventStep.seed ((LocalCommandRun.step model start (journey model start vocabulary law work state count).1
      (choose model start vocabulary law work (journey model start vocabulary law work state count).1)).current model start)).remaining = _
    rw [HeaderDispatch.every_actual_dispatch_step_spends_its_original_invocation model start _ _,ih]
    omega

theorem original_fuel_generates_the_entire_admitted_productive_dispatch
    (state : State model start) (count : Nat) (funded : count ≤ (EventStep.seed (state.current model start)).remaining) :
    admitted model start vocabulary law work state count = .running (journey model start vocabulary law work state count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have before := ih (by omega)
    have live : 0 < (EventStep.seed ((journey model start vocabulary law work state count).1.current model start)).remaining := by
      rw [every_generated_prefix_spends_its_original_invocation_account]
      omega
    have allowed := (List.mem_filter.mp (positive_actual_fuel_admits_the_generated_choice model start vocabulary law work _ live)).2
    change DynamicCommandSource.tick model start 0 (fun _ previous => choose model start vocabulary law work previous) count (admitted model start vocabulary law work state count) = _
    rw [before]
    simp only [DynamicCommandSource.tick,DynamicCommandSource.submit,allowed,dif_pos]
    rfl

theorem resuming_the_actual_state_is_the_same_generated_execution
    (state : State model start) (before after : Nat) :
    (journey model start vocabulary law work state (before+after)).1 = (journey model start vocabulary law work (journey model start vocabulary law work state before).1 after).1 := by
  induction after with
  | zero => rfl
  | succ after ih => exact congrArg (fun current => LocalCommandRun.step model start current (choose model start vocabulary law work current)) ih

theorem the_generated_transcript_executes_the_same_actual_state (state : State model start) (count : Nat) :
    (journey model start vocabulary law work state count).1 = (journey model start vocabulary law work state count).2.foldl (LocalCommandRun.step model start) state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change LocalCommandRun.step model start (journey model start vocabulary law work state count).1 _ = ((journey model start vocabulary law work state count).2 ++ [_]).foldl _ state
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,← ih]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkDispatch

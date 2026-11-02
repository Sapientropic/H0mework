import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Support

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

/-- All submitted local and external requests retain their primitive source. -/
def requests : List (Request Party Good Port Technology Instrument) :=
  code.actions ++ code.eventAlphabet.filterMap (fun event => match event with
    | .adversary request => some request | _ => none) ++
  (List.finRange code.sites).flatMap (fun sender =>
    (List.finRange code.sites).flatMap fun recipient => code.sendCost sender recipient) ++
  (List.finRange code.sites).flatMap fun recipient => code.deliveryCost recipient

def revision (request : Request Party Good Port Technology Instrument) : Option Technology :=
  match request.operation with | .revise _ technology => some technology | _ => none

def technologies (initial : List Technology) : List Technology := initial ++ (requests code).filterMap revision

theorem each_source_revision_enters_the_generated_technology_menu
    (initial : List Technology) (request : Request Party Good Port Technology Instrument)
    (source : request ∈ requests code) (operator : Party) (target : Technology)
    (changed : request.operation = .revise operator target) : target ∈ technologies code initial :=
  List.mem_append_right _ (List.mem_filterMap.mpr ⟨request,source,by simp [revision,changed]⟩)

private theorem each_local_action_is_source_generated (policy : code.Policy)
    (supported : Normalization.Supported code policy) (site : Fin code.sites) (signal : Fin code.signals) :
    ∀ request ∈ code.action policy site signal,request ∈ requests code := by
  intro request inside
  have original : request ∈ code.actions := by
    unfold Code.action at inside
    split at inside
    · exact supported _ _ request inside
    · simp only [List.not_mem_nil] at inside
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ original))

private theorem each_chosen_request_is_source_generated (policy : code.Policy)
    (supported : Normalization.Supported code policy) (state : State code) (choice : Choice code) :
    ∀ request ∈ (stepLocal code policy state choice.val).word,request ∈ requests code := by
  rcases choice with ⟨event,original⟩
  cases event with
  | adversary action =>
    intro request inside
    have same : request = action := List.mem_singleton.mp inside
    subst request
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_filterMap.mpr ⟨.adversary action,original,rfl⟩)))
  | send sender recipient =>
    intro request inside
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨sender,List.mem_finRange _,List.mem_flatMap.mpr ⟨recipient,List.mem_finRange _,inside⟩⟩))
  | deliver address =>
    simp only [stepLocal,Code.step]
    cases packet : state.frame.sent[address]? with
    | none => simp
    | some message =>
      intro request inside
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨message.recipient,List.mem_finRange _,inside⟩)
  | activate site => exact each_local_action_is_source_generated code policy supported site _

theorem every_actual_submitted_word_uses_primitive_source_requests
    (policy : Option code.Policy) (supported : ∀ raw,policy = some raw → Normalization.Supported code raw)
    (input : Input code) (state : State code) :
    ∀ request ∈ word code policy input state,request ∈ requests code := by
  cases policy with
  | none => simp [word]
  | some policy =>
    cases chosen : decision code input state with
    | none => simp [word,chosen]
    | some event => simpa only [word,chosen] using
        each_chosen_request_is_source_generated code policy (supported _ rfl) state event

theorem each_executed_source_word_keeps_all_intermediate_technologies
    (initial : List Technology) (current : RawCurrent Party Good Technology Instrument)
    (known : current.technology ∈ technologies code initial)
    (word : RawEvent Party Good Port Technology Instrument)
    (source : ∀ request ∈ word,request ∈ requests code) (index : Nat) :
    (code.law.execute current index word).final.technology ∈ technologies code initial ∧
    ∀ item ∈ (code.law.execute current index word).items,item.before.technology ∈ technologies code initial := by
  induction word generalizing current index with
  | nil => exact ⟨known,by simp [RawLaw.execute]⟩
  | cons request tail ih =>
    have next : (code.law.step current request).technology ∈ technologies code initial := by
      by_cases accepted : code.law.Valid current request
      · simp only [RawLaw.step,if_pos accepted,RawLaw.paidStep]
        cases operation : request.operation with
        | revise operator technology =>
          exact each_source_revision_enters_the_generated_technology_menu code initial request
            (source request List.mem_cons_self) operator technology operation
        | _ => exact known
      · simpa only [RawLaw.step,if_neg accepted] using known
    have rest := ih (code.law.step current request) next
      (fun action inside => source action (List.mem_cons_of_mem _ inside)) (index+1)
    exact ⟨rest.1,by simpa only [RawLaw.execute,List.forall_mem_cons] using And.intro known rest.2⟩

theorem every_actual_raw_run_stays_in_the_source_technology_menu
    (initial : List Technology) (schedule : Residual.Schedule code) (input : Input code) (seed : State code)
    (known : seed.current.technology ∈ technologies code initial) (horizon : Nat)
    (supported : ∀ n < horizon,∀ policy,schedule n = some policy → Normalization.Supported code policy)
    (n : Nat) (inside : n ≤ horizon) :
    (Residual.run code schedule input seed n).current.technology ∈ technologies code initial := by
  induction n with
  | zero => exact known
  | succ n ih =>
    have prior := ih (by omega)
    have primitive := every_actual_submitted_word_uses_primitive_source_requests code (schedule n)
      (supported n (by omega)) input (Residual.run code schedule input seed n)
    exact (each_executed_source_word_keeps_all_intermediate_technologies code initial _ prior _ primitive 0).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic

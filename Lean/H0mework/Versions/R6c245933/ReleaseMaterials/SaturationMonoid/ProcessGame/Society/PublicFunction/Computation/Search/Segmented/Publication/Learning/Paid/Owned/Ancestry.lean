import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Planner

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Ancestry
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication
open Publication.Reservation.Feedback.Asynchronous

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def Trace (initial : List (View (code := code))) (past : List (Prefix.Rule code))
    (view : View (code := code)) : Prop :=
  ∃ first ∈ initial, ∃ stages : List (EventHistory.Stage (code := code)),
    stages.map Prod.fst = past ∧ view.point = EventHistory.execute first.point stages ∧
    view.origin.val = first.origin.val

def Generated (initial : List (View (code := code))) (past : List (Prefix.Rule code))
    (beliefs : List (View (code := code))) : Prop := ∀ view ∈ beliefs, Trace initial past view

theorem execute_append (point : Cursor code) (left right : List (EventHistory.Stage (code := code))) :
    EventHistory.execute point (left ++ right) = EventHistory.execute (EventHistory.execute point left) right := by
  induction left generalizing point with
  | nil => rfl
  | cons stage rest ih => exact ih (point.after stage.1 stage.2)

theorem each_initial_belief_is_its_own_native_origin (initial : List (View (code := code))) :
    Generated initial [] initial := by
  intro view member
  exact ⟨view,member,[],rfl,rfl,rfl⟩

theorem each_actual_step_extends_its_original_trace
    {initial : List (View (code := code))} {past : List (Prefix.Rule code)}
    {view : View (code := code)} (prior : Trace initial past view)
    (rule : Prefix.Rule code) (rival : Opponent code) :
    Trace initial (past ++ [rule]) (Evidence.after view rule rival) := by
  obtain ⟨first,member,stages,rules,point,origin⟩ := prior
  refine ⟨first,member,stages ++ [(rule,rival)],?_,?_,origin⟩
  · simp only [List.map_append,List.map_cons,List.map_nil,rules]
  · rw [execute_append]
    change view.point.after rule rival = (EventHistory.execute first.point stages).after rule rival
    rw [point]

theorem every_public_next_belief_retains_its_actual_native_trace
    {initial : List (View (code := code))} {past : List (Prefix.Rule code)}
    {beliefs : List (View (code := code))} (prior : Generated initial past beliefs)
    (rule : Prefix.Rule code) : Generated initial (past ++ [rule]) (PublicDomain.next rule beliefs) := by
  intro next member
  obtain ⟨previous,inside,rival,same⟩ := Rolling.Receipt.Domain.every_public_successor_retains_its_actual_predecessor
    beliefs rule next member
  rw [same]
  exact each_actual_step_extends_its_original_trace (prior previous inside) rule rival

theorem every_public_finite_prefix_retains_its_actual_native_trace
    {initial : List (View (code := code))} {past : List (Prefix.Rule code)}
    {beliefs : List (View (code := code))} (prior : Generated initial past beliefs)
    (published : List (Prefix.Rule code)) :
    Generated initial (past ++ published) (Window.Observed.Transcript.publicViews published beliefs) := by
  induction published generalizing past beliefs with
  | nil => simpa only [List.append_nil,Window.Observed.Transcript.publicViews,List.foldl_nil] using prior
  | cons rule rest ih =>
      have next := every_public_next_belief_retains_its_actual_native_trace prior rule
      have later := ih next
      simpa only [List.append_assoc,List.singleton_append,Window.Observed.Transcript.publicViews,List.foldl_cons] using later

theorem removing_beliefs_preserves_their_actual_native_traces
    {initial : List (View (code := code))} {past : List (Prefix.Rule code)}
    {beliefs selected : List (View (code := code))} (prior : Generated initial past beliefs)
    (retained : ∀ view ∈ selected,view ∈ beliefs) : Generated initial past selected :=
  fun view member => prior view (retained view member)

section GenericState
variable {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}
  {initial : List (View (code := model.source.code))}
  (state : Paid.State model domain original baseline actualHorizon)

theorem carrying_keeps_every_beliefs_actual_trace
    (prior : Generated initial state.past state.beliefs) (rule : Prefix.Rule model.source.code)
    (booked : state.Booked rule) : Generated initial (state.carry rule booked).past (state.carry rule booked).beliefs :=
  every_public_finite_prefix_retains_its_actual_native_trace prior [rule]

theorem committing_keeps_every_beliefs_actual_trace
    (prior : Generated initial state.past state.beliefs)
    (reader : Fin model.source.code.sites) (reading : Fin model.source.code.signals)
    (decision : state.Decision reader) :
    Generated initial (state.commit reader reading decision).past (state.commit reader reading decision).beliefs := by
  cases decision <;>
    exact removing_beliefs_preserves_their_actual_native_traces prior
      (fun view member => ((mem_fiber _ _ _ _).mp member).1)

theorem driving_keeps_every_beliefs_actual_trace
    (prior : Generated initial state.past state.beliefs) :
    Generated initial (Driving.Progress.next state).past (Driving.Progress.next state).beliefs := by
  unfold Driving.Progress.next
  split
  · exact every_public_finite_prefix_retains_its_actual_native_trace prior [Driving.Progress.rule state]
  · exact prior

end GenericState

variable (input : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  {initial : List (View (code := input.model.source.code))}

theorem advancing_keeps_every_beliefs_actual_trace (cache : Cache input)
    (prior : Generated initial cache.past cache.beliefs) :
    Generated initial (advance input cache).past (advance input cache).beliefs := by
  exact removing_beliefs_preserves_their_actual_native_traces (driving_keeps_every_beliefs_actual_trace cache prior)
    (Reception.condition_only_removes_existing_beliefs _ _ _)

theorem each_paid_walk_keeps_every_beliefs_actual_trace {cache : Cache input}
    (walk : Walk input cache) (prior : Generated initial cache.past cache.beliefs) :
    Generated initial walk.final.past walk.final.beliefs := by
  induction walk with
  | exhausted | terminal => exact prior
  | @learned state live owned decision =>
      exact advancing_keeps_every_beliefs_actual_trace input _
        (committing_keeps_every_beliefs_actual_trace state prior _ _ decision)
  | waiting live foreign later ih => exact ih (advancing_keeps_every_beliefs_actual_trace input _ prior)

theorem each_paid_or_refused_turn_keeps_every_beliefs_actual_trace {cache : Cache input}
    (event : Turn input cache) (prior : Generated initial cache.past cache.beliefs) :
    Generated initial event.final.past event.final.beliefs := by
  cases event with
  | unsupported => exact prior
  | unreserved =>
      change Generated initial (if input.continueUnreserved then advance input cache else cache).past
        (if input.continueUnreserved then advance input cache else cache).beliefs
      split
      · exact advancing_keeps_every_beliefs_actual_trace input cache prior
      · exact prior
  | unpaid supported booked missing => exact carrying_keeps_every_beliefs_actual_trace cache prior _ booked
  | paid supported booked receipt walk =>
      exact each_paid_walk_keeps_every_beliefs_actual_trace input walk
        (carrying_keeps_every_beliefs_actual_trace cache prior _ booked)

theorem every_finite_paid_run_keeps_every_beliefs_actual_trace (rounds : Nat) (cache : Cache input)
    (prior : Generated initial cache.past cache.beliefs) :
    Generated initial (run input rounds cache).past (run input rounds cache).beliefs := by
  induction rounds generalizing cache with
  | zero => exact prior
  | succ rounds ih => exact ih _ (each_paid_or_refused_turn_keeps_every_beliefs_actual_trace input _ prior)

theorem every_source_generated_posterior_has_actual_origins (rounds : Nat) :
    match Source.response input rounds with
    | .inl _ => True
    | .inr cache => Generated (Source.initialBeliefs input) cache.past cache.beliefs := by
  unfold Source.response Source.generate
  cases Source.seed input with
  | rejected => trivial
  | accepted cache empty programme beliefs =>
      change Generated (Source.initialBeliefs input) (trace input rounds cache).1.past (trace input rounds cache).1.beliefs
      rw [trace_is_the_original_run_and_reports]
      apply every_finite_paid_run_keeps_every_beliefs_actual_trace
      rw [empty,beliefs]
      exact each_initial_belief_is_its_own_native_origin _

theorem every_emitted_posterior_has_actual_origins (rounds : Nat) (made : Source.Occurrence input rounds) :
    match made.response with
    | .inl _ => True
    | .inr cache => Generated (Source.initialBeliefs input) cache.past cache.beliefs := by
  have same : made.response = Source.response input rounds := by
    unfold Source.Occurrence.response Source.response
    rw [made.exact_generation]
  rw [same]
  exact every_source_generated_posterior_has_actual_origins input rounds

theorem every_emitted_belief_spells_the_original_paid_past (rounds : Nat) (made : Source.Occurrence input rounds) :
    match made.response with
    | .inl _ => True
    | .inr cache => ∀ view ∈ cache.beliefs,
        ∃ first ∈ input.domain, ∃ stages : List (EventHistory.Stage (code := input.model.source.code)),
          stages.map Prod.fst = cache.past ∧ view.point = EventHistory.execute first stages ∧
          view.origin.val = arrival first := by
  have all := every_emitted_posterior_has_actual_origins input rounds made
  cases outcome : made.response with
  | inl => trivial
  | inr cache =>
      rw [outcome] at all
      intro view member
      obtain ⟨first,inside,stages,rules,point,origin⟩ := all view member
      obtain ⟨cursor,initial,same⟩ := List.mem_map.mp inside
      subst first
      exact ⟨cursor,initial,stages,rules,point,origin⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Ancestry

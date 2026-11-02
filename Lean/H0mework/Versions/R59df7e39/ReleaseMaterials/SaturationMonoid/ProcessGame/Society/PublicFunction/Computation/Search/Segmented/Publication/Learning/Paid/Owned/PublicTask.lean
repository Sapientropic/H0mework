import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Planner
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistory

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Public material and task request; neither an actual world nor a successful plan is input. -/
structure Request where
  model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  budget : Nat
  installed : List (Prefix.Rule model.source.code)
  original : Prefix.Rule model.source.code
  reference : List (Prefix.Rule model.source.code)
  reader : Fin model.source.code.sites
  quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  encoding : StageTransport.Encoding (code := model.source.code)
  law : StageReception.Law model.source.code

variable {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def currentView (cursor : Cursor code) : View (code := code) :=
  ⟨cursor,⟨arrival cursor,by omega⟩⟩

def advanceViews : List (View (code := code)) → List (Prefix.Rule code) → List (View (code := code))
  | views, [] => views
  | views, rule :: tail => advanceViews (successors rule views) tail

def actualView : View (code := code) → List (EventHistory.Stage (code := code)) → View (code := code)
  | view, [] => view
  | view, (rule,rival) :: tail => actualView (Evidence.after view rule rival) tail

theorem every_actual_prefix_retains_its_complete_source_relation
    (views : List (View (code := code))) (actual : View (code := code))
    (covered : Knowledge.Contains views actual) (stages : List (EventHistory.Stage (code := code))) :
    Knowledge.Contains (advanceViews views (stages.map Prod.fst)) (actualView actual stages) := by
  induction stages generalizing views actual with
  | nil => exact covered
  | cons stage tail ih => exact ih _ _ (Knowledge.after _ _ covered stage.1 stage.2)

theorem actual_point (view : View (code := code)) (stages : List (EventHistory.Stage (code := code))) :
    (actualView view stages).point = EventHistory.execute view.point stages := by
  induction stages generalizing view with
  | nil => rfl
  | cons stage tail ih => exact ih _

theorem reset_preserves_complete_coverage
    (views : List (View (code := code))) (actual : View (code := code))
    (covered : Knowledge.Contains views actual) :
    Knowledge.Contains (views.map fun view => currentView view.point) (currentView actual.point) := by
  obtain ⟨representative,inside,matched⟩ := covered
  refine ⟨currentView representative.point,List.mem_map.mpr ⟨representative,inside,rfl⟩,matched.cursor,?_⟩
  change arrival representative.point = arrival actual.point
  change representative.point.history.length+2+representative.point.cut = actual.point.history.length+2+actual.point.cut
  rw [matched.cursor.history,matched.cursor.cut]

variable (request : Request (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def initial := (EventHistory.genesis request.model request.budget).map currentView

def views := (advanceViews (initial request) request.installed).map fun view => currentView view.point

def domain (signal : Fin request.model.source.code.signals) :=
  (fiber (views request) request.reader signal).map View.point

theorem every_origin_and_adaptive_prefix_is_covered
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    Knowledge.Contains (views request)
      (currentView (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages)) := by
  have member : currentView (EventHistory.ofOrigin request.model request.budget origin) ∈ initial request :=
    List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨origin,
      Distributed.Recall.Information.every_origin_is_generated request.model origin,rfl⟩,rfl⟩
  have kept := reset_preserves_complete_coverage _ _
    (every_actual_prefix_retains_its_complete_source_relation _ _ (Knowledge.member _ _ member) stages)
  rw [actual_point,installed] at kept
  exact kept

theorem every_actual_receipt_has_a_complete_local_source
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    let actual := currentView (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages)
    Knowledge.Contains (fiber (views request) request.reader (observation actual request.reader)) actual :=
  Prefix.Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain _ _
    (every_origin_and_adaptive_prefix_is_covered request origin stages installed) request.reader

inductive Plan (signal : Fin request.model.source.code.signals) where
  | absent (empty : fiber (views request) request.reader signal = [])
  | overBudget (long : horizon (domain request signal) < request.reference.length)
  | planned (fits : request.reference.length ≤ horizon (domain request signal))
      (outcome : Selection.Outcome request.model (domain request signal) request.original ⟨request.reference,fits⟩)

def plan (signal : Fin request.model.source.code.signals) : Plan request signal :=
  if empty : fiber (views request) request.reader signal = [] then .absent empty
  else if fits : request.reference.length ≤ horizon (domain request signal) then
    .planned fits (Prefix.Rolling.Receipt.defaultPlanner request.model _ _ ⟨request.reference,fits⟩)
  else .overBudget (Nat.lt_of_not_ge fits)

theorem the_original_selected_plan_accepts_itself {signal : Fin request.model.source.code.signals}
    {fits : request.reference.length ≤ horizon (domain request signal)}
    (choice : Selection.Choice request.model (domain request signal) request.original ⟨request.reference,fits⟩) :
    Selection.acceptable request.model (domain request signal) request.original choice.policy.protocol choice.policy.protocol := by
  apply (Selection.acceptable_iff_every_generated_cursor _ _ _ _ _).mpr
  intro world table
  have accepted := (Selection.acceptable_iff_every_generated_cursor _ _ _ _ _).mp choice.policy.accepted world table
  exact ⟨accepted.1,accepted.2.1,rfl,⟨List.Subperm.refl _,List.Subperm.refl _⟩,fun _ _ => le_refl _⟩

def task (signal : Fin request.model.source.code.signals)
    (fits : request.reference.length ≤ horizon (domain request signal))
    (choice : Selection.Choice request.model (domain request signal) request.original ⟨request.reference,fits⟩)
    (actual : View (code := request.model.source.code)) (rival : Opponent request.model.source.code) :
    Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  model := request.model
  domain := domain request signal
  original := request.original
  baseline := choice.policy.protocol
  point := actual
  rival := rival
  reader := request.reader
  quote := request.quote
  vocabulary := request.vocabulary
  encoding := request.encoding
  law := request.law
  continueUnreserved := true
  initialVerifier := .isTrue (the_original_selected_plan_accepts_itself request choice)

variable {request}

theorem initial_knowledge_is_generated_from_the_actual_receipt
    (signal : Fin request.model.source.code.signals)
    (fits : request.reference.length ≤ horizon (domain request signal))
    (choice : Selection.Choice request.model (domain request signal) request.original ⟨request.reference,fits⟩)
    (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code)
    (covered : Knowledge.Contains (fiber (views request) request.reader signal) (currentView point)) :
    Knowledge.Contains (Source.initialBeliefs (task request signal fits choice (currentView point) rival)) (currentView point) := by
  obtain ⟨representative,inside,matched⟩ := covered
  refine ⟨currentView representative.point,List.mem_map.mpr ⟨representative.point,
    List.mem_map.mpr ⟨representative,inside,rfl⟩,rfl⟩,matched.cursor,?_⟩
  change arrival representative.point = arrival point
  change representative.point.history.length+2+representative.point.cut = point.history.length+2+point.cut
  rw [matched.cursor.history,matched.cursor.cut]
  rfl

inductive Output (request : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
    (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code) (rounds : Nat) where
  | absent (empty : fiber (views request) request.reader (observation (currentView point) request.reader) = [])
  | overBudget (long : horizon (domain request (observation (currentView point) request.reader)) < request.reference.length)
  | blocked (fits : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)))
      (rejected : ∀ programme : Program request.model.source.code (horizon (domain request (observation (currentView point) request.reader))),
        Selection.Rejection request.model (domain request (observation (currentView point) request.reader)) request.original
          ⟨request.reference,fits⟩ programme)
  | deployed (fits : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)))
      (choice : Selection.Choice request.model (domain request (observation (currentView point) request.reader)) request.original ⟨request.reference,fits⟩)
      (made : Source.Occurrence (task request (observation (currentView point) request.reader) fits choice (currentView point) rival) rounds)

def generate (request : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
    (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code) (rounds : Nat) :
    Output request point rival rounds :=
  match plan request (observation (currentView point) request.reader) with
  | .absent empty => .absent empty
  | .overBudget long => .overBudget long
  | .planned fits (.blocked rejected) => .blocked fits rejected
  | .planned fits (.selected choice) => .deployed fits choice
      (Source.occurrence (task request _ fits choice (currentView point) rival) rounds)

theorem generated_execution_protects_the_original_request
    (signal : Fin request.model.source.code.signals)
    (fits : request.reference.length ≤ horizon (domain request signal))
    (choice : Selection.Choice request.model (domain request signal) request.original ⟨request.reference,fits⟩)
    (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code) (rounds : Nat) :
    match Source.response (task request signal fits choice (currentView point) rival) rounds with
    | .inl _ => False
    | .inr cache => Selection.acceptable request.model (domain request signal) request.original
        ⟨request.reference,fits⟩ cache.programme := by
  let input := task request signal fits choice (currentView point) rival
  have self := the_original_selected_plan_accepts_itself request choice
  unfold Source.response Source.generate
  cases seeded : Source.seed input with
  | rejected reason => exact False.elim (reason.broken (self reason.row reason.generated))
  | accepted cache empty programme beliefs =>
      exact Selection.acceptable_trans _ _ _ _ _ _ (Owned.trace input rounds cache).1.above choice.policy.accepted

theorem every_accepted_continuation_of_the_selected_plan_is_nondominated
    (signal : Fin request.model.source.code.signals)
    (fits : request.reference.length ≤ horizon (domain request signal))
    (choice : Selection.Choice request.model (domain request signal) request.original ⟨request.reference,fits⟩)
    (programme : Program request.model.source.code (horizon (domain request signal)))
    (kept : Selection.acceptable request.model (domain request signal) request.original choice.policy.protocol programme) :
    Selection.verify request.model (domain request signal) request.original ⟨request.reference,fits⟩ programme = true := by
  apply (Selection.verify_iff _ _ _ _ _).mpr
  refine ⟨Selection.acceptable_trans _ _ _ _ _ _ kept choice.policy.accepted,?_⟩
  intro other accepted better
  obtain ⟨candidate,inside,same⟩ := Selection.every_accepted_protocol_is_generated _ _ _ _ _ accepted
  have maximal := choice.maximal candidate inside
  change ¬ Distributed.Improves (Selection.axes (fuel := horizon (domain request signal)) request.model (domain request signal))
    (Selection.benefit request.model (domain request signal) request.original) choice.policy.protocol candidate.protocol at maximal
  rw [same] at maximal
  apply maximal
  have forward := Selection.acceptance_bounds_every_benefit _ _ _ _ _ kept
  refine ⟨fun axis member => (better.1 axis member).trans (forward axis member),?_⟩
  intro reverse
  exact better.2 (fun axis member => (forward axis member).trans (reverse axis member))

def RootConsumption
    (input : Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (rounds : Nat) (made : Source.Occurrence input rounds) : Prop :=
  Runtime.read input rounds made made.controls.length = some (Runtime.snapshot input rounds made) ∧
  ∀ count : Nat,
    let current := Runtime.activated input rounds made count
    Native.Coupling.Match input.model.source.code (Runtime.cutPoint input rounds made count).source.input
      (Runtime.source input rounds made).input
      (Financial.accountAt (Runtime.cutPoint input rounds made count).source.input (arrival (Runtime.cutPoint input rounds made count)))
      (Financial.accountAt (Runtime.source input rounds made).input (arrival (Runtime.cutPoint input rounds made count))) ∧
    HEq ((Runtime.facade input rounds made).readoutAt current .learning)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    (count < made.controls.length → current.tick.nextCurrent = (Runtime.activated input rounds made (count+1)).current)

theorem generated_root_consumes_its_original_complete_account
    (input : Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (rounds : Nat) (made : Source.Occurrence input rounds) : RootConsumption input rounds made :=
  ⟨Runtime.the_final_named_read_releases_its_source_generated_outcome input rounds made,
    fun count => (Runtime.the_same_root_consumes_each_actual_cut_full_account_and_literal_next input rounds made count).2⟩

def Output.Sound {point : Cursor request.model.source.code} {rival : Opponent request.model.source.code} {rounds : Nat} :
    Output request point rival rounds → Prop
  | .absent _ => False
  | .overBudget _ => True
  | .blocked fits _ => ∀ programme : Program request.model.source.code (horizon (domain request (observation (currentView point) request.reader))),
      ¬ Selection.acceptable request.model (domain request (observation (currentView point) request.reader)) request.original ⟨request.reference,fits⟩ programme
  | .deployed fits choice made =>
      let input := task request (observation (currentView point) request.reader) fits choice (currentView point) rival
      match made.response with
      | .inl _ => False
      | .inr cache =>
          Selection.verify request.model input.domain request.original ⟨request.reference,fits⟩ cache.programme = true ∧
          Knowledge.Contains cache.beliefs (cache.current input.point input.rival) ∧
          (cache.current input.point input.rival).point = Runtime.full input rounds made ∧
          RootConsumption input rounds made

theorem the_public_source_generates_an_originally_verified_actual_continuation
    (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code) (rounds : Nat)
    (covered : Knowledge.Contains (views request) (currentView point)) :
    (generate request point rival rounds).Sound := by
  have localCovered := Prefix.Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain _ _ covered request.reader
  unfold generate
  cases prepared : plan request (observation (currentView point) request.reader) with
  | absent empty =>
      obtain ⟨representative,inside,_⟩ := localCovered
      rw [empty] at inside
      exact List.not_mem_nil inside
  | overBudget => trivial
  | planned fits outcome =>
      cases outcome with
      | blocked rejected =>
          intro programme accepted
          exact (rejected programme).broken (accepted _ (rejected programme).generated)
      | selected choice =>
          let input := task request _ fits choice (currentView point) rival
          have initial := initial_knowledge_is_generated_from_the_actual_receipt _ fits choice point rival localCovered
          have known := Source.every_generated_feedback_chain_keeps_actual_public_knowledge input rounds initial
          have same := Source.the_generated_cache_current_is_the_same_actual_source input rounds
          have complete := generated_execution_protects_the_original_request _ fits choice point rival rounds
          change (match Source.response input rounds with
            | .inl _ => False
            | .inr cache => Selection.acceptable request.model input.domain request.original ⟨request.reference,fits⟩ cache.programme) at complete
          change match Source.response input rounds with
            | .inl _ => False
            | .inr cache => Selection.verify request.model input.domain request.original ⟨request.reference,fits⟩ cache.programme = true ∧
                Knowledge.Contains cache.beliefs (cache.current input.point input.rival) ∧
                (cache.current input.point input.rival).point = Runtime.full input rounds (Source.occurrence input rounds) ∧
                RootConsumption input rounds (Source.occurrence input rounds)
          cases result : Source.response input rounds with
          | inl rejection => simp only [result] at complete
          | inr cache =>
              rw [result] at known same
              exact ⟨every_accepted_continuation_of_the_selected_plan_is_nondominated _ fits choice cache.programme cache.above,known,
                same.trans (Runtime.the_generated_learning_and_root_share_one_actual_source input rounds (Source.occurrence input rounds)),
                generated_root_consumes_its_original_complete_account input rounds (Source.occurrence input rounds)⟩

theorem all_origins_and_finite_adaptive_histories_generate_the_full_local_contract
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed)
    (rival : Opponent request.model.source.code) (rounds : Nat) :
    (generate request (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages) rival rounds).Sound :=
  the_public_source_generates_an_originally_verified_actual_continuation _ _ _
    (every_origin_and_adaptive_prefix_is_covered request origin stages installed)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask

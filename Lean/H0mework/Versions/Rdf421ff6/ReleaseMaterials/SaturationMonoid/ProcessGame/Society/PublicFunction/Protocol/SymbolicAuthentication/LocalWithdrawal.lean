import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponseRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWithdrawal

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (installed : List (Rule model.source.code))

-- The advertised initial cursor is fixed before the query. Only installed rules,
-- never the actual external choices or a chosen representative, enter this domain.
def domain := EventHistory.history [start] installed
abbrev reading (cursor : Cursor model.source.code) (site : Fin model.source.code.sites) :=
  (EventStep.seed cursor).frame.inbox site
def fibre (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :=
  (domain model start installed).filter fun cursor => reading model cursor site == signal
abbrev request (cursor : Cursor model.source.code) (site : Fin model.source.code.sites) :=
  Mandate.request model.scope (EventStep.seed cursor).current (model.source.code.siteParty site) .revoke

theorem mem_fibre (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals)
    (cursor : Cursor model.source.code) :
    cursor ∈ fibre model start installed site signal ↔
      cursor ∈ domain model start installed ∧ reading model cursor site = signal := by simp [fibre]

private theorem generated_execution
    {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (rules : List (Rule code)) (seeds : List (Cursor code)) (cursor : Cursor code)
    (inside : cursor ∈ EventHistory.history seeds rules) :
    ∃ seed ∈ seeds, ∃ stages : List (EventHistory.Stage (code := code)),
      stages.map Prod.fst = rules ∧ EventHistory.execute seed stages = cursor := by
  induction rules generalizing seeds with
  | nil => exact ⟨cursor, inside, [], rfl, rfl⟩
  | cons rule rules ih =>
    obtain ⟨middle, generated, stages, selected, actual⟩ := ih (EventStep.advance rule seeds) inside
    obtain ⟨seed, original, mapped⟩ := List.mem_flatMap.mp generated
    obtain ⟨reply, _, same⟩ := List.mem_map.mp mapped
    subst middle
    exact ⟨seed, original, (rule, EventStep.fixed reply) :: stages, by simp [selected], actual⟩

theorem every_generated_cursor_is_an_actual_installed_execution
    (cursor : Cursor model.source.code) (inside : cursor ∈ domain model start installed) :
    ∃ stages : List (EventHistory.Stage (code := model.source.code)),
      stages.map Prod.fst = installed ∧ EventHistory.execute start stages = cursor := by
  obtain ⟨seed, original, stages, selected, actual⟩ := generated_execution installed [start] cursor inside
  have same := List.mem_singleton.mp original
  subst seed
  exact ⟨stages, selected, actual⟩

variable (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals)

inductive Query where
  | unseen (empty : fibre model start installed site signal = [])
  | ready (value : Request Party Good Port (Mandate.State Party Technology) Instrument) (first : Cursor model.source.code)
      (actual : first ∈ fibre model start installed site signal)
      (exact : request model first site = value)
      (uniform : ∀ other ∈ fibre model start installed site signal, request model other site = value)
  | ambiguous (first second : Cursor model.source.code)
      (left : first ∈ fibre model start installed site signal)
      (right : second ∈ fibre model start installed site signal)
      (different : request model second site ≠ request model first site)

def query : Query model start installed site signal :=
  match selected : fibre model start installed site signal with
  | [] => .unseen selected
  | first :: rest =>
    match inspect (fun other => request model other site = request model first site) rest with
    | .accepted uniform => .ready (request model first site) first
        (by rw [selected]; exact List.mem_cons_self) rfl (by
          intro other member
          rw [selected] at member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ rfl
          · exact uniform other later)
    | .rejected other member different => .ambiguous first other
        (by rw [selected]; exact List.mem_cons_self)
        (by rw [selected]; exact List.mem_cons_of_mem _ member) different

inductive Obstruction where
  | notMember | noCapacity | unsupportedActivation | sealed | unsupportedAction
  deriving DecidableEq

inductive Result where
  | unseen
  | ambiguous (first second : Cursor model.source.code)
  | blocked (reason : Obstruction)
  | ready (value : Request Party Good Port (Mandate.State Party Technology) Instrument)

def produce : Result model :=
  match query model start installed site signal with
  | .unseen _ => .unseen
  | .ambiguous first second .. => .ambiguous first second
  | .ready value .. =>
    if model.source.code.siteParty site ∉ Delegation.members model.scope.task then .blocked .notMember else
    if ¬ 1 ≤ model.source.code.actionLimit then .blocked .noCapacity else
    if Event.activate site ∉ model.source.code.eventAlphabet then .blocked .unsupportedActivation else
    if model.source.code.memoryReady signal ≠ true then .blocked .sealed else
    if value ∉ model.source.code.actions then .blocked .unsupportedAction else .ready value

def value? : Result model → Option (Request Party Good Port (Mandate.State Party Technology) Instrument)
  | .ready value => some value
  | _ => none

theorem ready_of_value (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : value? model (produce model start installed site signal) = some value) :
    produce model start installed site signal = .ready value := by
  cases selected : produce model start installed site signal <;> simp_all [value?]

def work := match produce model start installed site signal with
  | .ready value => [value]
  | _ => []

theorem ready_admission (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : produce model start installed site signal = .ready value) :
    1 ≤ model.source.code.actionLimit ∧ value ∈ model.source.code.actions ∧
      Event.activate site ∈ model.source.code.eventAlphabet ∧ model.source.code.memoryReady signal = true ∧
      model.source.code.siteParty site ∈ Delegation.members model.scope.task := by
  unfold produce at prepared
  cases selected : query model start installed site signal with
  | unseen empty => simp only [selected] at prepared; contradiction
  | ambiguous first second left right different => simp only [selected] at prepared; contradiction
  | ready candidate first actual precise uniform =>
    simp only [selected] at prepared
    split_ifs at prepared
    simp_all

theorem work_is_source_supported : work model start installed site signal ∈
    words model.source.code.actions model.source.code.actionLimit := by
  unfold work
  split
  · rename_i value selected
    have allowed := ready_admission model start installed site signal value selected
    exact (mem_words_iff _ _ _).mpr ⟨allowed.1, by
      intro item inside
      simpa only [List.mem_singleton.mp inside] using allowed.2.1⟩
  all_goals exact (mem_words_iff _ _ _).mpr (by simp)

theorem ready_has_its_actual_request (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : produce model start installed site signal = .ready value) :
    (∀ cursor ∈ fibre model start installed site signal, request model cursor site = value) ∧
      model.source.code.memoryReady signal = true ∧
      model.source.code.siteParty site ∈ Delegation.members model.scope.task := by
  unfold produce at prepared
  cases selected : query model start installed site signal with
  | unseen empty => simp only [selected] at prepared; contradiction
  | ambiguous first second left right different => simp only [selected] at prepared; contradiction
  | ready candidate first actual precise uniform =>
    simp only [selected] at prepared
    split_ifs at prepared
    cases prepared
    exact ⟨uniform, by simp_all, by simp_all⟩

def policy : model.source.code.Policy :=
  let table := Vector.ofFn (work model start installed site)
  fun key _ => if key.1 = site then table.get key.2 else []

theorem policy_at (record : Fin model.source.code.signals) :
    policy model start installed site (site, record) (model.source.code.key_mem _) =
      work model start installed site record := by
  simp only [policy, Vector.get, Vector.ofFn, if_pos rfl, Array.getElem_ofFn]
  apply congrArg (work model start installed site)
  exact Fin.ext rfl

theorem policy_generated : policy model start installed site ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key inside
  rcases key with ⟨worker, record⟩
  by_cases same : worker = site
  · subst worker
    rw [policy_at]
    exact work_is_source_supported model start installed site record
  · simp only [policy, if_neg same]
    exact (mem_words_iff _ _ _).mpr (by simp)

def activation (worker : Fin model.source.code.sites)
    (supported : Event.activate worker ∈ model.source.code.eventAlphabet) : LocalMove model.source.code worker :=
  ⟨some ⟨.activate worker, supported⟩, by
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact ⟨⟨.activate worker, supported⟩, List.mem_filter.mpr ⟨List.mem_attach _ _, by simp⟩, rfl⟩⟩

def protocol : Rule model.source.code where
  work := ⟨policy model start installed site, policy_generated model start installed site⟩
  events := fun key _ => if key.1 = site then
    if supported : Event.activate key.1 ∈ model.source.code.eventAlphabet then
      if work model start installed site key.2 = [] then ⟨none, List.mem_cons_self⟩
      else activation model key.1 supported
    else ⟨none, List.mem_cons_self⟩
    else ⟨none, List.mem_cons_self⟩

theorem equal_received_records_have_the_same_work_and_own_event
    (left right : Cursor model.source.code) (same : reading model left site = reading model right site) :
    work model start installed site (reading model left site) = work model start installed site (reading model right site) ∧
      localEvent model.source.code (protocol model start installed site) site (reading model left site) =
        localEvent model.source.code (protocol model start installed site) site (reading model right site) := by rw [same]; exact ⟨rfl, rfl⟩

theorem every_adaptive_actual_prefix_has_a_compatible_representative
    (past : List (EventHistory.Stage (code := model.source.code))) :
    ∃ representative ∈ fibre model start (past.map Prod.fst) site
        (reading model (EventHistory.execute start past) site),
      EventStep.Matches representative (EventHistory.execute start past) := by
  obtain ⟨representative, inside, same⟩ := EventHistory.every_finite_actual_trace_has_a_generated_raw_prefix
    [start] start start List.mem_cons_self (EventStep.matches_self _) past
  refine ⟨representative, (mem_fibre model start _ _ _ _).mpr ⟨inside, ?_⟩, same⟩
  exact congrArg (fun state : State model.source.code => state.frame.inbox site) same.state

theorem a_ready_query_recovers_the_actual_original_revoke
    (past : List (EventHistory.Stage (code := model.source.code))) (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : produce model start (past.map Prod.fst) site
      (reading model (EventHistory.execute start past) site) = .ready value) :
    value = NativeReview.action model start past site := by
  obtain ⟨representative, inside, same⟩ := every_adaptive_actual_prefix_has_a_compatible_representative model start site past
  have actual := (ready_has_its_actual_request model start _ _ _ value prepared).1 representative inside
  exact actual.symm.trans (congrArg (fun state : State model.source.code =>
    Mandate.request model.scope state.current (model.source.code.siteParty site) .revoke) same.state)

theorem the_prepared_local_request_is_actually_submitted
    (past : List (EventHistory.Stage (code := model.source.code)))
    (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : produce model start (past.map Prod.fst) site
      (reading model (EventHistory.execute start past) site) = .ready value)
    (live : 0 < (EventStep.seed (EventHistory.execute start past)).remaining)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code
      (EventHistory.execute start past).ownerStart (EventStep.seed (EventHistory.execute start past)).history.length = some site)
    (rival : Opponent model.source.code) :
    let row := StageTrace.material (EventHistory.execute start past)
      (protocol model start (past.map Prod.fst) site) rival
    StageTrace.activation row = some site ∧ row.submitted = [NativeReview.action model start past site] := by
  let cursor := EventHistory.execute start past
  let rule := protocol model start (past.map Prod.fst) site
  let row := StageTrace.material cursor rule rival
  change produce model start (past.map Prod.fst) site (reading model cursor site) = .ready value at prepared
  change 0 < (EventStep.seed cursor).remaining at live
  change Distributed.Recall.Information.Agency.ownerAt model.source.code cursor.ownerStart
    (EventStep.seed cursor).history.length = some site at owned
  have admitted := ready_admission model start _ _ _ value prepared
  have nonempty : work model start (past.map Prod.fst) site (reading model cursor site) = [value] := by
    simp only [work, prepared]
  have activation : StageTrace.activation row = some site := by
    simp [row, rule, StageTrace.activation, StageTrace.material, StageTrace.capture,
      Nat.ne_of_gt live, owned, localEvent, protocol, admitted.2.2.1, nonempty, LocalWithdrawal.activation]
  refine ⟨activation, ?_⟩
  have actual := StageTrace.an_owned_activation_submits_its_selected_work cursor rule rival site activation
  have requested := a_ready_query_recovers_the_actual_original_revoke model start site past value prepared
  exact actual.2.trans (by
    change model.source.code.action (policy model start (past.map Prod.fst) site) site (reading model cursor site) = _
    simp only [Code.action, admitted.2.2.2.1, if_pos, policy_at, nonempty, requested])

theorem an_ambiguity_retains_two_generated_indistinguishable_requests
    (first second : Cursor model.source.code)
    (result : produce model start installed site signal = .ambiguous first second) :
    first ∈ domain model start installed ∧ second ∈ domain model start installed ∧
      reading model first site = reading model second site ∧ request model second site ≠ request model first site := by
  unfold produce at result
  cases selected : query model start installed site signal with
  | unseen empty => simp only [selected] at result; contradiction
  | ready candidate witness actual precise uniform =>
    simp only [selected] at result
    split_ifs at result
  | ambiguous left right one two different =>
    simp only [selected] at result
    cases result
    have a := (mem_fibre model start installed site signal first).mp one
    have b := (mem_fibre model start installed site signal second).mp two
    exact ⟨a.1, b.1, a.2.trans b.2.symm, different⟩

theorem no_record_only_word_can_realize_both_requests
    (first second : Cursor model.source.code)
    (same : reading model first site = reading model second site)
    (different : request model second site ≠ request model first site)
    (table : Fin model.source.code.signals → Request Party Good Port (Mandate.State Party Technology) Instrument) :
    ¬ (table (reading model first site) = request model first site ∧
      table (reading model second site) = request model second site) := by
  rintro ⟨left, right⟩
  exact different (right.symm.trans ((congrArg table same).symm.trans left))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWithdrawal

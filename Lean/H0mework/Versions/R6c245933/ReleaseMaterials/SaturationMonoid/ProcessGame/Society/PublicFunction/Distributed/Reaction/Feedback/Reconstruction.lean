import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension.Source

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Reconstruction
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- A recorded control and choice retain cut boundaries, including explicit none. -/
structure Command (code : Code Party Good Port Technology Instrument) where
  policy : Option code.Policy
  move : Move code

variable (original : Code Party Good Port Technology Instrument)
  (law : RawLaw Party Good Port Technology Instrument)
  (initial : RawCurrent Party Good Technology Instrument) (task : PublicTaskSpec Party Good)

/-- Reuse the local architecture; the new interpreter pays its own effects. -/
abbrev code : Code Party Good Port Technology Instrument :=
  {original with law := law, initial := initial, bootstrap := [], task := task}

def recode (command : Command original) : Command (code original law initial task) :=
  ⟨command.policy, command.move⟩

variable {original law initial task}
variable (source : Machine Party Good Port Technology Instrument)

theorem emission_is_supported :
    ∀ event ∈ source.emissionEvents (source.code.historyCurrent source.history), event ∈ source.code.eventAlphabet := by
  unfold Machine.emissionEvents Machine.eventsFor
  cases chosen : source.policy? with
  | none => simp
  | some policy => exact (traceFrom_is_supported source.code policy _ _ _ _ _ _).2

/-- The first actual response is followed by every actual feedback cut. Its
source chooses the commands; a consumer cannot replace them with a happy trace. -/
def transcript (entry : Input source.code) (cut : Nat) : List (Command source.code) :=
  ((source.emissionEvents (source.code.historyCurrent source.history)).attach.map fun event =>
    ⟨source.policy?, some ⟨event.val,emission_is_supported source event.val event.property⟩⟩) ++
  (List.range cut).map fun index =>
    ⟨source.feedbackPolicy index, decision source.code entry (source.feedbackState entry index)⟩

theorem every_feedback_control_keeps_its_actual_cut (entry : Input source.code) (cut index : Nat)
    (inside : index < cut) :
    (transcript source entry cut)[(source.emissionEvents (source.code.historyCurrent source.history)).length + index]? =
      some ⟨source.feedbackPolicy index,decision source.code entry (source.feedbackState entry index)⟩ := by
  unfold transcript
  rw [List.getElem?_append_right (by simp only [List.length_map,List.length_attach];omega)]
  simp only [List.length_map,List.length_attach,Nat.add_sub_cancel_left,
    List.getElem?_map,List.getElem?_range inside,Option.map_some]

variable (target : Code Party Good Port Technology Instrument)

def next (state : State target) (command : Command target) : State target :=
  Residual.forced target command.policy command.move state

def submitted (state : State target) (command : Command target) :=
  word target command.policy ⟨fun _ _ _ => command.move,0⟩ state

/-- Failure reports the new interpreter's real obstacle, never an old law flag. -/
inductive Failure (state : State target) (command : Command target) where
  | refused (item : ExecutionItem Party Good Port Technology Instrument)
      (present : item ∈ target.law.rawItems state.current (submitted target state command))
      (invalid : ¬ target.law.Valid item.before item.request)
  | noPacket (policy : target.Policy) (address : Nat)
      (active : command.policy = some policy) (chosen : command.move.map Subtype.val = some (.deliver address))
      (missing : state.frame.sent[address]? = none)
  | notReady (policy : target.Policy) (site : Fin target.sites)
      (active : command.policy = some policy) (chosen : command.move.map Subtype.val = some (.activate site))
      (asleep : target.memoryReady (state.frame.inbox site) = false)
  | exhausted (stopped : state.remaining = 0)

def failure? (state : State target) (command : Command target) : Option (Failure target state command) :=
  if stopped : state.remaining = 0 then some (.exhausted stopped) else
  match Distributed.inspect (fun item : ExecutionItem Party Good Port Technology Instrument =>
      target.law.Valid item.before item.request) (target.law.rawItems state.current (submitted target state command)) with
  | .rejected item present invalid => some (.refused item present invalid)
  | .accepted _ =>
    match active : command.policy, chosen : command.move with
    | some policy, some event => match kind : event.val with
      | .deliver address => if missing : state.frame.sent[address]? = none then
          some (.noPacket policy address active (by simp only [chosen,Option.map_some,kind]) missing) else none
      | .activate site => if asleep : target.memoryReady (state.frame.inbox site) = false then
          some (.notReady policy site active (by simp only [chosen,Option.map_some,kind]) asleep) else none
      | _ => none
    | _, _ => none

inductive Run : State target → List (Command target) → Type where
  | done (state : State target) : Run state []
  | step (state : State target) (command : Command target) (later : List (Command target))
      (observed : Option (Failure target state command))
      (exact_observation : observed = failure? target state command)
      (rest : Run (next target state command) later) : Run state (command :: later)

def execute (state : State target) : (commands : List (Command target)) → Run target state commands
  | [] => .done state
  | command :: later => .step state command later (failure? target state command) rfl
      (execute (next target state command) later)

namespace Run
variable {target}
def state : {seed : State target} → {commands : List (Command target)} → Run target seed commands → State target
  | _, _, .done seed => seed
  | _, _, .step _ _ _ _ _ rest => rest.state

def words : {seed : State target} → {commands : List (Command target)} → Run target seed commands →
    List (RawEvent Party Good Port Technology Instrument)
  | _, _, .done _ => []
  | _, _, .step seed command _ _ _ rest => submitted target seed command :: rest.words

def blocked : {seed : State target} → {commands : List (Command target)} → Run target seed commands → Bool
  | _, _, .done _ => false
  | _, _, .step _ _ _ observed _ rest => observed.isSome || rest.blocked

omit [DecidableEq Port] [DecidableEq Technology] in
theorem current_is_the_actual_raw_fold {seed : State target} {commands : List (Command target)}
    (run : Run target seed commands) :
    run.state.current = run.words.foldl target.law.next seed.current := by
  induction run with
  | done => rfl
  | step seed command later observed exact_observation rest ih =>
      rw [state,words,List.foldl_cons,ih]
      rfl

omit [DecidableEq Port] [DecidableEq Technology] in
theorem complete_history_is_retained {seed : State target} {commands : List (Command target)}
    (run : Run target seed commands) : run.state.history = seed.history ++ run.words := by
  induction run with
  | done => exact (List.append_nil _).symm
  | step seed command later observed exact_observation rest ih =>
      rw [state,words,ih]
      change (seed.history ++ [submitted target seed command]) ++ rest.words = _
      simp only [List.append_assoc,List.singleton_append]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_cut_is_retained {seed : State target} {commands : List (Command target)}
    (run : Run target seed commands) : run.words.length = commands.length := by
  induction run with
  | done => rfl
  | step _ _ _ _ _ rest ih => simp only [words,List.length_cons,ih]
end Run

/-- Historical inputs are not re-authorized. These commands are new attempts
at the new actual cut, with a fresh frame and the preserved local architecture. -/
def seed (target : Code Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (budget : Nat) : State target :=
  ⟨current,[],[],target.start,budget⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Reconstruction

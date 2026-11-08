import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource

structure Node (net : Network) extends ActualRoundNetworkSource.Node net where
  omissions : List Nat

def initial (net : Network) : Node net := ⟨ActualRoundNetworkSource.initial net,[]⟩
def opportunity (net : Network) (node : Node net) : Bool :=
  match StageTrace.capture node.cursor (protocol net) (EventStep.fixed none) node.state with
  | .own _ (some event) => match event.val with | .send _ _ => true | _ => false
  | _ => false

-- A request is executed even beyond the completion envelope; it is never forced back to follow.
def withholding (net : Network) (node : Node net) (requested : Bool) : Bool := opportunity net node && requested
def rule (net : Network) (node : Node net) (requested : Bool) : Rule (code net) :=
  let old := protocol net
  ⟨old.work,fun key member => if withholding net node requested then ⟨none,List.mem_cons_self⟩ else old.events key member⟩
def material (net : Network) (node : Node net) (requested : Bool) (rival : Opponent (code net)) : StageTrace.Record (code := code net) :=
  let selectedRule := rule net node requested
  let call := StageTrace.capture node.cursor selectedRule rival node.state
  let selected : Input (code net) := ⟨fun _ _ _ => ControlExecution.admitted (code net) call,node.cursor.entry.budget⟩
  ⟨node.cursor,selectedRule,node.state,call,word (code net) (some selectedRule.work.val) selected node.state,
    Reaction.Feedback.advance (code net) (some selectedRule.work.val) selected node.state⟩
def step (net : Network) (node : Node net) (requested : Bool) (rival : Opponent (code net)) : Node net :=
  let selectedRule := rule net node requested
  let row := material net node requested rival
  ⟨⟨node.cursor.after selectedRule rival,row.after,node.stages ++ [(selectedRule,rival)],node.rows ++ [row]⟩,
    if withholding net node requested then node.omissions ++ [node.cursor.cut] else node.omissions⟩
abbrev Valid (net : Network) (node : Node net) := ActualRoundNetworkSource.Valid net node.toNode
abbrev Controller (net : Network) := Nat → Feedback.State (code net) → Bool

def actual (net : Network) (control : Controller net) (callbacks : Nat → Opponent (code net)) : Nat → Node net :=
  Nat.rec (initial net) fun _ node => step net node (control node.cursor.cut node.state) (callbacks node.cursor.cut)

theorem step_valid (net : Network) (node : Node net) (valid : Valid net node)
    (requested : Bool) (rival : Opponent (code net)) : Valid net (step net node requested rival) := by
  have row : material net node requested rival = StageTrace.material node.cursor (rule net node requested) rival := by
    unfold material
    rw [valid.2.1]
    rfl
  refine ⟨?_,?_,?_⟩
  · change node.cursor.after _ _ = EventHistory.execute (start net) (node.stages ++ [_])
    rw [OriginQueue.execute_append,← valid.1]
    rfl
  · change (material net node requested rival).after = _
    rw [row]
    exact (StageTrace.material_is_the_actual_step _ _ _).1
  · change node.rows ++ [_] = StageTrace.records (start net) (node.stages ++ [_])
    rw [OriginQueue.records_append,valid.2.2,← valid.1,row]
    rfl

theorem actual_valid (net : Network) (control : Controller net) (callbacks : Nat → Opponent (code net)) (n : Nat) :
    Valid net (actual net control callbacks n) := by
  induction n with
  | zero => exact ActualRoundNetworkSource.initial_valid net
  | succ n prior => exact step_valid net _ prior _ _

abbrev limit (net : Network) := min net.settings.allowance ((window net-4)/2)
abbrev spent (net : Network) (node : Node net) := node.omissions.length+InterferenceEnvelope.gap (start net) node.rows
def controls (net : Network) (node : Node net) : List Bool :=
  if opportunity net node && decide (spent net node < limit net) then [false,true] else [false]
def choices (net : Network) (node : Node net) : List (Move (code net)) :=
  if (Distributed.Recall.Information.Agency.ownerAt (code net) node.cursor.ownerStart node.state.history.length).isSome then [none]
  else match CompletionEnvelope.available (OriginQueue.baseline (start net)) node.state with
    | [] => [none]
    | head :: tail => if spent net node < limit net then none :: (head::tail).map some else (head::tail).map some
abbrev intake (net : Network) (node : Node net) := ActualRoundNetworkSource.intake net node.toNode

def Within (net : Network) (control : Controller net) (callbacks : Nat → Opponent (code net)) (count : Nat) : Prop :=
  ∀ n < count, let node := actual net control callbacks n
    control node.cursor.cut node.state ∈ controls net node ∧
    intake net node (callbacks node.cursor.cut) ∈ choices net node

def generate (net : Network) : Nat → List (Node net) :=
  Nat.rec [initial net] fun _ domain => domain.flatMap fun node =>
    (controls net node).flatMap fun request => (choices net node).map fun move => step net node request (EventStep.fixed move)

theorem generated_valid (net : Network) (n : Nat) (node : Node net) (member : node ∈ generate net n) : Valid net node := by
  induction n generalizing node with
  | zero => cases List.mem_singleton.mp member;exact ActualRoundNetworkSource.initial_valid net
  | succ n prior =>
    obtain ⟨before,inside,rest⟩ := List.mem_flatMap.mp member
    obtain ⟨request,_,rest⟩ := List.mem_flatMap.mp rest
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp rest
    exact step_valid net before (prior before inside) _ _

abbrev result (net : Network) (node : Node net) := ActualRoundNetworkSource.result net node.toNode
inductive Scan (net : Network) (subject : Subject net) (nodes : List (Node net)) where
  | complete (all : ∀ node ∈ nodes, result net node = .decided true subject)
  | counterexample (node : Node net) (member : node ∈ nodes)
      (failed : result net node ≠ .decided true subject)

-- Standard list folds avoid a partial runtime helper for the dependent result.
def scan (net : Network) (subject : Subject net) (nodes : List (Node net)) : Scan net subject nodes :=
  if all : nodes.all (fun node => decide (result net node = .decided true subject)) then
    .complete (by intro node member;simpa using List.all_eq_true.mp all node member)
  else match found : nodes.find? (fun node => !decide (result net node = .decided true subject)) with
    | some node => .counterexample node (List.mem_of_find?_eq_some found)
        (by have bad := List.find?_some found;simpa using bad)
    | none => False.elim (all (List.all_eq_true.mpr (by
        intro node member
        have good := List.find?_eq_none.mp found node member
        simpa using good)))

inductive Verdict (net : Network) where
  | unresolved (missing : expected net = none)
  | completed (subject : Subject net) (origin : expected net = some subject)
      (checked : ∀ node ∈ generate net (window net), result net node = .decided true subject)
  | obstructed (subject : Subject net) (origin : expected net = some subject)
      (node : Node net) (member : node ∈ generate net (window net))
      (failed : result net node ≠ .decided true subject)

def assess (net : Network) : Verdict net := match origin : expected net with
  | none => .unresolved origin
  | some subject => match scan net subject (generate net (window net)) with
    | .complete checked => .completed subject origin checked
    | .counterexample node member failed => .obstructed subject origin node member failed

def completion (net : Network) : Option (Subject net) := match assess net with
  | .completed subject _ _ => some subject
  | _ => none

def obstruction (net : Network) : Option (Node net) := match assess net with
  | .obstructed _ _ node _ _ => some node
  | _ => none

def produce (state : NetworkReentrySource.State) (production feed : Bool) (settings : Settings) :
    Option (Sigma Verdict) :=
  (NetworkReentrySource.inspect state production feed settings).map fun net => ⟨net,assess net⟩

structure Attempt where
  private mk ::
  network : Network
  control : Controller network
  callbacks : Nat → Opponent (code network)
  trace : Node network
  trace_exact : trace = actual network control callbacks (window network)
def execute (net : Network) (control : Controller net) (callbacks : Nat → Opponent (code net)) : Attempt :=
  ⟨net,control,callbacks,actual net control callbacks (window net),rfl⟩
abbrev model (attempt : Attempt) : MaterialRoundSource.Bound :=
  ⟨attempt.network.entry.bound.base,attempt.network.entry.bound.scope,attempt.trace.cursor.source,
    attempt.network.entry.bound.law_exact,attempt.network.entry.bound.task_exact⟩
abbrev ordinal (attempt : Attempt) := MaterialRoundSource.depth (model attempt) attempt.trace.cursor.cut-1
abbrev disposition (attempt : Attempt) := Native.Authority.fullGenerate (model attempt) (ordinal attempt)
def after (attempt : Attempt) : RoundEpisodeSource.State :=
  ⟨model attempt,attempt.trace.cursor.cut,attempt.network.state.archive ++
    RoundEpisodeSource.nativeArchive attempt.network.state (RoundEpisodeSource.normal attempt.network.state attempt.network.raw) ++
    [.native (model attempt) (ordinal attempt) (disposition attempt)]⟩

structure State where
  legacy : NetworkReentrySource.State
  evidence : List Attempt := []
abbrev Controls := (net : Network) → Controller net

def next (state : State) (production feed : Bool) (settings : Settings)
    (control : Controls) (callbacks : NetworkReentrySource.Callbacks) : State :=
  match NetworkReentrySource.inspect state.legacy production feed settings with
  | none => ⟨⟨RoundEpisodeSource.next (NetworkReentrySource.prepared state.legacy production feed)
      (RoundEpisodeSource.normal (NetworkReentrySource.prepared state.legacy production feed)
        (NetworkReentrySource.incoming state.legacy production feed)),state.legacy.evidence⟩,state.evidence⟩
  | some net => let attempt := execute net (control net) (callbacks net)
    ⟨⟨after attempt,state.legacy.evidence⟩,state.evidence ++ [attempt]⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlSource

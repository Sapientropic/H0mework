import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePaymentQuorum
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EnvelopeObservation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

structure Settings where
  allowance : Nat := 1
  maxDelay : Nat := 3
  threshold : Nat := 1

structure Network where
  private mk ::
  state : RoundEpisodeSource.State
  raw : List RecycledQuorumMaterial.Action
  entry : RoundEpisodeSource.Entry state raw
  settings : Settings

def inspect (state : RoundEpisodeSource.State) (raw : List RecycledQuorumMaterial.Action)
    (settings : Settings := {}) : Option Network :=
  (RoundEpisodeSource.inspect state raw).map fun entry => ⟨state,raw,entry,settings⟩

abbrev emitter (net : Network) := RoundEpisodeSource.emitter net.state net.raw net.entry
abbrev code (net : Network) := (emitter net).code
abbrev input (net : Network) := RoundEpisodeSource.input net.state net.raw net.entry
abbrev protocol (net : Network) : Rule (code net) := (RoundEpisodeSource.normal net.state net.raw).localRule net.entry
abbrev vocabulary (net : Network) := RoundEpisodeSource.vocabulary net.state net.raw net.entry
abbrev encoding (net : Network) : StageTransport.Encoding (code := code net) := RoundEpisodeSource.encoding net.state net.raw net.entry
abbrev scope (net : Network) := RoundEpisodeSource.slot net.state net.raw net.entry
abbrev window (net : Network) := (input net).budget
abbrev allowance (net : Network) := net.settings.allowance
abbrev reception (net : Network) : StageReception.Law (code net) := ⟨fun _ _ => scope net,net.settings.maxDelay⟩
def start (net : Network) : Cursor (code net) :=
  ⟨(emitter net).reference,(emitter net).reference_generated,(emitter net).history,(emitter net).original,
    (emitter net).opponent,(emitter net).side,(input net),[],0,Distributed.Recall.Information.Agency.start (emitter net) 0⟩

structure Node (net : Network) where
  cursor : Cursor (code net)
  state : Feedback.State (code net)
  stages : List (EventHistory.Stage (code := (code net)))
  rows : List (StageTrace.Record (code := (code net)))
def initial (net : Network) : (Node net) := ⟨(start net),EventStep.seed (start net),[],[]⟩

-- Cache the actual fold; the equality below ties it back to the native occurrence.
def material (net : Network) (node : (Node net)) (rival : Opponent (code net)) : StageTrace.Record (code := (code net)) :=
  let call := StageTrace.capture node.cursor (protocol net) rival node.state
  let selected : Input (code net) := ⟨fun _ _ _ => ControlExecution.admitted (code net) call,node.cursor.entry.budget⟩
  ⟨node.cursor,(protocol net),node.state,call,word (code net) (some (protocol net).work.val) selected node.state,
    Reaction.Feedback.advance (code net) (some (protocol net).work.val) selected node.state⟩
def step (net : Network) (node : (Node net)) (rival : Opponent (code net)) : (Node net) :=
  let row := (material net) node rival
  ⟨node.cursor.after (protocol net) rival,row.after,node.stages ++ [((protocol net),rival)],node.rows ++ [row]⟩
def Valid (net : Network) (node : (Node net)) : Prop :=
  node.cursor = EventHistory.execute (start net) node.stages ∧ node.state = EventStep.seed node.cursor ∧
    node.rows = StageTrace.records (start net) node.stages

theorem initial_valid (net : Network) : (Valid net) (initial net) := ⟨rfl,rfl,rfl⟩
theorem step_valid (net : Network) (node : (Node net)) (valid : (Valid net) node) (rival : Opponent (code net)) : (Valid net) ((step net) node rival) := by
  have material_eq : (material net) node rival = StageTrace.material node.cursor (protocol net) rival := by
    unfold material
    rw [valid.2.1]
    rfl
  refine ⟨?_,?_,?_⟩
  · change node.cursor.after _ _ = EventHistory.execute (start net) (node.stages ++ [_])
    rw [OriginQueue.execute_append,← valid.1]
    rfl
  · change ((material net) node rival).after = _
    rw [material_eq]
    exact (StageTrace.material_is_the_actual_step _ _ _).1
  · change node.rows ++ [_] = StageTrace.records (start net) (node.stages ++ [_])
    rw [OriginQueue.records_append,valid.2.2,← valid.1,material_eq]
    rfl

def actual (net : Network) (rivals : Nat → Opponent (code net)) : Nat → (Node net) :=
  Nat.rec (initial net) fun _ node => (step net) node (rivals node.cursor.cut)
theorem actual_valid (net : Network) (rivals : Nat → Opponent (code net)) (count : Nat) : (Valid net) ((actual net) rivals count) := by
  induction count with
  | zero => exact (initial_valid net)
  | succ count ih => exact (step_valid net) _ ih _

def choices (net : Network) (node : (Node net)) : List (Move (code net)) :=
  if (Distributed.Recall.Information.Agency.ownerAt (code net) node.cursor.ownerStart node.state.history.length).isSome then [none]
  else match CompletionEnvelope.available (OriginQueue.baseline (start net)) node.state with
    | [] => [none]
    | head :: tail => if InterferenceEnvelope.gap (start net) node.rows < (allowance net) then none :: (head::tail).map some
      else (head::tail).map some

abbrev intake (net : Network) (node : (Node net)) (rival : Opponent (code net)) := InterferenceEnvelope.intake node.cursor rival

theorem choices_are_the_original_source_envelope (net : Network) (node : (Node net)) (valid : (Valid net) node) :
    (choices net) node = InterferenceEnvelope.choices (start net) node.stages (allowance net) := by
  have noExtras : InterferenceEnvelope.extras (start net) node.stages = [] := by
    unfold InterferenceEnvelope.extras
    have zero : (code net).eventLimit = 0 := rfl
    rw [zero,if_neg (Nat.not_lt_zero _)]
  unfold choices InterferenceEnvelope.choices
  rw [noExtras,← valid.1]
  dsimp only
  unfold InterferenceEnvelope.fresh CompletionEnvelope.fresh
  rw [← valid.2.1,← valid.2.2]
  simp only [List.append_nil,List.map_nil]
  split
  · rfl
  · cases CompletionEnvelope.available (OriginQueue.baseline (start net)) node.state <;> simp

def Within (net : Network) (rivals : Nat → Opponent (code net)) (count : Nat) : Prop :=
  ∀ index < count, (intake net) ((actual net) rivals index) (rivals ((actual net) rivals index).cursor.cut) ∈ (choices net) ((actual net) rivals index)
def generate (net : Network) : Nat → List (Node net) :=
  Nat.rec [(initial net)] fun _ domain => domain.flatMap fun node =>
    ((choices net) node).map fun move => (step net) node (EventStep.fixed move)

theorem generated_valid (net : Network) (count : Nat) (node : (Node net)) (inside : node ∈ (generate net) count) : (Valid net) node := by
  induction count generalizing node with
  | zero => cases List.mem_singleton.mp inside;exact (initial_valid net)
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp inside
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp next
    exact (step_valid net) before (ih before member) _

abbrev cached (net : Network) (node : (Node net)) := SourceReceiptRows.run (vocabulary net) (encoding net) node.rows (reception net) 0 node.rows.length
abbrev subject (net : Network) (node : (Node net)) := StagePaymentQuorum.resolveRows (vocabulary net) node.rows (scope net)
abbrev result (net : Network) (node : (Node net)) := StagePaymentQuorum.produce (vocabulary net) (start net) (encoding net) (reception net) node.stages 0 (scope net) net.settings.threshold
abbrev Subject (net : Network) := StagePaymentQuorum.Subject (code := code net)
-- The subject comes from the first actual paid local action, not a requested outcome.
def expected (net : Network) : Option (Subject net) :=
  StagePaymentQuorum.resolveAt (vocabulary net) (material net (initial net) (EventStep.fixed none)) (scope net)

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
      (all : ∀ node ∈ generate net (window net), result net node = .decided true subject)
  | obstructed (subject : Subject net) (origin : expected net = some subject)
      (node : Node net) (member : node ∈ generate net (window net))
      (failed : result net node ≠ .decided true subject)

def assess (net : Network) : Verdict net :=
  match origin : expected net with
  | none => .unresolved origin
  | some subject => match scan net subject (generate net (window net)) with
    | .complete all => .completed subject origin all
    | .counterexample node member failed => .obstructed subject origin node member failed

-- Inspection and finite generation are inside the producer mouth.
def produce (state : RoundEpisodeSource.State) (raw : List RecycledQuorumMaterial.Action := [])
    (settings : Settings := {}) : Option (Sigma Verdict) :=
  (inspect state raw settings).map fun net => ⟨net,assess net⟩

inductive Status where
  | admissionRefused | unresolved | completed | obstructed
  deriving DecidableEq

def status (state : RoundEpisodeSource.State) (raw : List RecycledQuorumMaterial.Action := [])
    (settings : Settings := {}) : Status :=
  match produce state raw settings with
  | none => .admissionRefused
  | some ⟨_,.unresolved _⟩ => .unresolved
  | some ⟨_,.completed _ _ _⟩ => .completed
  | some ⟨_,.obstructed _ _ _ _ _⟩ => .obstructed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkSource

import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedRoundControls
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePaymentQuorum
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EnvelopeObservation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev emitter := FinancedRoundSource.emitter FinancedRoundControls.old FinancedRoundControls.oldCount FinancedRoundControls.entry
abbrev code := emitter.code
abbrev input := FinancedRoundSource.input FinancedRoundControls.old FinancedRoundControls.oldCount FinancedRoundControls.entry
abbrev protocol := FinancedRoundSource.protocol FinancedRoundControls.old FinancedRoundControls.oldCount FinancedRoundControls.entry
abbrev vocabulary := FinancedRoundSource.vocabulary FinancedRoundControls.old FinancedRoundControls.oldCount FinancedRoundControls.entry
abbrev encoding : StageTransport.Encoding (code := code) := FinancedRoundSource.encoding FinancedRoundControls.old FinancedRoundControls.oldCount FinancedRoundControls.entry
abbrev scope := FinancedRoundSource.slot FinancedRoundControls.old FinancedRoundControls.oldCount FinancedRoundControls.entry
abbrev window := input.budget
abbrev allowance := (window - 2*code.sites - 2)/2
abbrev reception : StageReception.Law code := ⟨fun _ _ => scope,2*allowance+1⟩
def start : Cursor code :=
  ⟨emitter.reference,emitter.reference_generated,emitter.history,emitter.original,
    emitter.opponent,emitter.side,input,[],0,Distributed.Recall.Information.Agency.start emitter 0⟩

structure Node where
  cursor : Cursor code
  state : Feedback.State code
  stages : List (EventHistory.Stage (code := code))
  rows : List (StageTrace.Record (code := code))
def initial : Node := ⟨start,EventStep.seed start,[],[]⟩

-- Cache the actual fold; the equality below ties it back to the native occurrence.
def material (node : Node) (rival : Opponent code) : StageTrace.Record (code := code) :=
  let call := StageTrace.capture node.cursor protocol rival node.state
  let selected : Input code := ⟨fun _ _ _ => ControlExecution.admitted code call,node.cursor.entry.budget⟩
  ⟨node.cursor,protocol,node.state,call,word code (some protocol.work.val) selected node.state,
    Reaction.Feedback.advance code (some protocol.work.val) selected node.state⟩
def step (node : Node) (rival : Opponent code) : Node :=
  let row := material node rival
  ⟨node.cursor.after protocol rival,row.after,node.stages ++ [(protocol,rival)],node.rows ++ [row]⟩
def Valid (node : Node) : Prop :=
  node.cursor = EventHistory.execute start node.stages ∧ node.state = EventStep.seed node.cursor ∧
    node.rows = StageTrace.records start node.stages

theorem initial_valid : Valid initial := ⟨rfl,rfl,rfl⟩
theorem step_valid (node : Node) (valid : Valid node) (rival : Opponent code) : Valid (step node rival) := by
  have cached : material node rival = StageTrace.material node.cursor protocol rival := by
    unfold material
    rw [valid.2.1]
    rfl
  refine ⟨?_,?_,?_⟩
  · change node.cursor.after _ _ = EventHistory.execute start (node.stages ++ [_])
    rw [OriginQueue.execute_append,← valid.1]
    rfl
  · change (material node rival).after = _
    rw [cached]
    exact (StageTrace.material_is_the_actual_step _ _ _).1
  · change node.rows ++ [_] = StageTrace.records start (node.stages ++ [_])
    rw [OriginQueue.records_append,valid.2.2,← valid.1,cached]
    rfl

def actual (rivals : Nat → Opponent code) : Nat → Node :=
  Nat.rec initial fun _ node => step node (rivals node.cursor.cut)
theorem actual_valid (rivals : Nat → Opponent code) (count : Nat) : Valid (actual rivals count) := by
  induction count with
  | zero => exact initial_valid
  | succ count ih => exact step_valid _ ih _

def choices (node : Node) : List (Move code) :=
  if (Distributed.Recall.Information.Agency.ownerAt code node.cursor.ownerStart node.state.history.length).isSome then [none]
  else match CompletionEnvelope.available (OriginQueue.baseline start) node.state with
    | [] => [none]
    | head :: tail => if InterferenceEnvelope.gap start node.rows < allowance then none :: (head::tail).map some
      else (head::tail).map some

abbrev intake (node : Node) (rival : Opponent code) := InterferenceEnvelope.intake node.cursor rival

theorem choices_are_the_original_source_envelope (node : Node) (valid : Valid node) :
    choices node = InterferenceEnvelope.choices start node.stages allowance := by
  have noExtras : InterferenceEnvelope.extras start node.stages = [] := by
    unfold InterferenceEnvelope.extras
    have zero : code.eventLimit = 0 := rfl
    rw [zero,if_neg (Nat.not_lt_zero _)]
  unfold choices InterferenceEnvelope.choices
  rw [noExtras,← valid.1]
  dsimp only
  unfold InterferenceEnvelope.fresh CompletionEnvelope.fresh
  rw [← valid.2.1,← valid.2.2]
  simp only [List.append_nil,List.map_nil]
  split
  · rfl
  · cases CompletionEnvelope.available (OriginQueue.baseline start) node.state <;> simp

def Within (rivals : Nat → Opponent code) (count : Nat) : Prop :=
  ∀ index < count, intake (actual rivals index) (rivals (actual rivals index).cursor.cut) ∈ choices (actual rivals index)
def generate : Nat → List Node :=
  Nat.rec [initial] fun _ domain => domain.flatMap fun node =>
    (choices node).map fun move => step node (EventStep.fixed move)

theorem generated_valid (count : Nat) (node : Node) (inside : node ∈ generate count) : Valid node := by
  induction count generalizing node with
  | zero => cases List.mem_singleton.mp inside;exact initial_valid
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp inside
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp next
    exact step_valid before (ih before member) _

abbrev cached (node : Node) := SourceReceiptRows.run vocabulary encoding node.rows reception 0 node.rows.length
abbrev subject (node : Node) := StagePaymentQuorum.resolveRows vocabulary node.rows scope
abbrev result (node : Node) := StagePaymentQuorum.produce vocabulary start encoding reception node.stages 0 scope 1
abbrev expected : StagePaymentQuorum.Subject (code := code) := FinancedRoundControls.subject

theorem the_window_and_funded_delivery_generate_the_timing_allowance :
    window = 6 ∧ allowance = 1 ∧ reception.maxDelay = 3 ∧
      StageBudget.ledger vocabulary start [] = [] := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkSource

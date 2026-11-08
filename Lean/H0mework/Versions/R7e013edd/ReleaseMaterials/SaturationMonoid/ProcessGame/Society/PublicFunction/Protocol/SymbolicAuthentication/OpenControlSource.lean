import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlledPaymentConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenControlSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FinancedNetworkSource (code start window)

abbrev Node := ControlledPaymentSource.Node
abbrev Valid := ControlledPaymentSource.Valid
abbrev initial := ControlledPaymentSource.initial
abbrev base := ControlledPaymentSource.base
abbrev owner := ControlledPaymentSource.owner
abbrev opportunity := ControlledPaymentSource.opportunity

def withhold (node : Node) (requested : Bool) : Bool :=
  opportunity node && requested

def protocol (node : Node) (requested : Bool) : Rule code :=
  ⟨base.work,fun key inside => if withhold node requested then ⟨none,List.mem_cons_self⟩ else base.events key inside⟩

def material (node : Node) (requested : Bool) (rival : Opponent code) : StageTrace.Record (code := code) :=
  let rule := protocol node requested
  let call := StageTrace.capture node.cursor rule rival node.state
  let selected : Input code := ⟨fun _ _ _ => ControlExecution.admitted code call,node.cursor.entry.budget⟩
  ⟨node.cursor,rule,node.state,call,word code (some rule.work.val) selected node.state,
    Reaction.Feedback.advance code (some rule.work.val) selected node.state⟩

def step (node : Node) (requested : Bool) (rival : Opponent code) : Node :=
  let rule := protocol node requested
  let row := material node requested rival
  ⟨⟨node.cursor.after rule rival,row.after,node.stages ++ [(rule,rival)],node.rows ++ [row]⟩,
    if withhold node requested then node.omissions ++ [(node.cursor.cut,(owner node).getD 0)] else node.omissions,
    node.attempts ++ [(node.cursor.cut,requested,withhold node requested)]⟩

theorem initial_valid : Valid initial := ⟨rfl,rfl,rfl⟩
theorem step_valid (node : Node) (valid : Valid node) (requested : Bool) (rival : Opponent code) : Valid (step node requested rival) := by
  have cached : material node requested rival = StageTrace.material node.cursor (protocol node requested) rival := by
    unfold material
    rw [valid.2.1]
    rfl
  refine ⟨?_,?_,?_⟩
  · change node.cursor.after _ _ = EventHistory.execute start (node.stages ++ [_])
    rw [OriginQueue.execute_append,← valid.1]
    rfl
  · change (material node requested rival).after = _
    rw [cached]
    exact (StageTrace.material_is_the_actual_step _ _ _).1
  · change node.rows ++ [_] = StageTrace.records start (node.stages ++ [_])
    rw [OriginQueue.records_append,valid.2.2,← valid.1,cached]
    rfl

abbrev Controller := Nat → Feedback.State code → Bool
def actual (control : Controller) (rivals : Nat → Opponent code) : Nat → Node :=
  Nat.rec initial fun _ node => step node (control node.cursor.cut node.state) (rivals node.cursor.cut)
theorem actual_valid (control : Controller) (rivals : Nat → Opponent code) (count : Nat) : Valid (actual control rivals count) := by
  induction count with
  | zero => exact initial_valid
  | succ count ih => exact step_valid _ ih _ _

theorem raw_control_requests_and_their_actual_admission_are_retained
    (control : Controller) (rivals : Nat → Opponent code) (count : Nat) :
    let node := actual control rivals count
    (actual control rivals (count+1)).attempts = node.attempts ++
      [(node.cursor.cut,control node.cursor.cut node.state,withhold node (control node.cursor.cut node.state))] := rfl

abbrev allowance (node : Node) := min ControlledPaymentSource.capacity ((node.state.remaining-1)/ControlledPaymentSource.rosterWidth)
def choices (node : Node) : List (Move code) :=
  if (owner node).isSome then [none] else match CompletionEnvelope.available (OriginQueue.baseline start) node.state with
    | [] => [none]
    | head :: tail => if InterferenceEnvelope.gap start node.rows < allowance node then none :: (head::tail).map some
      else (head::tail).map some
abbrev intake (node : Node) (rival : Opponent code) := InterferenceEnvelope.intake node.cursor rival

theorem choices_are_the_original_source_envelope (node : Node) (valid : Valid node) :
    choices node = InterferenceEnvelope.choices start node.stages (allowance node) := by
  have noExtras : InterferenceEnvelope.extras start node.stages = [] := by
    unfold InterferenceEnvelope.extras
    have zero : code.eventLimit = 0 := rfl
    rw [zero,if_neg (Nat.not_lt_zero _)]
  unfold choices owner InterferenceEnvelope.choices
  rw [noExtras,← valid.1]
  dsimp only
  unfold InterferenceEnvelope.fresh CompletionEnvelope.fresh
  rw [← valid.2.1,← valid.2.2]
  simp only [List.append_nil,List.map_nil]
  split
  · rfl
  · cases CompletionEnvelope.available (OriginQueue.baseline start) node.state <;> simp

def Within (control : Controller) (rivals : Nat → Opponent code) (count : Nat) : Prop :=
  ∀ index < count, intake (actual control rivals index) (rivals (actual control rivals index).cursor.cut) ∈ choices (actual control rivals index)
def controls (node : Node) : List Bool := if opportunity node then [false,true] else [false]
def generate : Nat → List Node :=
  Nat.rec [initial] fun _ domain => domain.flatMap fun node => (controls node).flatMap fun requested =>
    (choices node).map fun move => step node requested (EventStep.fixed move)
theorem generated_valid (count : Nat) (node : Node) (inside : node ∈ generate count) : Valid node := by
  induction count generalizing node with
  | zero => cases List.mem_singleton.mp inside;exact initial_valid
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp inside
    obtain ⟨requested,_,rest⟩ := List.mem_flatMap.mp next
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp rest
    exact step_valid before (ih before member) _ _

abbrev result := ControlledPaymentSource.result
abbrev originSubject := ControlledPaymentSource.originSubject
abbrev originRow := ControlledPaymentSource.originRow

def released (node : Node) : Bool := node.omissions.all fun entry => decide (entry.1 ≠ 2 ∧ entry.1 ≠ 4)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenControlSource

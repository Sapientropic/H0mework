import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandTransitConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EnvelopeObservation
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeStep

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReservedTransitSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open DemandScheduleConsumer (original quiet)

structure Node where
  cursor : Cursor code
  state : Feedback.State code
  stages : List (EventHistory.Stage (code := code))
  rows : List (StageTrace.Record (code := code))

abbrev start := RenewedQuorumConsumer.start
abbrev front := AdaptiveDeliveryTrace.stages RenewedQuorumConsumer.protocols RenewedQuorumConsumer.rivals 16 ++
  (DemandTransitSource.signed quiet).stages
def initial : Node :=
  ⟨DemandTransitSource.departure quiet,(DemandTransitSource.signed quiet).state,front,StageTrace.records start front⟩
def due (node : Node) : Nat :=
  ResidualFeeStep.localDue node.state.frame.inbox +
    (QueueScheduler.untried code (OriginQueue.baseline start) node.state.past).card

def needs (node : Node) : Bool :=
  decide (node.state.current.stock 1 .service < (due node : ℚ) ∧
    RenewedQuorumMaterial.Inputs node.state.current)

-- Remaining native local positions and admitted untried serials generate the reserve bill.
def protocol (node : Node) : Rule code :=
  let old := DemandTransitSource.compile quiet node.state
  ⟨old.work,fun key inside =>
    if key.1 = 2 then
      if needs node then RenewedQuorumSource.activation _ _ _ key.1 else ⟨none,List.mem_cons_self⟩
    else old.events key inside⟩
def step (node : Node) (external : Opponent code) : Node :=
  let rule := protocol node
  let row := DemandSchedulePolicy.materialAt node.cursor rule external node.state
  ⟨node.cursor.after rule external,row.after,node.stages ++ [(rule,external)],node.rows ++ [row]⟩

def Valid (node : Node) : Prop :=
  node.cursor = EventHistory.execute start node.stages ∧ node.state = EventStep.seed node.cursor ∧
    node.rows = StageTrace.records start node.stages

theorem initial_is_the_original_prefix : Valid initial :=
  ⟨by change DemandTransitSource.departure quiet = EventHistory.execute start front
      rw [StageQueue.execute_append,AdaptiveDeliveryTrace.execute_stages],
    DemandTransitSource.sourceState quiet,rfl⟩

theorem the_initial_occurrence_has_unconverted_original_fuel :
    initial.cursor.cut = 21 ∧ initial.state.current.stock 1 .service = 1 ∧
      initial.state.current.stock 0 .feedstock = 1 ∧ initial.state.frame.sent.length = 2 := by
  decide +kernel

theorem every_actual_step_preserves_its_source (node : Node) (valid : Valid node) (external : Opponent code) :
    Valid (step node external) := by
  obtain ⟨cursor,state,rows⟩ := valid
  refine ⟨?_,DemandSchedulePolicy.cached_after_is_the_same_source_successor _ _ _ _ state,?_⟩
  · change node.cursor.after _ _ = EventHistory.execute start (node.stages ++ [_])
    rw [OriginQueue.execute_append]
    exact congrArg (fun current : Cursor code => current.after (protocol node) external) cursor
  · change node.rows ++ [_] = StageTrace.records start (node.stages ++ [_])
    rw [OriginQueue.records_append,rows,← cursor]
    exact congrArg (StageTrace.records start node.stages ++ ·)
      (congrArg List.singleton (DemandSchedulePolicy.cached_material_is_the_actual_occurrence _ _ _ _ state))

def actual (external : Nat → Opponent code) : Nat → Node :=
  Nat.rec initial fun _ node => step node (external node.cursor.cut)

theorem actual_is_source_generated (external : Nat → Opponent code) (count : Nat) : Valid (actual external count) := by
  induction count with
  | zero => exact initial_is_the_original_prefix
  | succ count ih => exact every_actual_step_preserves_its_source _ ih _

-- Patience is an explicit communication condition; extra charged events retain the original zero quota.
abbrev allowance : Nat := 2
def envelope (node : Node) : List (Move code) :=
  if (Distributed.Recall.Information.Agency.ownerAt code node.cursor.ownerStart node.state.history.length).isSome then [none]
  else match CompletionEnvelope.available (OriginQueue.baseline start) node.state with
    | [] => [none]
    | head :: tail =>
      if InterferenceEnvelope.gap start node.rows < allowance then none :: ((head :: tail).map some)
      else (head :: tail).map some

theorem envelope_is_the_original_source_envelope (node : Node) (valid : Valid node) :
    envelope node = InterferenceEnvelope.choices start node.stages allowance := by
  obtain ⟨cursor,state,rows⟩ := valid
  have extras : InterferenceEnvelope.extras start node.stages = [] := by
    simp [InterferenceEnvelope.extras,RenewedQuorumSource.code]
  unfold envelope InterferenceEnvelope.choices
  dsimp only
  rw [← cursor,← rows,extras]
  unfold InterferenceEnvelope.fresh CompletionEnvelope.fresh
  rw [← state]
  split_ifs
  all_goals cases CompletionEnvelope.available (OriginQueue.baseline start) node.state <;> simp

-- Funding is an output of the local reserve policy, not part of this communication domain.
abbrev choices := envelope

def intake (node : Node) (external : Opponent code) : Move code :=
  CompletionEnvelope.intake node.cursor external
def Within (external : Nat → Opponent code) (count : Nat) : Prop :=
  ∀ index < count, intake (actual external index) (external (actual external index).cursor.cut) ∈
    choices (actual external index)

def generate : Nat → List Node :=
  Nat.rec [initial] fun _ domain => domain.flatMap fun node =>
    (choices node).map fun move => step node (EventStep.fixed move)

theorem every_generated_node_keeps_the_original_source (count : Nat) (node : Node)
    (member : node ∈ generate count) : Valid node := by
  induction count generalizing node with
  | zero => cases List.mem_singleton.mp member; exact initial_is_the_original_prefix
  | succ count ih =>
    obtain ⟨before,inside,next⟩ := List.mem_flatMap.mp member
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp next
    exact every_actual_step_preserves_its_source before (ih before inside) _

abbrev window := initial.state.remaining
abbrev deliveryBound :=
  2 * ((QueueScheduler.untried code (OriginQueue.baseline start) initial.state.past).card * (allowance + 1)) - 1

theorem the_actual_source_generates_the_reserve_bill_and_delivery_bound :
    due initial = 4 ∧ needs initial = true ∧ deliveryBound = 11 := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReservedTransitSource

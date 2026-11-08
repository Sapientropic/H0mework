import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReservedTransitDomain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)

abbrev start := ReservedTransitSource.start
abbrev front := AdaptiveDeliveryTrace.stages RenewedQuorumConsumer.protocols RenewedQuorumConsumer.rivals 16
abbrev rosterWidth := 2 * code.sites
abbrev completionWidth := rosterWidth + code.sites + ReservedTransitSource.deliveryBound

structure Node extends ReservedTransitSource.Node where
  omissions : List (Nat × Fin code.sites)

def initial : Node :=
  ⟨⟨DemandScheduleConsumer.original,
    AdaptiveDeliveryTrace.state start RenewedQuorumConsumer.protocols RenewedQuorumConsumer.rivals 16,
    front,StageTrace.records start front⟩,[]⟩
abbrev window := initial.state.remaining
abbrev controlCapacity := (window - completionWidth) / rosterWidth
abbrev vocabulary := RenewedQuorumSource.vocabulary

def ballots (node : Node) := node.rows.flatMap (StageTransport.ballots vocabulary)
def encoding (node : Node) : StageTransport.Encoding (code := code) := fun signal =>
  (ballots node).find? fun body => decide (body.scope = RenewedQuorumSource.slot true ∧
    ((signal = 2 ∧ body.key = 0) ∨ (signal = 3 ∧ body.key = 1)))

def base (node : Node) : Rule code :=
  ⟨⟨DemandSchedulePolicy.work true,DemandSchedulePolicy.work_generated true⟩,fun key _ =>
    if key.1 = 2 then
      if ReservedTransitSource.needs node.toNode then RenewedQuorumSource.activation _ _ _ key.1
      else ⟨none,List.mem_cons_self⟩
    else if key.2 = 2 ∧ 1 ≤ node.state.current.stock 1 .service then
      RenewedQuorumSource.activation _ _ _ key.1
    else if key.2 = 3 ∧ (encoding node key.2).isSome ∧
        (ReservedTransitSource.due node.toNode : ℚ) ≤ node.state.current.stock 1 .service then
      RenewedQuorumSource.sending _ _ _ key.1 else ⟨none,List.mem_cons_self⟩⟩

def owner (node : Node) :=
  Distributed.Recall.Information.Agency.ownerAt code node.cursor.ownerStart node.state.history.length

def opportunity (node : Node) : Bool :=
  if node.state.remaining = 0 then false else match owner node with
    | none => false
    | some site => (localEvent code (base node) site (node.state.frame.inbox site)).isSome

def withhold (node : Node) (requested : Bool) : Bool :=
  opportunity node && decide (node.omissions.length < controlCapacity) && requested

-- One actual owned opportunity may withhold signing, supply or sending. Empty/unfunded turns
-- do not consume its clock-derived capacity; an unpaid signature is never preinstalled.
def protocol (node : Node) (requested : Bool) : Rule code :=
  let old := base node
  ⟨old.work,fun key inside =>
    if withhold node requested then ⟨none,List.mem_cons_self⟩ else old.events key inside⟩

def step (node : Node) (requested : Bool) (external : Opponent code) : Node :=
  let rule := protocol node requested
  let row := DemandSchedulePolicy.materialAt node.cursor rule external node.state
  ⟨⟨node.cursor.after rule external,row.after,node.stages ++ [(rule,external)],node.rows ++ [row]⟩,
    if withhold node requested then node.omissions ++ [(node.cursor.cut,(owner node).getD 0)] else node.omissions⟩

abbrev Controller := Nat → Feedback.State code → Bool

def actual (control : Controller) (external : Nat → Opponent code) : Nat → Node :=
  Nat.rec initial fun _ node => step node (control node.cursor.cut node.state) (external node.cursor.cut)

abbrev Valid (node : Node) := ReservedTransitSource.Valid node.toNode

theorem initial_is_the_original_source : Valid initial :=
  ⟨(AdaptiveDeliveryTrace.execute_stages start RenewedQuorumConsumer.protocols RenewedQuorumConsumer.rivals 16).symm,rfl,rfl⟩

theorem every_actual_step_preserves_source (node : Node) (valid : Valid node)
    (requested : Bool) (external : Opponent code) : Valid (step node requested external) := by
  obtain ⟨cursor,state,rows⟩ := valid
  refine ⟨?_,DemandSchedulePolicy.cached_after_is_the_same_source_successor _ _ _ _ state,?_⟩
  · change node.cursor.after _ _ = EventHistory.execute start (node.stages ++ [_])
    rw [OriginQueue.execute_append]
    exact congrArg (fun current : Cursor code => current.after (protocol node requested) external) cursor
  · change node.rows ++ [_] = StageTrace.records start (node.stages ++ [_])
    rw [OriginQueue.records_append,rows,← cursor]
    exact congrArg (StageTrace.records start node.stages ++ ·)
      (congrArg List.singleton (DemandSchedulePolicy.cached_material_is_the_actual_occurrence _ _ _ _ state))

theorem every_actual_cut_is_source_generated (control : Controller) (external : Nat → Opponent code) (count : Nat) :
    Valid (actual control external count) := by
  induction count with
  | zero => exact initial_is_the_original_source
  | succ count ih => exact every_actual_step_preserves_source _ ih _ _

theorem every_actual_control_is_within_the_original_clock_capacity
    (control : Controller) (external : Nat → Opponent code) (count : Nat) :
    (actual control external count).omissions.length ≤ controlCapacity := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    change (if withhold _ _ then _ ++ [_] else _).length ≤ _
    split
    · rename_i withheld
      have room : (actual control external count).omissions.length < controlCapacity := by
        simp only [withhold,Bool.and_eq_true_iff,decide_eq_true_eq] at withheld
        exact withheld.1.2
      simp only [List.length_append,List.length_singleton]
      change (actual control external count).omissions.length + 1 ≤ controlCapacity
      omega
    · exact ih

abbrev choices (node : Node) := ReservedTransitSource.choices node.toNode
abbrev intake (node : Node) := ReservedTransitSource.intake node.toNode

def Within (control : Controller) (external : Nat → Opponent code) (count : Nat) : Prop :=
  ∀ index < count, intake (actual control external index) (external (actual control external index).cursor.cut) ∈
    choices (actual control external index)

def controls (node : Node) : List Bool := if opportunity node && decide (node.omissions.length < controlCapacity)
  then [false,true] else [false]

def generate : Nat → List Node :=
  Nat.rec [initial] fun _ domain => domain.flatMap fun node =>
    (controls node).flatMap fun requested =>
      (choices node).map fun move => step node requested (EventStep.fixed move)

theorem every_generated_node_is_source_generated (count : Nat) (node : Node) (inside : node ∈ generate count) :
    Valid node := by
  induction count generalizing node with
  | zero => cases List.mem_singleton.mp inside;exact initial_is_the_original_source
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp inside
    obtain ⟨requested,_,rest⟩ := List.mem_flatMap.mp next
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp rest
    exact every_actual_step_preserves_source before (ih before member) requested _

theorem source_clock_generates_the_owned_withholding_budget :
    window = 32 ∧ rosterWidth = 6 ∧ completionWidth = 20 ∧ controlCapacity = 2 := by decide +kernel

theorem initial_occurrence_has_unconverted_fuel_and_no_new_paid_signature :
    initial.cursor.cut = 16 ∧ initial.state.current.stock 1 .service = 0 ∧
      initial.state.current.stock 0 .feedstock = 2 ∧
      ((ballots initial).filter fun body => decide (body.scope = RenewedQuorumSource.slot true)) = [] := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumSource

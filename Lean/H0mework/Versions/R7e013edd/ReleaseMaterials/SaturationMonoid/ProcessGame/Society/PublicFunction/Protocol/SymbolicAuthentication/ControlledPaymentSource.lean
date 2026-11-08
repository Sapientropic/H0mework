import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlledPaymentSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FinancedNetworkSource (code start window)

abbrev rosterWidth := 2*code.sites
abbrev completionWidth := rosterWidth+2
abbrev capacity := (window-completionWidth)/rosterWidth

structure Node extends FinancedNetworkSource.Node where
  omissions : List (Nat × Fin code.sites)
  attempts : List (Nat × Bool × Bool)
def initial : Node := ⟨FinancedNetworkSource.initial,[],[]⟩
abbrev Valid (node : Node) := FinancedNetworkSource.Valid node.toNode
abbrev base := FinancedNetworkSource.protocol
abbrev owner (node : Node) := Distributed.Recall.Information.Agency.ownerAt code node.cursor.ownerStart node.state.history.length
def opportunity (node : Node) : Bool :=
  if node.state.remaining = 0 then false else match owner node with
    | none => false
    | some site => (localEvent code base site (node.state.frame.inbox site)).isSome
def withhold (node : Node) (requested : Bool) : Bool :=
  opportunity node && decide (node.omissions.length < capacity) && requested

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

theorem actual_omissions_spend_only_the_source_clock_capacity
    (control : Controller) (rivals : Nat → Opponent code) (count : Nat) :
    (actual control rivals count).omissions.length ≤ capacity := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    change (if withhold _ _ then _ ++ [_] else _).length ≤ _
    split
    · rename_i held
      have room : (actual control rivals count).omissions.length < capacity := by
        simp only [withhold,Bool.and_eq_true_iff,decide_eq_true_eq] at held
        exact held.1.2
      simp only [List.length_append,List.length_singleton]
      change (actual control rivals count).omissions.length+1 ≤ capacity
      omega
    · exact ih

theorem raw_control_requests_and_their_actual_admission_are_retained
    (control : Controller) (rivals : Nat → Opponent code) (count : Nat) :
    let node := actual control rivals count
    (actual control rivals (count+1)).attempts = node.attempts ++
      [(node.cursor.cut,control node.cursor.cut node.state,withhold node (control node.cursor.cut node.state))] := rfl

abbrev allowance (node : Node) := capacity-node.omissions.length
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
def controls (node : Node) : List Bool := if opportunity node && decide (node.omissions.length < capacity) then [false,true] else [false]
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

abbrev Payment := Settlement.Statement (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Instrument := Unit)
abbrev paymentAt (row : StageTrace.Record (code := code)) := Settlement.issuedAt code.law row.before.current row.submitted 0

def originRow (node : Node) := node.rows.find? fun row => (paymentAt row).isSome
def scope (node : Node) : Option Scope := (originRow node).bind fun row => (paymentAt row).map (·.scope)
def vocabulary (name : Scope) : OwnedAttestation.Vocabulary (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => if port = .reserve 1 then some (name,true) else none,fun current => current.round,.service⟩
def originSubject (node : Node) : Option (StagePaymentQuorum.Subject (code := code)) :=
  (originRow node).bind fun row => (paymentAt row).bind fun payment =>
    StagePaymentQuorum.resolveAt (vocabulary payment.scope) row payment.scope

def ballots (node : Node) (name : Scope) := node.rows.flatMap (StageTransport.ballots (vocabulary name))
def encoding (node : Node) (name : Scope) : StageTransport.Encoding (code := code) := fun signal =>
  if signal = 1 then (ballots node name).find? fun body => decide (body.scope = name ∧ body.key = 0) else none
abbrev reception (name : Scope) : StageReception.Law code := ⟨fun _ _ => name,window-rosterWidth-1⟩

def result (node : Node) : StagePaymentQuorum.Result (code := code) :=
  match scope node,originSubject node with
  | some name,some original => match StagePaymentQuorum.produce (vocabulary name) start (encoding node name) (reception name) node.stages 0 name 1 with
    | .blocked reason => .blocked reason
    | .decided value subject => if subject = original then .decided value subject else .blocked .missingSourceSubject
  | _,_ => .blocked .missingSourceSubject

theorem the_original_clock_generates_the_joint_control_capacity :
    window = 6 ∧ completionWidth = 4 ∧ rosterWidth = 2 ∧ capacity = 1 ∧ allowance initial = 1 ∧
      scope initial = none ∧ originSubject initial = none := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlledPaymentSource

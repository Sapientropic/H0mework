import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedLocalDomain
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceEnvelope

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EnvelopeObservation
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Raw callbacks keep their own sources; this relation preserves admitted effects and envelope clocks.
def external (row : StageTrace.Record (code := code)) : Bool := match row.call with
  | .external _ => true
  | _ => false

structure Same (left right : StageTrace.Record (code := code)) : Prop extends CommunicationObservation.Same left right where
  protocol : left.protocol = right.protocol
  external : external left = external right

abbrev Related := List.Forall₂ (Same (code := code))

theorem communication {left right : List (StageTrace.Record (code := code))} (same : Related left right) :
    CommunicationObservation.Related left right := same.imp (fun _ _ item => item.toSame)

theorem reflexive (rows : List (StageTrace.Record (code := code))) : Related rows rows := by
  induction rows with
  | nil => exact .nil
  | cons row tail ih => exact .cons ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩ ih

variable (start : Cursor code)

private theorem progress_shape (row : StageTrace.Record (code := code)) :
    InterferenceEnvelope.progresses start row =
      if external row then match StageTransport.admission row with
        | some event => decide (event ∈ InterferenceEnvelope.available (OriginQueue.baseline start) row.before)
        | none => false
      else false := by
  cases called : row.call <;>
    simp [InterferenceEnvelope.progresses,external,StageTransport.admission,called,ControlExecution.admitted]
  all_goals rfl

 theorem progress_equal {left right : StageTrace.Record (code := code)} (same : Same left right) :
    InterferenceEnvelope.progresses start left = InterferenceEnvelope.progresses start right := by
  rw [progress_shape,progress_shape,same.external,same.admission,same.before]

private theorem interference_shape (row : StageTrace.Record (code := code)) :
    InterferenceEnvelope.interference start row =
      if external row then (StageTransport.admission row).isSome && !(InterferenceEnvelope.progresses start row) else false := by
  cases called : row.call <;>
    simp [InterferenceEnvelope.interference,external,StageTransport.admission,called,ControlExecution.admitted]

 theorem interference_equal {left right : StageTrace.Record (code := code)} (same : Same left right) :
    InterferenceEnvelope.interference start left = InterferenceEnvelope.interference start right := by
  rw [interference_shape,interference_shape,same.external,same.admission,progress_equal start same]

 theorem gap_equal {left right : List (StageTrace.Record (code := code))} (same : Related left right) :
    InterferenceEnvelope.gap start left = InterferenceEnvelope.gap start right := by
  have step (a b : StageTrace.Record (code := code)) (item : Same a b) (count : Nat) :
      (match a.call with | .external _ => if (InterferenceEnvelope.available (OriginQueue.baseline start) a.before).isEmpty ||
        InterferenceEnvelope.progresses start a then 0 else count + 1 | _ => count) =
      (match b.call with | .external _ => if (InterferenceEnvelope.available (OriginQueue.baseline start) b.before).isEmpty ||
        InterferenceEnvelope.progresses start b then 0 else count + 1 | _ => count) := by
    have shape (row : StageTrace.Record (code := code)) :
        (match row.call with | .external _ => if (InterferenceEnvelope.available (OriginQueue.baseline start) row.before).isEmpty ||
          InterferenceEnvelope.progresses start row then 0 else count + 1 | _ => count) =
        if external row then if (InterferenceEnvelope.available (OriginQueue.baseline start) row.before).isEmpty ||
          InterferenceEnvelope.progresses start row then 0 else count + 1 else count := by cases called : row.call <;> simp [external,called]
    rw [shape,shape,item.external,item.before,progress_equal start item]
  let stepFn : Nat → StageTrace.Record (code := code) → Nat := fun count row =>
    match row.call with
    | .external _ => if (InterferenceEnvelope.available (OriginQueue.baseline start) row.before).isEmpty ||
        InterferenceEnvelope.progresses start row then 0 else count + 1
    | _ => count
  change left.foldl stepFn 0 = right.foldl stepFn 0
  have fold : ∀ count : Nat, left.foldl stepFn count = right.foldl stepFn count := by
    induction same with
    | nil => intro count;rfl
    | @cons a b left right item rest ih =>
      intro count
      simp only [List.foldl_cons]
      have current : stepFn count a = stepFn count b := step a b item count
      rw [current]
      exact ih _
  exact fold 0

 theorem spent_equal (first second : List (EventHistory.Stage (code := code)))
    (same : Related (StageTrace.records start first) (StageTrace.records start second)) :
    InterferenceEnvelope.spent start first = InterferenceEnvelope.spent start second := by
  have lengths {left right : List (StageTrace.Record (code := code))} (related : Related left right) :
      (left.filter (InterferenceEnvelope.interference start)).length =
        (right.filter (InterferenceEnvelope.interference start)).length := by
    induction related with
    | nil => rfl
    | @cons a b left right item rest ih =>
      simp only [List.filter_cons,interference_equal start item]
      split <;> simp only [List.length_cons,ih]
  exact lengths same

abbrev Compatible (first second : List (EventHistory.Stage (code := code))) :=
  EventStep.Matches (EventHistory.execute start first) (EventHistory.execute start second) ∧
    Related (StageTrace.records start first) (StageTrace.records start second)

 theorem choices_equal (first second : List (EventHistory.Stage (code := code)))
    (same : Compatible start first second) (allowance : Nat) :
    InterferenceEnvelope.choices start first allowance = InterferenceEnvelope.choices start second allowance := by
  have fresh : InterferenceEnvelope.fresh start (EventHistory.execute start first) =
      InterferenceEnvelope.fresh start (EventHistory.execute start second) := by
    unfold InterferenceEnvelope.fresh CompletionEnvelope.fresh
    rw [same.1.state]
  simp only [InterferenceEnvelope.choices,same.1.ownerStart,same.1.state,fresh,gap_equal start same.2,
    InterferenceEnvelope.extras,spent_equal start first second same.2]
  cases InterferenceEnvelope.fresh start (EventHistory.execute start second) <;> rfl

 theorem compact_extension (first second : List (EventHistory.Stage (code := code)))
    (same : Compatible start first second) (rule : Rule code) (rival : Opponent code) :
    Compatible start
      (first ++ [(rule,EventStep.fixed (CausalLocalDomain.chosen (EventHistory.execute start first) (EventHistory.execute start second) rival))])
      (second ++ [(rule,rival)]) := by
  have old : ReceivedLocalDomain.Compatible start first second := ⟨same.1,communication same.2⟩
  have next := ReceivedLocalDomain.compact_extension start first second old rule rival
  refine ⟨next.1,?_⟩
  rw [StageQueue.records_append,StageQueue.records_append]
  apply List.rel_append same.2
  refine .cons ⟨ReceivedLocalDomain.compact_row _ _ same.1 rule rival,rfl,?_⟩ .nil
  by_cases stopped : (EventStep.seed (EventHistory.execute start second)).remaining = 0
  · simp only [external,StageTrace.material,StageTrace.capture,same.1.state,if_pos stopped]
  · cases own : Distributed.Recall.Information.Agency.ownerAt code (EventHistory.execute start second).ownerStart
        (EventStep.seed (EventHistory.execute start second)).history.length <;>
      simp only [external,StageTrace.material,StageTrace.capture,same.1.state,same.1.ownerStart,if_neg stopped,own]


 theorem chosen_is_the_actual_intake (first second : List (EventHistory.Stage (code := code)))
    (same : Compatible start first second) (rival : Opponent code) :
    CausalLocalDomain.chosen (EventHistory.execute start first) (EventHistory.execute start second) rival =
      InterferenceEnvelope.intake (EventHistory.execute start second) rival := by
  simp only [CausalLocalDomain.chosen,same.1.state,same.1.ownerStart,
    CompletionEnvelope.intake,CompletionEnvelope.raw]
  split <;> rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EnvelopeObservation

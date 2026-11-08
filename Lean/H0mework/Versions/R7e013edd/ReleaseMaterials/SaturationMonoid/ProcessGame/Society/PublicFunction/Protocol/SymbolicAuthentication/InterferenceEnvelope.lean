import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceEnvelope

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev available := @CompletionEnvelope.available
abbrev fresh := @CompletionEnvelope.fresh
abbrev Input (code : Code Party Good Port (Mandate.State Party Technology) Instrument) := CompletionEnvelope.Input code
abbrev raw := @CompletionEnvelope.raw
abbrev intake := @CompletionEnvelope.intake

def externalEvents : List (Choice code) := code.eventAlphabet.attach.filter fun event => match event.val with
  | .deliver _ | .adversary _ => true
  | _ => false

def progresses (start : Cursor code) (row : StageTrace.Record (code := code)) : Bool :=
  match row.call with
  | .external move => match Distributed.Recall.Information.Agency.externalChoice code move with
    | some event => decide (event ∈ available (OriginQueue.baseline start) row.before)
    | none => false
  | _ => false

-- Repeating an old delivery does not reset the fresh-delivery clock.
def gap (start : Cursor code) (rows : List (StageTrace.Record (code := code))) : Nat :=
  rows.foldl (fun count row => match row.call with
    | .external _ => if (available (OriginQueue.baseline start) row.before).isEmpty || progresses start row then 0 else count + 1
    | _ => count) 0

def interference (start : Cursor code) (row : StageTrace.Record (code := code)) : Bool :=
  match row.call with
  | .external move => (Distributed.Recall.Information.Agency.externalChoice code move).isSome && !(progresses start row)
  | _ => false

def spent (start : Cursor code) (past : List (EventHistory.Stage (code := code))) : Nat :=
  ((StageTrace.records start past).filter (interference start)).length

def extras (start : Cursor code) (past : List (EventHistory.Stage (code := code))) : List (Choice code) :=
  if spent start past < code.eventLimit then
    externalEvents.filter fun event => decide (event ∉ fresh start (EventHistory.execute start past))
  else []

def choices (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat) : List (Move code) :=
  let current := EventHistory.execute start past
  if (Distributed.Recall.Information.Agency.ownerAt code current.ownerStart (EventStep.seed current).history.length).isSome then [none]
  else match fresh start current with
    | [] => none :: (extras start past).map some
    | head :: tail =>
      if gap start (StageTrace.records start past) < allowance then
        none :: ((head :: tail) ++ extras start past).map some
      else (head :: tail).map some

theorem the_generated_domain_is_nonempty
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat) :
    choices start past allowance ≠ [] := by
  dsimp only [choices]
  split_ifs
  all_goals cases fresh start (EventHistory.execute start past) <;> simp

theorem every_extra_event_has_source_admission_and_unspent_interface_capacity
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (event : Choice code)
    (member : event ∈ extras start past) :
    event.val ∈ code.eventAlphabet ∧ spent start past < code.eventLimit ∧
    event ∉ fresh start (EventHistory.execute start past) ∧
    (match event.val with | .deliver _ | .adversary _ => True | _ => False) := by
  unfold extras at member
  split at member <;> try contradiction
  rename_i capacity
  have selected := (List.mem_filter.mp member).1
  have absent := of_decide_eq_true (List.mem_filter.mp member).2
  refine ⟨event.property, capacity, absent, ?_⟩
  have kind := (List.mem_filter.mp selected).2
  rcases event with ⟨event, supported⟩
  cases event <;> simp_all

theorem a_nonfresh_generated_choice_needs_unspent_source_capacity
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat)
    (event : Choice code) (chosen : some event ∈ choices start past allowance)
    (notFresh : event ∉ fresh start (EventHistory.execute start past)) :
    spent start past < code.eventLimit := by
  by_cases owner : (Distributed.Recall.Information.Agency.ownerAt code
      (EventHistory.execute start past).ownerStart (EventStep.seed (EventHistory.execute start past)).history.length).isSome = true
  · simp [choices, owner] at chosen
  · cases pending : fresh start (EventHistory.execute start past) with
    | nil =>
      have extra : event ∈ extras start past := by simpa [choices, owner, pending] using chosen
      exact (every_extra_event_has_source_admission_and_unspent_interface_capacity start past event extra).2.1
    | cons head tail =>
      by_cases room : gap start (StageTrace.records start past) < allowance
      · have generated : event ∈ fresh start (EventHistory.execute start past) ++ extras start past := by
          simpa [choices, owner, pending, room] using chosen
        rcases List.mem_append.mp generated with fresh | extra
        · exact False.elim (notFresh fresh)
        · exact (every_extra_event_has_source_admission_and_unspent_interface_capacity start past event extra).2.1
      · have member : event ∈ fresh start (EventHistory.execute start past) := by
          simpa [choices, owner, pending, room] using chosen
        exact False.elim (notFresh member)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem external_intake_is_idempotent (move : Move code) :
    Distributed.Recall.Information.Agency.externalChoice code
      (Distributed.Recall.Information.Agency.externalChoice code move) =
        Distributed.Recall.Information.Agency.externalChoice code move := by
  cases move with
  | none => rfl
  | some event => rcases event with ⟨event, supported⟩; cases event <;> rfl

theorem every_actual_charged_step_needs_unspent_source_capacity
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat)
    (protocol : Rule code) (move : Move code)
    (normalized : Distributed.Recall.Information.Agency.externalChoice code move = move)
    (chosen : move ∈ choices start past allowance)
    (charged : interference start (StageTrace.material (EventHistory.execute start past) protocol (EventStep.fixed move)) = true) :
    spent start past < code.eventLimit := by
  unfold interference at charged
  split at charged <;> try contradiction
  rename_i attempted called
  have external := StageTrace.external_callback_is_retained_before_admission _ protocol (EventStep.fixed move) attempted called
  have same : attempted = move := by simpa only [EventStep.fixed] using external.2.2.symm
  subst attempted
  rw [normalized] at charged
  cases move with
  | none => contradiction
  | some event =>
    have captured : StageTrace.capture (EventHistory.execute start past) protocol (EventStep.fixed (some event))
        (EventStep.seed (EventHistory.execute start past)) = .external (some event) := called
    have absent : event ∉ fresh start (EventHistory.execute start past) := by
      have bad : (!decide (event ∈ fresh start (EventHistory.execute start past))) = true := by
        simpa only [Option.isSome_some, Bool.true_and, progresses, StageTrace.material, captured, normalized,
          fresh, CompletionEnvelope.fresh, available] using charged
      intro present
      have yes : decide (event ∈ fresh start (EventHistory.execute start past)) = true := decide_eq_true present
      simp only [yes, Bool.not_true, Bool.false_eq_true] at bad
    exact a_nonfresh_generated_choice_needs_unspent_source_capacity start past allowance event chosen absent

theorem a_supported_actual_step_preserves_the_source_interface_bound
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat)
    (protocol : Rule code) (move : Move code)
    (normalized : Distributed.Recall.Information.Agency.externalChoice code move = move)
    (chosen : move ∈ choices start past allowance) :
    spent start (past ++ [(protocol, EventStep.fixed move)]) ≤ max code.eventLimit (spent start past) := by
  have counts : spent start (past ++ [(protocol, EventStep.fixed move)]) = spent start past +
      if interference start (StageTrace.material (EventHistory.execute start past) protocol (EventStep.fixed move)) then 1 else 0 := by
    simp only [spent, StageQueue.records_append, StageTrace.records, List.filter_append, List.length_append]
    split <;> simp_all
  rw [counts]
  split
  · have capacity := every_actual_charged_step_needs_unspent_source_capacity start past allowance protocol move normalized chosen (by assumption)
    omega
  · omega

def observe (start : Cursor code) (past : List (EventHistory.Stage (code := code)))
    (allowance : Nat) (rival : Opponent code) : Input code :=
  let current := EventHistory.execute start past
  ⟨current.cut, raw current rival, intake current rival,
    decide (intake current rival ∈ choices start past allowance)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceEnvelope

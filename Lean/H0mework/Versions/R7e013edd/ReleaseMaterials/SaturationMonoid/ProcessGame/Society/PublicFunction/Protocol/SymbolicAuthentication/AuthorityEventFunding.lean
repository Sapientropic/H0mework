import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceSignatureInterface

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AuthorityEventFunding
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Inspect the actual accepted revision target, rather than a future Resources value.
def permits (law : RawLaw Party Good Port (Mandate.State Party Technology) Instrument)
    (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument) : Bool :=
  match item.request.operation with
  | .revise _ target => !(decide (law.Valid item.before item.request)) || target.holder.isSome || target.offered.isSome
  | _ => true

omit [DecidableEq Port] [DecidableEq Technology] in
theorem accepted_effects_preserve_actual_authority
    (law : RawLaw Party Good Port (Mandate.State Party Technology) Instrument)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (request : Request Party Good Port (Mandate.State Party Technology) Instrument) (index : Nat)
    (active : IncidentResponse.activeAt current) (checked : permits law ⟨index, current, request⟩ = true) :
    IncidentResponse.activeAt (law.step current request) := by
  by_cases paid : law.Valid current request
  · rw [RawLaw.step, if_pos paid]
    cases operation : request.operation with
    | revise actor target =>
      simp only [permits, operation, decide_eq_true paid, Bool.not_true, Bool.false_or, Bool.or_eq_true] at checked
      simpa only [IncidentResponse.activeAt, RawLaw.paidStep, operation] using checked
    | _ => simpa only [IncidentResponse.activeAt, RawLaw.paidStep, operation] using active
  · rw [law.rejected_preserves_current _ _ paid]
    exact active

def wordCheck (law : RawLaw Party Good Port (Mandate.State Party Technology) Instrument)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) : Bool :=
  (law.rawItems current word).all (permits law)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem actual_raw_items_generate_authority_after_the_word
    (law : RawLaw Party Good Port (Mandate.State Party Technology) Instrument)
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (index : Nat)
    (active : IncidentResponse.activeAt current)
    (checked : ((law.execute current index word).items).all (permits law) = true) :
    IncidentResponse.activeAt (law.execute current index word).final := by
  induction word generalizing current index with
  | nil => exact active
  | cons request tail ih =>
    simp only [RawLaw.execute, List.all_cons, Bool.and_eq_true] at checked
    exact ih (law.step current request) (index + 1)
      (accepted_effects_preserve_actual_authority law current request index active checked.1) checked.2

def stageCheck (cursor : Cursor code) (stage : EventHistory.Stage (code := code)) : Bool :=
  wordCheck code.law (EventStep.seed cursor).current (StageTrace.material cursor stage.1 stage.2).submitted

theorem the_actual_stage_effect_preserves_authority
    (cursor : Cursor code) (stage : EventHistory.Stage (code := code))
    (active : IncidentResponse.activeAt (EventStep.seed cursor).current)
    (checked : stageCheck cursor stage = true) :
    IncidentResponse.activeAt (EventStep.seed (cursor.after stage.1 stage.2)).current := by
  have actual := (StageTrace.material_is_the_actual_step cursor stage.1 stage.2).2
  have paid := actual_raw_items_generate_authority_after_the_word code.law
    (StageTrace.material cursor stage.1 stage.2).submitted (EventStep.seed cursor).current 0 active checked
  rw [EventStep.actual_next_state]
  change IncidentResponse.activeAt (code.law.next (EventStep.seed cursor).current _)
  rw [← actual]
  exact paid

-- A cut observes the state before its row. The final row may legitimately revoke.
def inspect (cursor : Cursor code) : List (EventHistory.Stage (code := code)) → Bool
  | [] => true
  | [_] => true
  | stage :: next :: tail => stageCheck cursor stage && inspect (cursor.after stage.1 stage.2) (next :: tail)

theorem actual_effects_generate_authority_at_every_required_physical_cut
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (active : IncidentResponse.activeAt (EventStep.seed cursor).current)
    (checked : inspect cursor stages = true) (n : Nat) (inside : n < stages.length) :
    IncidentResponse.activeAt (EventStep.seed (EventHistory.execute cursor (stages.take n))).current := by
  induction stages generalizing cursor n with
  | nil => simp only [List.length_nil] at inside; omega
  | cons stage tail ih =>
    cases n with
    | zero => exact active
    | succ n =>
      cases tail with
      | nil => simp only [List.length_cons, List.length_nil] at inside; omega
      | cons next rest =>
        have gates := Bool.and_eq_true_iff.mp checked
        exact ih (cursor.after stage.1 stage.2)
          (the_actual_stage_effect_preserves_authority cursor stage active gates.1) gates.2 n
          (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AuthorityEventFunding

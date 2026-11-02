import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver)

/-- The support is generated from the actual paid frame, rather than the machine's stale feedback seed. -/
def controls := sequences (Feedback.Residual.controlMenu cursor.source.val) cursor.state.remaining
abbrev Term := {term // term ∈ controls cursor}
def terms : List (Term cursor) := (controls cursor).attach
abbrev schedule (term : Term cursor) := Feedback.Residual.scheduleAt cursor.source.val cursor.feedbackIndex term.val
def programs := (controls cursor).map (Feedback.Residual.scheduleAt cursor.source.val cursor.feedbackIndex)

theorem schedule_is_generated (term : Term cursor) : schedule cursor term ∈ programs cursor :=
  List.mem_map.mpr ⟨term.val,term.property,rfl⟩

def baseline : Term cursor := ⟨[],(mem_sequences_iff _ _ _).mpr ⟨Nat.zero_le _,by simp⟩⟩
abbrev Table := Feedback.Residual.Table cursor.source.val.code cursor.state (programs cursor)
def tables := Feedback.Residual.tables cursor.source.val.code cursor.state (programs cursor)
abbrev opponent (table : Table cursor) := Feedback.Residual.respond cursor.source.val.code cursor.state (programs cursor) table
abbrev restrict (rival : Opponent cursor.source.val.code) :=
  Feedback.Residual.restrict cursor.source.val.code cursor.state (programs cursor) rival

theorem restriction_is_generated (rival : Opponent cursor.source.val.code) : restrict cursor rival ∈ tables cursor :=
  Feedback.Residual.restriction_is_generated _ _ _ rival

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem words_are_the_history_suffix
    (code : Code Party Good Port Technology Instrument) (control : Feedback.Residual.Schedule code)
    (input : Feedback.Input code) (state : Feedback.State code) (n : Nat) :
    forecastWords code control input state n =
      (Feedback.Residual.run code control input state n).history.drop state.history.length := by
  rw [forecast_is_the_generated_history_suffix,List.drop_append_of_le_length (Nat.le_refl _),List.drop_length,List.nil_append]

theorem one_joint_table_preserves_every_forecast_word
    (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat)
    (bounded : n ≤ cursor.state.remaining) :
    forecastWords cursor.source.val.code (schedule cursor term)
      ⟨opponent cursor (restrict cursor rival),cursor.input.budget⟩ cursor.state n =
    forecastWords cursor.source.val.code (schedule cursor term) ⟨rival,cursor.input.budget⟩ cursor.state n := by
  have same := Feedback.Residual.one_restriction_preserves_the_whole_remaining_run
    cursor.source.val.code cursor.state (programs cursor) (schedule cursor term)
    (schedule_is_generated cursor term) ⟨rival,cursor.input.budget⟩ n bounded
  rw [words_are_the_history_suffix,words_are_the_history_suffix,same]

theorem one_joint_table_preserves_the_entire_actual_source
    (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat)
    (bounded : n ≤ cursor.state.remaining) :
    cursor.forecast (schedule cursor term) (opponent cursor (restrict cursor rival)) n =
      cursor.forecast (schedule cursor term) rival n :=
  congrArg cursor.install (one_joint_table_preserves_every_forecast_word cursor term rival n bounded)

theorem all_future_opponents_have_a_generated_joint_source_table :
    ∀ rival : Opponent cursor.source.val.code, ∃ table ∈ tables cursor,
      ∀ term : Term cursor, ∀ n ≤ cursor.state.remaining,
        cursor.forecast (schedule cursor term) (opponent cursor table) n =
          cursor.forecast (schedule cursor term) rival n := by
  intro rival
  exact ⟨restrict cursor rival,restriction_is_generated cursor rival,
    fun term n bounded => one_joint_table_preserves_the_entire_actual_source cursor term rival n bounded⟩

abbrev target (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :
    Future.Recovery.SameCodeTarget cursor.model :=
  ⟨cursor.forecast (schedule cursor term) rival n,rfl⟩
abbrev candidate (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :
    Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) :=
  ⟨seed.base,seed.scope,(target cursor term rival n).val,cursor.source.property.1,cursor.source.property.2⟩

def present (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :=
  Window.evaluate (candidate cursor term rival n) cursor.depth n

abbrev wordTarget (words : List (List (Future.Recovery.Action cursor.model))) : Future.Recovery.SameCodeTarget cursor.model :=
  ⟨cursor.install words,rfl⟩

/-- Recovery and its invoice failures are generated by the original paid kernel. -/
def restorationWords (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (words : List (List (Future.Recovery.Action cursor.model))) (n : Nat)
    (word : List (Future.Recovery.Action cursor.model)) :
    Option (Future.Recovery.Assessment.Report cursor.model ×
      Option (Future.Recovery.Funding.Failure cursor.model cursor.depth word)) :=
  match Future.produce cursor.model cursor.depth (wordTarget cursor words).indexed (cursor.count+n) word with
  | .inl _ => none
  | .inr receipt =>
    let made := Future.Recovery.produceWith pricing receipt
    some (Future.Recovery.Assessment.reportFrom made cursor.depth rfl,Future.Recovery.Funding.ofWalk made.walk)

def restoration (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (term : Term cursor) (rival : Opponent cursor.source.val.code) (n : Nat) :=
  restorationWords cursor pricing
    (forecastWords cursor.source.val.code (schedule cursor term) ⟨rival,cursor.input.budget⟩ cursor.state n) n

def execute (term : Term cursor) (n : Nat) : Cursor seed driver := cursor.realize (schedule cursor term) n

theorem execution_is_the_evaluated_actual_source (term : Term cursor) (n : Nat) :
    (execute cursor term n).source.val = (candidate cursor term cursor.input.opponent n).source := rfl

theorem complete_evaluation_is_jointly_covered (term : Term cursor)
    (rival : Opponent cursor.source.val.code) (n : Nat) (bounded : n ≤ cursor.state.remaining) :
    present cursor term (opponent cursor (restrict cursor rival)) n = present cursor term rival n := by
  exact congrArg (fun words => (show Distributed.Recall.Information.Agency.Protocol.Evaluation cursor.source.val.code from
    Window.evaluate ⟨seed.base,seed.scope,cursor.install words,cursor.source.property.1,cursor.source.property.2⟩ cursor.depth n))
      (one_joint_table_preserves_every_forecast_word cursor term rival n bounded)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning

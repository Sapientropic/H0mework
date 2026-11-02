import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Schedule

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}

namespace Progress
variable (state : Paid.State model domain original baseline actualHorizon)

def padded : Paid.State model domain original baseline actualHorizon :=
  {state with
    programme := Commitment.padded original state.programme
    retained := Padding.preserves_prefix original state.programme state.past state.retained
    above := Commitment.padded_acceptance model domain original baseline state.programme state.above}

def Live : Prop := state.past.length < actualHorizon ∧ state.past.length < horizon domain
instance : Decidable (Live state) := by unfold Live;infer_instance

abbrev rule := state.programme.at original state.past.length

/-- Execute the already accepted next stage. Padding only materializes the
existing implicit final rule; it does not search for a replacement plan. -/
def take (live : Live state) : Paid.State model domain original baseline actualHorizon :=
  {padded state with
    past := state.past ++ [rule state]
    beliefs := Window.Observed.Transcript.publicViews [rule state] state.beliefs
    within := by
      have room := live.2
      simp only [List.length_append,List.length_singleton];omega
    actualWithin := by
      have room := live.1
      simp only [List.length_append,List.length_singleton];omega
    retained := by
      simpa only [padded,rule,List.length_append,List.length_singleton] using
        Commitment.next_prefix original state.programme state.past state.retained live.2}

def next := if live : Live state then take state live else state
def rules := if Live state then [rule state] else []

theorem the_next_cached_stage_is_paid_into_the_actual_past :
    (next state).past = state.past ++ rules state := by
  unfold next rules
  split
  · rfl
  · exact (List.append_nil _).symm

theorem an_existing_live_slot_is_really_consumed (live : Live state) :
    (next state).past.length = state.past.length+1 := by
  simp only [next,dif_pos live,take,List.length_append,List.length_singleton]

theorem no_actual_slot_is_rolled_back : state.past.length ≤ (next state).past.length := by
  by_cases live : Live state
  · rw [an_existing_live_slot_is_really_consumed state live]
    omega
  · simp only [next,dif_neg live];exact Nat.le_refl _

theorem actual_local_knowledge_survives_the_cached_stage
    (point : View (code := model.source.code)) (rival : Opponent model.source.code)
    (covered : Knowledge.Contains state.beliefs (state.current point rival)) :
    Knowledge.Contains (next state).beliefs ((next state).current point rival) := by
  unfold next
  split
  · rename_i live
    have after := Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
      [rule state] state.beliefs (state.current point rival) covered rival
    change Knowledge.Contains _ (Window.Observed.Transcript.actualView (state.past ++ [rule state]) point rival)
    unfold Window.Observed.Transcript.actualView at *
    rw [List.foldl_append]
    exact after
  · exact covered

theorem consumed_rules_are_source_native :
    ∀ rule ∈ rules state, rule ∈ Distributed.Recall.Information.Agency.Protocol.rules model.source.code := by
  intro rule _
  exact every_rule_is_source_generated _ _

end Progress
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving

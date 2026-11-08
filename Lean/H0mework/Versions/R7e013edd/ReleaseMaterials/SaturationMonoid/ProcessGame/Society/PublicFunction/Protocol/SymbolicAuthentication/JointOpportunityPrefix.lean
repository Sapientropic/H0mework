import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointOpportunityGate

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointOpportunityPrefix
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev atCut (past : JointResponse.Stages model) (rounds : Nat) :=
  (JointResponseRun.run model start vocabulary encoding law rounds past).stages

def nextStages (past : JointResponse.Stages model) :=
  match JointResponse.step model start vocabulary encoding law past with
  | .advance action => JointResponse.after model start vocabulary encoding law past action
  | _ => past

theorem zero_has_the_original_stages (past : JointResponse.Stages model) : atCut model start vocabulary encoding law past 0 = past := by
  simp only [atCut, JointResponseRun.run]
  split
  · rfl
  · split <;> rfl

private theorem a_clear_cut_stays_at_the_same_actual_stages (past : JointResponse.Stages model)
    (closed : JointResponse.Clear model start vocabulary encoding law past) (rounds : Nat) :
    atCut model start vocabulary encoding law past rounds = past := by
  cases rounds with
  | zero => exact zero_has_the_original_stages model start vocabulary encoding law past
  | succ rounds => simp only [atCut, JointResponseRun.run, JointResponse.step, dif_pos closed]

private theorem an_exhausted_cut_stays_at_the_same_actual_stages (past : JointResponse.Stages model)
    (empty : JointResponse.fuel model start past = 0) (rounds : Nat) :
    atCut model start vocabulary encoding law past rounds = past := by
  cases rounds with
  | zero => exact zero_has_the_original_stages model start vocabulary encoding law past
  | succ rounds =>
    by_cases closed : JointResponse.Clear model start vocabulary encoding law past
    · exact a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed _
    · have actual : JointResponse.step model start vocabulary encoding law past = .exhausted empty := by
        simp only [JointResponse.step, dif_neg closed, dif_neg (by omega : ¬ 0 < JointResponse.fuel model start past)]
      simp only [atCut, JointResponseRun.run, actual]

theorem actual_run_prefixes_compose (first later : Nat) (past : JointResponse.Stages model) :
    atCut model start vocabulary encoding law past (first + later) =
      atCut model start vocabulary encoding law (atCut model start vocabulary encoding law past first) later := by
  induction first generalizing past with
  | zero => simp only [Nat.zero_add, zero_has_the_original_stages]
  | succ first ih =>
    cases observed : JointResponse.step model start vocabulary encoding law past with
    | clear closed =>
      rw [a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed (first + 1 + later),
        a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed (first + 1),
        a_clear_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past closed later]
    | exhausted empty =>
      rw [an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty (first + 1 + later),
        an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty (first + 1),
        an_exhausted_cut_stays_at_the_same_actual_stages model start vocabulary encoding law past empty later]
    | advance action =>
      simpa only [Nat.succ_add, atCut, JointResponseRun.run, observed] using
        ih (JointResponse.after model start vocabulary encoding law past action)

theorem an_actual_opportunity_is_the_next_original_run_prefix (rounds : Nat) (past : JointResponse.Stages model)
    (answer : JointOpportunityGate.Attempt model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds)) :
    JointOpportunityGate.full model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) answer =
      atCut model start vocabulary encoding law past (rounds + 1) := by
  rw [actual_run_prefixes_compose]
  rw [JointOpportunityGate.full, answer.actual]
  simp only [atCut, JointResponseRun.run, answer.selected]
  exact (zero_has_the_original_stages model start vocabulary encoding law _).symm

theorem the_next_actual_prefix_is_the_same_original_step (rounds : Nat) (past : JointResponse.Stages model) :
    atCut model start vocabulary encoding law past (rounds + 1) =
      nextStages model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) := by
  rw [actual_run_prefixes_compose]
  cases observed : JointResponse.step model start vocabulary encoding law (atCut model start vocabulary encoding law past rounds) with
  | clear closed => simp only [atCut, JointResponseRun.run, nextStages, observed]
  | exhausted empty => simp only [atCut, JointResponseRun.run, nextStages, observed]
  | advance action =>
    simp only [atCut, JointResponseRun.run, nextStages, observed]
    exact zero_has_the_original_stages model start vocabulary encoding law _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointOpportunityPrefix

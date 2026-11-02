import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Evaluation

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Replay

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)

theorem future_body_at_feedback (opponent : Opponent source.code)
    (control : List (Option source.code.Policy)) (empty : source.continuation = [])
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (n : Nat)
    (rounds : current.round = source.code.initial.round + (source.history.length+2+(cut+n))) :
    (Future.target source input cut opponent control).body current =
      word source.code (Residual.scheduleAt source cut control n) ⟨opponent,input.budget⟩
        (Residual.run source.code (Residual.scheduleAt source cut control) ⟨opponent,input.budget⟩
          (Residual.seed source input cut) n) := by
  unfold Machine.body
  rw [rounds]
  have address : source.code.initial.round + (source.history.length+2+(cut+n)) - source.code.initial.round - 1 =
      source.history.length+1+(cut+n) := by omega
  rw [address,List.getElem?_eq_none (by dsimp only [Future.target,Execution.target];omega),
    if_pos (by dsimp only [Future.target,Execution.target];omega)]
  simp only []
  rw [show source.history.length+1+(cut+n) - (Future.target source input cut opponent control).history.length - 1 = cut+n by
    change source.history.length+1+(cut+n)-source.history.length-1 = cut+n;omega]
  rw [empty]
  change word source.code ((Future.target source input cut opponent control).feedbackPolicy (cut+n))
    (Future.takeover source input cut opponent)
    ((Future.target source input cut opponent control).feedbackState (Future.takeover source input cut opponent) (cut+n)) = _
  rw [Execution.policy_at,Future.the_whole_future_run_is_the_actual_state]
  have lengths (k : Nat) :
      (Residual.run source.code (Residual.scheduleAt source cut control) ⟨opponent,input.budget⟩
        (Residual.seed source input cut) k).history.length = source.history.length+1+cut+k := by
    induction k with
    | zero =>
      change (source.feedbackState input cut).history.length = _
      have earlier (j : Nat) : (source.feedbackState input j).history.length = source.history.length+1+j := by
        induction j with
        | zero => simp [Machine.feedbackState,Machine.feedbackInitial]
        | succ j ih =>
          change (advance source.code _ input _).history.length = _
          rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
          omega
      exact earlier cut
    | succ k ih =>
      change (advance source.code _ _ _).history.length = _
      rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
      omega
  simp only [word,decision,if_neg (show ¬(Residual.run source.code (Residual.scheduleAt source cut control)
    ⟨opponent,input.budget⟩ (Residual.seed source input cut) n).history.length < source.history.length+1+cut by
      rw [lengths];omega)]
  rfl

theorem feedback_history_length (n : Nat) :
    (source.feedbackState input n).history.length = source.history.length+1+n := by
  induction n with
  | zero => simp [Machine.feedbackState,Machine.feedbackInitial]
  | succ n ih =>
    change (advance source.code _ input _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

theorem history_length (raw : List (Option source.code.Policy)) (rival : Opponent source.code) (n : Nat) :
    (Residual.run source.code (Residual.scheduleAt source cut raw) ⟨rival,input.budget⟩
      (Residual.seed source input cut) n).history.length = source.history.length+1+cut+n := by
  induction n with
  | zero => exact feedback_history_length source input cut
  | succ n ih =>
    change (advance source.code _ _ _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

variable (raw nextRaw : List (Option source.code.Policy)) (rival nextRival : Opponent source.code)
  (runs : ∀ n, Residual.run source.code (Residual.scheduleAt source cut nextRaw)
      ⟨nextRival,input.budget⟩ (Residual.seed source input cut) n =
    Residual.run source.code (Residual.scheduleAt source cut raw)
      ⟨rival,input.budget⟩ (Residual.seed source input cut) n)

include runs in
theorem words (n : Nat) :
    word source.code (Residual.scheduleAt source cut nextRaw n) ⟨nextRival,input.budget⟩
      (Residual.run source.code (Residual.scheduleAt source cut nextRaw) ⟨nextRival,input.budget⟩ (Residual.seed source input cut) n) =
    word source.code (Residual.scheduleAt source cut raw n) ⟨rival,input.budget⟩
      (Residual.run source.code (Residual.scheduleAt source cut raw) ⟨rival,input.budget⟩ (Residual.seed source input cut) n) := by
  have both := congrArg State.history (runs (n+1))
  simp only [Residual.run,history_keeps_every_actual_word,runs n] at both
  simpa only [runs n] using List.singleton_inj.mp (List.append_cancel_left both)

include runs in
theorem source_events (active : source.feedback? = some input) (empty : source.continuation = [])
    (ordinal : Nat) :
    ProgrammeSource.rawEvent (Future.target source input cut nextRival nextRaw).input
      (ProgrammeHistory.visitAt (Future.target source input cut rival raw).input ordinal).current =
    ProgrammeSource.rawEvent (Future.target source input cut rival raw).input
      (ProgrammeHistory.visitAt (Future.target source input cut rival raw).input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt (Future.target source input cut rival raw).input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (Future.target source input cut nextRival nextRaw).body current =
      (Future.target source input cut rival raw).body current
    have rounds := ProgrammeHistory.visit_round (Future.target source input cut rival raw).input ordinal
    rw [view] at rounds
    change current.round = source.code.initial.round+ordinal at rounds
    by_cases earlier : ordinal < source.history.length+2+cut
    · exact (Future.earlier_body source input cut nextRival nextRaw active current
          (by omega)).trans
        (Future.earlier_body source input cut rival raw active current
          (by omega)).symm
    · let n := ordinal-(source.history.length+2+cut)
      have indexed : ordinal = source.history.length+2+(cut+n) := by dsimp only [n];omega
      rw [future_body_at_feedback source input cut nextRival nextRaw empty current n (by omega),
        future_body_at_feedback source input cut rival raw empty current n (by omega)]
      exact words source input cut raw nextRaw rival nextRival runs n

include runs in
theorem source_bodies (active : source.feedback? = some input) (empty : source.continuation = []) :
    (Future.target source input cut nextRival nextRaw).body =
      (Future.target source input cut rival raw).body := by
  funext current
  by_cases earlier : current.round-source.code.initial.round-1 < source.history.length+1+cut
  · exact (Future.earlier_body source input cut nextRival nextRaw active current earlier).trans
      (Future.earlier_body source input cut rival raw active current earlier).symm
  · let n := current.round-source.code.initial.round-(source.history.length+2+cut)
    have rounds : current.round = source.code.initial.round+(source.history.length+2+(cut+n)) := by
      dsimp only [n];omega
    rw [future_body_at_feedback source input cut nextRival nextRaw empty current n rounds,
      future_body_at_feedback source input cut rival raw empty current n rounds]
    exact words source input cut raw nextRaw rival nextRival runs n

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Replay

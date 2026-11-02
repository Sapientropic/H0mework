import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Rule
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Emission
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : Cursor code)

private theorem run_length (schedule : Residual.Schedule code) (input : Input code) (n : Nat) :
    (Residual.run code schedule input (Residual.seed point.source point.entry point.cut) n).history.length =
      point.history.length+1+point.cut+n := by
  have initial (count : Nat) : (point.source.feedbackState point.entry count).history.length = point.history.length+1+count := by
    induction count with
    | zero => simp only [Machine.feedbackState,Machine.feedbackInitial,List.length_append,List.length_singleton,Nat.add_zero]
    | succ count ih =>
        change (Feedback.advance code _ _ _).history.length = _
        rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
        omega
  induction n with
  | zero => exact initial point.cut
  | succ n ih =>
      rw [Residual.run,history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
      omega

private theorem body_at_round (driver : Opponent code) (term : Cut.Term point.source point.entry point.cut)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (n : Nat)
    (rounds : current.round = code.initial.round+(point.history.length+2+(point.cut+n))) :
    (Future.target point.source point.entry point.cut driver term.val).body current =
      word code (Residual.scheduleAt point.source point.cut term.val n) ⟨driver,point.entry.budget⟩
        (Residual.run code (Residual.scheduleAt point.source point.cut term.val)
          ⟨driver,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n) := by
  let candidate := Future.target point.source point.entry point.cut driver term.val
  have policy : candidate.feedbackPolicy (point.cut+n) = Residual.scheduleAt point.source point.cut term.val n :=
    Execution.policy_at {point.source with feedback? := some (Future.takeover point.source point.entry point.cut driver)} point.cut term.val n
  unfold Machine.body
  rw [rounds]
  have address : code.initial.round+(point.history.length+2+(point.cut+n))-code.initial.round-1 = point.history.length+1+(point.cut+n) := by omega
  rw [address,List.getElem?_eq_none (by dsimp only [Future.target,Execution.target];omega),if_pos (by dsimp only [Future.target,Execution.target];omega)]
  simp only []
  rw [show point.history.length+1+(point.cut+n)-candidate.history.length-1 = point.cut+n by change point.history.length+1+(point.cut+n)-point.history.length-1 = point.cut+n;omega]
  change (match point.source.continuation[point.cut+n]? with | some word => word | none => candidate.laterResponse current (point.cut+n)) = _
  rw [show point.source.continuation = [] from rfl]
  change word code (candidate.feedbackPolicy (point.cut+n)) (Future.takeover point.source point.entry point.cut driver)
    (candidate.feedbackState (Future.takeover point.source point.entry point.cut driver) (point.cut+n)) = _
  rw [policy,Future.the_whole_future_run_is_the_actual_state]
  simp only [word,decision,if_neg (show ¬(Residual.run code (Residual.scheduleAt point.source point.cut term.val) ⟨driver,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n).history.length < point.history.length+1+point.cut by rw [run_length];omega)]

variable (first second : Opponent code)
  (firstTerm secondTerm : Cut.Term point.source point.entry point.cut)
  (states : ∀ n, Residual.run code (Residual.scheduleAt point.source point.cut firstTerm.val) ⟨first,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n =
    Residual.run code (Residual.scheduleAt point.source point.cut secondTerm.val) ⟨second,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n)

include states in
theorem equal_actual_runs_generate_one_complete_input :
    (Future.target point.source point.entry point.cut first firstTerm.val).input =
      (Future.target point.source point.entry point.cut second secondTerm.val).input := by
  have words (n : Nat) :
      word code (Residual.scheduleAt point.source point.cut firstTerm.val n) ⟨first,point.entry.budget⟩
          (Residual.run code (Residual.scheduleAt point.source point.cut firstTerm.val) ⟨first,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n) =
      word code (Residual.scheduleAt point.source point.cut secondTerm.val n) ⟨second,point.entry.budget⟩
          (Residual.run code (Residual.scheduleAt point.source point.cut secondTerm.val) ⟨second,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n) := by
    have same := congrArg State.history (states (n+1))
    simp only [Residual.run,history_keeps_every_actual_word] at same
    rw [states n] at same ⊢
    exact List.singleton_inj.mp (List.append_cancel_left same)
  have bodies : (Future.target point.source point.entry point.cut first firstTerm.val).body =
      (Future.target point.source point.entry point.cut second secondTerm.val).body := by
    funext current
    by_cases earlier : current.round-code.initial.round-1 < point.history.length+1+point.cut
    · exact (Future.earlier_body point.source point.entry point.cut first firstTerm.val rfl current earlier).trans
        (Future.earlier_body point.source point.entry point.cut second secondTerm.val rfl current earlier).symm
    · let n := current.round-code.initial.round-1-(point.history.length+1+point.cut)
      have rounds : current.round = code.initial.round+(point.history.length+2+(point.cut+n)) := by dsimp only [n];omega
      rw [body_at_round point first firstTerm current n rounds,body_at_round point second secondTerm current n rounds]
      exact words n
  have reports : (Future.target point.source point.entry point.cut first firstTerm.val).report =
      (Future.target point.source point.entry point.cut second secondTerm.val).report := by
    funext current
    exact congrArg (ProgrammeSource.ProgrammeReport.original current) (congrFun bodies current)
  simp only [Machine.input,bodies,reports]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Emission

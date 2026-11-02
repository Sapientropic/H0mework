import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Transport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

structure Aligned (first second : Cursor code) : Prop where
  history : first.history = second.history
  cut : first.cut = second.cut
  owner : first.ownerStart = second.ownerStart
  budget : first.entry.budget = second.entry.budget
  body : first.source.body = second.source.body
  seed : first.source.feedbackState first.entry first.cut = second.source.feedbackState second.entry second.cut

namespace Aligned
variable {first second third : Cursor code}

theorem refl (point : Cursor code) : Aligned point point := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem trans (left : Aligned first second) (right : Aligned second third) : Aligned first third :=
  ⟨left.history.trans right.history,left.cut.trans right.cut,left.owner.trans right.owner,
    left.budget.trans right.budget,left.body.trans right.body,left.seed.trans right.seed⟩

theorem input (matched : Aligned first second) : first.source.input = second.source.input := by
  have reports : first.source.report = second.source.report := by
    funext current
    exact congrArg (ProgrammeSource.ProgrammeReport.original current) (congrFun matched.body current)
  simp only [Machine.input,matched.body,reports]

theorem horizon (matched : Aligned first second) :
    Cut.horizon first.source first.entry first.cut = Cut.horizon second.source second.entry second.cut :=
  congrArg State.remaining matched.seed

theorem start (matched : Aligned first second) : Cut.start first.source first.cut = Cut.start second.source second.cut := by
  change first.history.length+2+first.cut = second.history.length+2+second.cut
  rw [matched.history,matched.cut]

theorem finish (matched : Aligned first second) :
    Cut.finish first.source first.entry first.cut = Cut.finish second.source second.entry second.cut :=
  congrArg₂ (·+·) matched.start matched.horizon

private abbrev run (point : Cursor code) (rule : Rule code) (rival : Opponent code) (n : Nat) :=
  Residual.run code (Residual.scheduleAt point.source point.cut (term point.source point.entry point.cut rule).val)
    ⟨Cursor.controller point rule rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n

private theorem runs (matched : Aligned first second) (rule : Rule code) (rival : Opponent code) (n : Nat) :
    run first rule rival n = run second rule rival n := by
  have inputs : (⟨Cursor.controller first rule rival,first.entry.budget⟩ : Input code) =
      ⟨Cursor.controller second rule rival,second.entry.budget⟩ := by
    simp only [Cursor.controller,matched.owner,matched.budget]
  induction n with
  | zero => exact matched.seed
  | succ n ih =>
    simp only [run,Residual.run] at ih ⊢
    rw [ih,inputs]
    let actual := run second rule rival n
    change Reaction.Feedback.advance code _ _ actual = Reaction.Feedback.advance code _ _ actual
    by_cases exhausted : actual.remaining = 0
    · cases (Residual.scheduleAt first.source first.cut (term first.source first.entry first.cut rule).val n) <;>
        cases (Residual.scheduleAt second.source second.cut (term second.source second.entry second.cut rule).val n) <;>
        simp only [Reaction.Feedback.advance,word,decision,exhausted,if_pos]
    · have remaining := Residual.remaining_is_the_seed_budget code
        (Residual.scheduleAt second.source second.cut (term second.source second.entry second.cut rule).val)
        ⟨Cursor.controller second rule rival,second.entry.budget⟩
        (Residual.seed second.source second.entry second.cut) n
      change actual.remaining = _ at remaining
      have bounded : n < (second.source.feedbackState second.entry second.cut).remaining := by
        change actual.remaining = (second.source.feedbackState second.entry second.cut).remaining-n at remaining
        omega
      have leftBound : n < (first.source.feedbackState first.entry first.cut).remaining := by
        rw [matched.seed];exact bounded
      have leftPolicy : Residual.scheduleAt first.source first.cut
          (term first.source first.entry first.cut rule).val n = some rule.work.val := by
        simp only [Residual.scheduleAt,term,List.getElem?_replicate,if_pos leftBound,Option.getD_some]
      have rightPolicy : Residual.scheduleAt second.source second.cut
          (term second.source second.entry second.cut rule).val n = some rule.work.val := by
        simp only [Residual.scheduleAt,term,List.getElem?_replicate,if_pos bounded,Option.getD_some]
      rw [leftPolicy,rightPolicy]

theorem after_states (matched : Aligned first second) (rule : Rule code) (rival : Opponent code) (n : Nat) :
    (Cursor.target first rule rival).feedbackState (Cursor.targetInput first rule rival) (first.cut+n) =
      (Cursor.target second rule rival).feedbackState (Cursor.targetInput second rule rival) (second.cut+n) := by
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state]
  exact runs matched rule rival n

private theorem run_length (point : Cursor code) (rule : Rule code) (rival : Opponent code) (n : Nat) :
    (run point rule rival n).history.length = point.history.length+1+point.cut+n := by
  have lengthAt : ∀ k, (point.source.feedbackState point.entry k).history.length = point.history.length+1+k := by
    intro k
    induction k with
    | zero => simp [Machine.feedbackState,Machine.feedbackInitial,Cursor.source]
    | succ k ih =>
      change (Reaction.Feedback.advance code _ _ _).history.length = _
      rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
      omega
  induction n with
  | zero => exact lengthAt point.cut
  | succ n ih =>
    change (Reaction.Feedback.advance code _ _ _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

private theorem body_at (point : Cursor code) (rule : Rule code) (rival : Opponent code)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (n : Nat)
    (rounds : current.round = code.initial.round+(point.history.length+2+(point.cut+n))) :
    (Cursor.target point rule rival).body current =
      word code (Residual.scheduleAt point.source point.cut (term point.source point.entry point.cut rule).val n)
        ⟨Cursor.controller point rule rival,point.entry.budget⟩ (run point rule rival n) := by
  unfold Machine.body
  rw [rounds]
  have address : code.initial.round+(point.history.length+2+(point.cut+n))-code.initial.round-1 =
      point.history.length+1+(point.cut+n) := by omega
  rw [address,List.getElem?_eq_none (by dsimp only [Cursor.target,Future.target,Execution.target,Cursor.source];omega),
    if_pos (by dsimp only [Cursor.target,Future.target,Execution.target,Cursor.source];omega)]
  simp only []
  rw [show point.history.length+1+(point.cut+n)-(Cursor.target point rule rival).history.length-1 =
    point.cut+n by change point.history.length+1+(point.cut+n)-point.history.length-1 = _;omega]
  change word code ((Cursor.target point rule rival).feedbackPolicy (point.cut+n))
    (Cursor.targetInput point rule rival)
    ((Cursor.target point rule rival).feedbackState (Cursor.targetInput point rule rival) (point.cut+n)) = _
  have policy := Execution.policy_at
    {point.source with feedback? := some (Cursor.targetInput point rule rival)} point.cut
    (term point.source point.entry point.cut rule).val n
  change (Cursor.target point rule rival).feedbackPolicy (point.cut+n) =
    Residual.scheduleAt point.source point.cut (term point.source point.entry point.cut rule).val n at policy
  rw [policy,Future.the_whole_future_run_is_the_actual_state]
  simp only [word,decision,if_neg (show ¬(run point rule rival n).history.length <
    point.history.length+1+point.cut by rw [run_length];omega)]

private theorem words (matched : Aligned first second) (rule : Rule code) (rival : Opponent code) (n : Nat) :
    word code (Residual.scheduleAt first.source first.cut (term first.source first.entry first.cut rule).val n)
        ⟨Cursor.controller first rule rival,first.entry.budget⟩ (run first rule rival n) =
      word code (Residual.scheduleAt second.source second.cut (term second.source second.entry second.cut rule).val n)
        ⟨Cursor.controller second rule rival,second.entry.budget⟩ (run second rule rival n) := by
  have history := congrArg State.history (runs matched rule rival (n+1))
  simp only [run,Residual.run,history_keeps_every_actual_word] at history
  have same := runs matched rule rival n
  dsimp only [run] at same
  rw [same] at history
  simpa only [run,same] using List.singleton_inj.mp (List.append_cancel_left history)

theorem after_body (matched : Aligned first second) (rule : Rule code) (rival : Opponent code) :
    (Cursor.target first rule rival).body = (Cursor.target second rule rival).body := by
  funext current
  by_cases earlier : current.round-code.initial.round-1 < first.history.length+1+first.cut
  · have left := Future.earlier_body first.source first.entry first.cut (Cursor.controller first rule rival)
      (term first.source first.entry first.cut rule).val rfl current earlier
    have right := Future.earlier_body second.source second.entry second.cut (Cursor.controller second rule rival)
      (term second.source second.entry second.cut rule).val rfl current
      (by change _ < second.history.length+1+second.cut;rw [←matched.history,←matched.cut];exact earlier)
    exact left.trans ((congrFun matched.body current).trans right.symm)
  · let n := current.round-code.initial.round-(first.history.length+2+first.cut)
    have rounds : current.round = code.initial.round+(first.history.length+2+(first.cut+n)) := by
      dsimp only [n];omega
    rw [body_at first rule rival current n rounds,
      body_at second rule rival current n (by rw [←matched.history,←matched.cut];exact rounds)]
    exact words matched rule rival n

theorem after (matched : Aligned first second) (rule : Rule code) (rival : Opponent code) :
    Aligned (first.after rule rival) (second.after rule rival) :=
  ⟨matched.history,congrArg (·+1) matched.cut,matched.owner,matched.budget,
    after_body matched rule rival,after_states matched rule rival 1⟩

theorem representative (point : Cursor code) (rule : Rule code) (rival : Opponent code) :
    Aligned (Transport.representative point rule rival) (Transport.actual point rule rival) :=
  ⟨rfl,rfl,rfl,rfl,Transport.the_original_finite_table_preserves_the_complete_emitter point rule rival,
    Transport.the_next_seed_is_its_actual_unspent_state point rule rival⟩

end Aligned

def Covered (domain : List (Cursor code)) (actual : Cursor code) : Prop :=
  ∃ point ∈ domain, Aligned point actual

theorem every_actual_installation_stays_in_its_own_public_information_domain
    (domain : List (Cursor code)) (actual : Cursor code) (covered : Covered domain actual)
    (rule : Rule code) (rival : Opponent code) :
    Covered (advance code domain rule) (actual.after rule rival) := by
  obtain ⟨point,inside,matched⟩ := covered
  refine ⟨Transport.representative point rule rival,
    every_generated_table_produces_its_own_successor code domain rule point inside (externalTable point rival)
      (Residual.restriction_is_generated _ _ _ rival),?_⟩
  exact (Aligned.representative point rule rival).trans (matched.after rule rival)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation

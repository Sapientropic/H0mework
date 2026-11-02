import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Finite
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Alignment

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Successor

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def after (point : Cursor code) (fallback : Rule code) (program : Program code)
    (rival : Opponent code) (count : Nat) : Cursor code :=
  let actual := source point fallback program rival
  ⟨actual.reference,actual.reference_generated,actual.history,actual.original,actual.opponent,actual.side,
    entry point fallback program rival,actual.feedbackOverrides,point.cut+count,point.ownerStart⟩

def advance (domain : List (Cursor code)) (fallback : Rule code) (program : Program code) : List (Cursor code) :=
  domain.flatMap fun point => (Finite.tables point fallback [program]).map fun table =>
    after point fallback program (Finite.opponent point fallback [program] table) 1

theorem table_successor_is_generated (domain : List (Cursor code)) (point : Cursor code)
    (inside : point ∈ domain) (fallback : Rule code) (program : Program code)
    (table : Finite.Table point fallback [program]) (generated : table ∈ Finite.tables point fallback [program]) :
    after point fallback program (Finite.opponent point fallback [program] table) 1 ∈ advance domain fallback program :=
  List.mem_flatMap.mpr ⟨point,inside,List.mem_map.mpr ⟨table,generated,rfl⟩⟩

theorem representative (point : Cursor code) (fallback : Rule code) (program : Program code)
    (rival : Opponent code) (count : Nat) :
    Aligned (after point fallback program (Finite.representative point fallback [program] rival) count)
      (after point fallback program rival count) := by
  have runs := Finite.every_ordinal_state_is_preserved point fallback [program] program
    (List.mem_singleton_self _) rival
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  · exact Replay.source_bodies point.source point.entry point.cut
      (schedule point fallback program) (schedule point fallback program)
      (controller point fallback program rival)
      (controller point fallback program (Finite.representative point fallback [program] rival)) runs rfl rfl
  · change (source point fallback program (Finite.representative point fallback [program] rival)).feedbackState
      (entry point fallback program (Finite.representative point fallback [program] rival)) (point.cut+count) =
      (source point fallback program rival).feedbackState (entry point fallback program rival) (point.cut+count)
    rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state]
    exact runs count

private abbrev run (point : Cursor code) (fallback : Rule code) (program : Program code)
    (rival : Opponent code) (n : Nat) :=
  Residual.run code (Residual.scheduleAt point.source point.cut (schedule point fallback program))
    ⟨controller point fallback program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n

variable {first second : Cursor code} (matched : Aligned first second)
  (fallback : Rule code) (program : Program code) (rival : Opponent code)

include matched in
theorem schedules : schedule first fallback program = schedule second fallback program := by
  unfold schedule
  rw [matched.horizon]

include matched in
theorem controllers : controller first fallback program rival = controller second fallback program rival := by
  unfold controller
  rw [matched.history,matched.cut,matched.owner]

include matched in
theorem runs (n : Nat) : run first fallback program rival n = run second fallback program rival n := by
  have inputs : (⟨controller first fallback program rival,first.entry.budget⟩ : Input code) =
      ⟨controller second fallback program rival,second.entry.budget⟩ := by
    rw [controllers matched,matched.budget]
  induction n with
  | zero => exact matched.seed
  | succ n ih =>
    simp only [run,Residual.run] at ih ⊢
    rw [ih,inputs]
    let actual := run second fallback program rival n
    change Reaction.Feedback.advance code _ _ actual = Reaction.Feedback.advance code _ _ actual
    by_cases exhausted : actual.remaining = 0
    · cases (Residual.scheduleAt first.source first.cut (schedule first fallback program) n) <;>
        cases (Residual.scheduleAt second.source second.cut (schedule second fallback program) n) <;>
        simp only [Reaction.Feedback.advance,word,decision,exhausted,if_pos]
    · have remaining := Residual.remaining_is_the_seed_budget code
        (Residual.scheduleAt second.source second.cut (schedule second fallback program))
        ⟨controller second fallback program rival,second.entry.budget⟩
        (Residual.seed second.source second.entry second.cut) n
      change actual.remaining = _ at remaining
      have bounded : n < Cut.horizon second.source second.entry second.cut := by
        change actual.remaining = (second.source.feedbackState second.entry second.cut).remaining-n at remaining
        change n < (second.source.feedbackState second.entry second.cut).remaining
        omega
      have leftBound : n < Cut.horizon first.source first.entry first.cut := by rw [matched.horizon];exact bounded
      have atWork (point : Cursor code) (inside : n < Cut.horizon point.source point.entry point.cut) :
          Residual.scheduleAt point.source point.cut (schedule point fallback program) n =
            (stage code fallback program n).work := by
        simp only [Residual.scheduleAt,schedule,List.getElem?_map,
          List.getElem?_range inside,Option.map_some,Option.getD_some]
      rw [atWork first leftBound,atWork second bounded]

include matched in
theorem source_bodies : (source first fallback program rival).body = (source second fallback program rival).body := by
  have words (n : Nat) :
      word code (Residual.scheduleAt first.source first.cut (schedule first fallback program) n)
          ⟨controller first fallback program rival,first.entry.budget⟩ (run first fallback program rival n) =
      word code (Residual.scheduleAt second.source second.cut (schedule second fallback program) n)
          ⟨controller second fallback program rival,second.entry.budget⟩ (run second fallback program rival n) := by
    have histories := congrArg State.history (runs matched fallback program rival (n+1))
    simp only [run,Residual.run,history_keeps_every_actual_word] at histories
    have same := runs matched fallback program rival n
    dsimp only [run] at same
    rw [same] at histories
    simpa only [run,same] using List.singleton_inj.mp (List.append_cancel_left histories)
  funext current
  by_cases earlier : current.round-code.initial.round-1 < first.history.length+1+first.cut
  · exact (Future.earlier_body first.source first.entry first.cut (controller first fallback program rival)
      (schedule first fallback program) rfl current earlier).trans
      ((congrFun matched.body current).trans
        (Future.earlier_body second.source second.entry second.cut (controller second fallback program rival)
          (schedule second fallback program) rfl current
          (by change _ < second.history.length+1+second.cut;rw [←matched.history,←matched.cut];exact earlier)).symm)
  · let n := current.round-code.initial.round-(first.history.length+2+first.cut)
    have rounds : current.round = code.initial.round+(first.history.length+2+(first.cut+n)) := by
      dsimp only [n];omega
    rw [Replay.future_body_at_feedback first.source first.entry first.cut (controller first fallback program rival)
        (schedule first fallback program) rfl current n rounds,
      Replay.future_body_at_feedback second.source second.entry second.cut (controller second fallback program rival)
        (schedule second fallback program) rfl current n
        (by change current.round = code.initial.round+(second.history.length+2+(second.cut+n));rw [←matched.history,←matched.cut];exact rounds)]
    exact words n

include matched in
theorem aligned_after (count : Nat) :
    Aligned (after first fallback program rival count) (after second fallback program rival count) := by
  refine ⟨matched.history,congrArg (·+count) matched.cut,matched.owner,matched.budget,
    source_bodies matched fallback program rival,?_⟩
  change (source first fallback program rival).feedbackState (entry first fallback program rival) (first.cut+count) =
    (source second fallback program rival).feedbackState (entry second fallback program rival) (second.cut+count)
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state]
  exact runs matched fallback program rival count

theorem every_actual_raw_installation_has_a_public_successor
    (domain : List (Cursor code)) (actual : Cursor code) (covered : Covered domain actual)
    (fallback : Rule code) (program : Program code) (rival : Opponent code) :
    Covered (advance domain fallback program) (after actual fallback program rival 1) := by
  obtain ⟨point,inside,matched⟩ := covered
  refine ⟨after point fallback program (Finite.representative point fallback [program] rival) 1,
    table_successor_is_generated domain point inside fallback program
      (Finite.restrict point fallback [program] rival) (Residual.restriction_is_generated _ _ _ rival),?_⟩
  exact (representative point fallback program rival 1).trans (aligned_after matched fallback program rival 1)

def history (domain : List (Cursor code)) (fallback : Rule code) (installed : List (Program code)) :=
  installed.foldl (fun current program => advance current fallback program) domain

def execute (actual : Cursor code) (fallback : Rule code) : List (Program code × Opponent code) → Cursor code
  | [] => actual
  | (program,rival)::rest => execute (after actual fallback program rival 1) fallback rest

theorem every_finite_actual_raw_installation_stays_public
    (domain : List (Cursor code)) (actual : Cursor code) (covered : Covered domain actual)
    (fallback : Rule code) (installed : List (Program code × Opponent code)) :
    Covered (history domain fallback (installed.map Prod.fst)) (execute actual fallback installed) := by
  induction installed generalizing domain actual with
  | nil => exact covered
  | cons step rest ih =>
    exact ih (advance domain fallback step.1) (after actual fallback step.1 step.2 1)
      (every_actual_raw_installation_has_a_public_successor domain actual covered fallback step.1 step.2)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Successor

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

section Local

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : Continuation.Cursor code) (reference : Rule code) (program : Program code)

abbrev remaining := Cut.horizon point.source point.entry point.cut

omit [DecidableEq Port] [DecidableEq Technology] in
theorem normalized_controller_keeps_each_consumed_decision (cap horizon n : Nat) (inside : n < horizon)
    (rival : Opponent code) (history : History) (past : Events code) (frame : code.Frame)
    (length : history.length = point.history.length+1+point.cut+n) :
    controller point reference (normalized cap horizon reference program) rival history past frame =
      controller point reference program rival history past frame := by
  simp only [controller,length,Nat.add_sub_cancel_left]
  rw [normalized_at reference program cap horizon n inside]
  simp only [driver,localEvent,Rule.normalize]

private theorem consumed_work (n : Nat) (inside : n < remaining point) :
    Residual.scheduleAt point.source point.cut (schedule point reference program) n =
      (stage code reference program n).work := by
  simp only [Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

private theorem normalized_work (cap horizon n : Nat) (enough : remaining point ≤ horizon) (inside : n < remaining point) :
    Residual.scheduleAt point.source point.cut (schedule point reference (normalized cap horizon reference program)) n =
      (Residual.scheduleAt point.source point.cut (schedule point reference program) n).map (Normalization.policy code cap) := by
  rw [consumed_work point reference _ n inside,consumed_work point reference program n inside,
    normalized_at reference program cap horizon n (inside.trans_le enough)]
  rfl

theorem supported_schedule
    (supported : ∀ n < remaining point, (stage code reference program n).supported) :
    Normalization.Source.Supported point.source point.cut (schedule point reference program) (remaining point) := by
  intro n inside policy chosen
  rw [consumed_work point reference program n inside] at chosen
  exact supported n inside policy chosen

variable (party : Party) (good : Good) (floor : Gross.Floor code.law party good code.actions) (budget : ℚ)
  (rival : Opponent code) (horizon : Nat) (enough : remaining point ≤ horizon)
  (paid : Normalization.Source.Paid point.source point.entry point.cut (schedule point reference program)
    (remaining point) party good budget (controller point reference program rival))

include paid enough in
theorem normalized_program_keeps_every_actual_state (n : Nat) :
    Residual.run code (Residual.scheduleAt point.source point.cut
        (schedule point reference (normalized (floor.cap budget) horizon reference program)))
      ⟨controller point reference (normalized (floor.cap budget) horizon reference program) rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n =
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point reference program))
      ⟨controller point reference program rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n := by
  let old := Residual.scheduleAt point.source point.cut (schedule point reference program)
  let new := Residual.scheduleAt point.source point.cut
    (schedule point reference (normalized (floor.cap budget) horizon reference program))
  have localBounds := Normalization.gross_budget_bounds_only_local_work code old
    ⟨controller point reference program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut)
    (remaining point) party good floor budget paid.1 paid.2
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Residual.run]
    rw [ih]
    let actual := Residual.run code old ⟨controller point reference program rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n
    change advance code (new n)
        ⟨controller point reference (normalized (floor.cap budget) horizon reference program) rival,point.entry.budget⟩ actual =
      advance code (old n) ⟨controller point reference program rival,point.entry.budget⟩ actual
    by_cases exhausted : actual.remaining = 0
    · cases new n <;> cases old n <;>
        simp only [advance,word,decision,exhausted,if_pos]
    · have inside : n < remaining point := by
        have left := Residual.remaining_is_the_seed_budget code old
          ⟨controller point reference program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n
        change actual.remaining = remaining point-n at left
        omega
      have length := Replay.history_length point.source point.entry point.cut (schedule point reference program)
        (controller point reference program rival) n
      have decisions := normalized_controller_keeps_each_consumed_decision point reference program (floor.cap budget)
        horizon n (inside.trans_le enough) rival actual.history actual.past actual.frame length
      calc
        _ = advance code (new n) ⟨controller point reference program rival,point.entry.budget⟩ actual := by
          rw [Residual.advance_is_its_actual_choice,Residual.advance_is_its_actual_choice]
          exact congrArg (fun move => Residual.forced code (new n) move actual) decisions
        _ = advance code (old n) ⟨controller point reference program rival,point.entry.budget⟩ actual := by
          rw [show new n = (old n).map (Normalization.policy code (floor.cap budget)) from
            normalized_work point reference program (floor.cap budget) horizon n enough inside]
          exact Normalization.one_step_preserves_all_external_attempts code (floor.cap budget) (old n)
            ⟨controller point reference program rival,point.entry.budget⟩ actual (localBounds n inside)

end Local

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (world : Continuation.Cursor model.source.code) (fallback : Rule model.source.code)
  (raw : Program model.source.code) (bearer : Party) (material : Good)
  (positive : Gross.Floor model.source.code.law bearer material model.source.code.actions) (publicR : ℚ)
  (environment : Opponent model.source.code) (horizon : Nat) (enough : remaining world ≤ horizon)
  (originalPaid : Normalization.Source.Paid world.source world.entry world.cut (schedule world fallback raw)
    (remaining world) bearer material publicR (controller world fallback raw environment))

include originalPaid enough in
theorem normalized_program_preserves_the_complete_actual_evaluation :
    Finite.actualEvaluation model world fallback (normalized (positive.cap publicR) horizon fallback raw) environment =
      Finite.actualEvaluation model world fallback raw environment := by
  have runs := normalized_program_keeps_every_actual_state world fallback raw bearer material positive publicR environment horizon enough originalPaid
  exact Transport.full_evaluation_congr (Continuation.Replanning.native model world) world.entry world.cut
    (schedule world fallback raw) (schedule world fallback (normalized (positive.cap publicR) horizon fallback raw))
    (controller world fallback raw environment)
    (controller world fallback (normalized (positive.cap publicR) horizon fallback raw) environment)
    (fun ordinal _ => Replay.source_events world.source world.entry world.cut
      (schedule world fallback raw) (schedule world fallback (normalized (positive.cap publicR) horizon fallback raw))
      (controller world fallback raw environment)
      (controller world fallback (normalized (positive.cap publicR) horizon fallback raw) environment)
      runs rfl rfl ordinal)
    (runs _) rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme

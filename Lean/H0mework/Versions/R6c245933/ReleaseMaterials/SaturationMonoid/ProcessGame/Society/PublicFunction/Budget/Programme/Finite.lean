import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Replay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Finite

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

section Remaining

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : Continuation.Cursor code) (reference : Rule code) (pool : List (Program code))

/-- Keys are generated from these actual raw schedules, not from the old actionLimit. -/
def schedules : List (Residual.Schedule code) := pool.map (fun program => Residual.scheduleAt point.source point.cut (schedule point reference program))
abbrev Table := Residual.Table code (Residual.seed point.source point.entry point.cut) (schedules point reference pool)
abbrev tables := Residual.tables code (Residual.seed point.source point.entry point.cut) (schedules point reference pool)
abbrev opponent (table : Table point reference pool) :=
  Residual.respond code (Residual.seed point.source point.entry point.cut) (schedules point reference pool) table
abbrev restrict (rival : Opponent code) : Table point reference pool :=
  Residual.restrict code (Residual.seed point.source point.entry point.cut) (schedules point reference pool) rival
abbrev representative (rival : Opponent code) := opponent point reference pool (restrict point reference pool rival)

variable (program : Program code) (generated : program ∈ pool) (rival : Opponent code)

include generated in
theorem every_ordinal_state_is_preserved (n : Nat) :
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point reference program))
      ⟨controller point reference program (representative point reference pool rival),point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n =
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point reference program))
      ⟨controller point reference program rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n := by
  let controls := Residual.scheduleAt point.source point.cut (schedule point reference program)
  have registered : controls ∈ schedules point reference pool := List.mem_map.mpr ⟨program,generated,rfl⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Residual.run]
    rw [ih]
    let actual := Residual.run code controls ⟨controller point reference program rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n
    change advance code (controls n) ⟨controller point reference program (representative point reference pool rival),point.entry.budget⟩ actual =
      advance code (controls n) ⟨controller point reference program rival,point.entry.budget⟩ actual
    by_cases exhausted : actual.remaining = 0
    · simp only [advance,word,decision,exhausted,if_pos]
    · have bounded : n < (Residual.seed point.source point.entry point.cut).remaining := by
        have remaining := Residual.remaining_is_the_seed_budget code controls
          ⟨controller point reference program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n
        change actual.remaining = _ at remaining
        omega
      have keyed := Residual.every_remaining_decision_is_generated code
        (Residual.seed point.source point.entry point.cut) (schedules point reference pool)
        controls registered ⟨controller point reference program rival,point.entry.budget⟩ n bounded
      rw [Residual.advance_is_its_actual_choice,Residual.advance_is_its_actual_choice]
      apply congrArg (fun move => Residual.forced code (controls n) move actual)
      simp only [controller,driver]
      cases owned : ownerAt code point.ownerStart actual.history.length with
      | some site => rfl
      | none =>
        exact congrArg (externalChoice code)
          (Residual.restriction_agrees code (Residual.seed point.source point.entry point.cut)
            (schedules point reference pool) rival actual keyed)

end Remaining

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (world : Continuation.Cursor model.source.code) (fallback : Rule model.source.code)
  (programmes : List (Program model.source.code))

abbrev actualEvaluation (program : Program model.source.code) (rival : Opponent model.source.code) :=
  Normalization.evaluate (Continuation.Replanning.native model world) world.entry world.cut rfl
    (controller world fallback program rival) (schedule world fallback program)
abbrev tableEvaluation (program : Program model.source.code) (table : Table world fallback programmes) :=
  actualEvaluation model world fallback program (opponent world fallback programmes table)

variable (program : Program model.source.code) (generated : program ∈ programmes)
  (rival : Opponent model.source.code)

include generated in
theorem one_external_restriction_preserves_the_complete_evaluation :
    tableEvaluation model world fallback programmes program (restrict world fallback programmes rival) =
      actualEvaluation model world fallback program rival := by
  have runs := every_ordinal_state_is_preserved world fallback programmes program generated rival
  apply Transport.full_evaluation_congr (Continuation.Replanning.native model world) world.entry world.cut
    (schedule world fallback program) (schedule world fallback program)
    (controller world fallback program rival)
    (controller world fallback program (representative world fallback programmes rival))
    (fun ordinal _ => Replay.source_events world.source world.entry world.cut
      (schedule world fallback program) (schedule world fallback program)
      (controller world fallback program rival)
      (controller world fallback program (representative world fallback programmes rival)) runs rfl rfl ordinal)
    (runs _) rfl

theorem one_common_table_preserves_two_complete_actual_occurrences
    (relation : Evaluation model.source.code → Evaluation model.source.code → Prop)
    (new old : Program model.source.code) (newInside : new ∈ programmes) (oldInside : old ∈ programmes) :
    (∀ table ∈ tables world fallback programmes,
      relation (tableEvaluation model world fallback programmes new table) (tableEvaluation model world fallback programmes old table)) ↔
    ∀ environment : Opponent model.source.code,
      relation (actualEvaluation model world fallback new environment) (actualEvaluation model world fallback old environment) := by
  constructor
  · intro finite environment
    have checked := finite (restrict world fallback programmes environment)
      (Residual.restriction_is_generated _ _ _ environment)
    rw [one_external_restriction_preserves_the_complete_evaluation model world fallback programmes new newInside environment,
      one_external_restriction_preserves_the_complete_evaluation model world fallback programmes old oldInside environment] at checked
    exact checked
  · intro all table _
    exact all (opponent world fallback programmes table)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Finite

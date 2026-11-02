import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Normalize

set_option autoImplicit false
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.SelfBudget

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private def maximum : List Nat → Nat
  | [] => 0
  | first::rest => max first (maximum rest)

private theorem member_le (values : List Nat) (value : Nat) (inside : value ∈ values) : value ≤ maximum values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at inside
  | cons first rest ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst value;exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def localCap (policy : code.Policy) : Nat :=
  maximum (code.keys.attach.map fun key => (policy key.val key.property).length)

def ruleCap (rule : Rule code) : Nat := (rule.work.map localCap).getD 0

def cap (horizon : Nat) (fallback : Rule code) (program : Program code) : Nat :=
  maximum ((List.range horizon).map fun ordinal => ruleCap (stage code fallback program ordinal))

theorem each_original_cell_is_bounded (policy : code.Policy) (key : code.Key) (inside : key ∈ code.keys) :
    (policy key inside).length ≤ localCap policy :=
  member_le _ _ (List.mem_map.mpr ⟨⟨key,inside⟩,List.mem_attach _ _,rfl⟩)

theorem each_consumed_rule_is_bounded (horizon : Nat) (fallback : Rule code) (program : Program code)
    (ordinal : Nat) (inside : ordinal < horizon) : ruleCap (stage code fallback program ordinal) ≤ cap horizon fallback program :=
  member_le _ _ (List.mem_map.mpr ⟨ordinal,List.mem_range.mpr inside,rfl⟩)

theorem a_sufficient_local_budget_keeps_the_original_policy (policy : code.Policy) (budget : Nat)
    (enough : localCap policy ≤ budget) : Normalization.policy code budget policy = policy := by
  funext key inside
  exact if_pos ((each_original_cell_is_bounded policy key inside).trans enough)

theorem a_sufficient_rule_budget_keeps_the_original_rule (rule : Rule code) (budget : Nat)
    (enough : ruleCap rule ≤ budget) : rule.normalize budget = rule := by
  rcases rule with ⟨work,events⟩
  cases work with
  | none => rfl
  | some policy =>
    change (⟨some (Normalization.policy code budget policy),events⟩ : Rule code) = ⟨some policy,events⟩
    rw [a_sufficient_local_budget_keeps_the_original_policy policy budget enough]

theorem every_consumed_rule_is_exact (horizon : Nat) (fallback : Rule code) (program : Program code)
    (budget : Nat) (enough : cap horizon fallback program ≤ budget)
    (ordinal : Nat) (inside : ordinal < horizon) :
    stage code fallback (normalized budget horizon fallback program) ordinal = stage code fallback program ordinal := by
  rw [normalized_at fallback program budget horizon ordinal inside]
  exact a_sufficient_rule_budget_keeps_the_original_rule _ budget
    ((each_consumed_rule_is_bounded horizon fallback program ordinal inside).trans enough)

variable [DecidableEq Port] [DecidableEq Technology]
  (point : Cursor code) (fallback : Rule code) (program : Program code)
  (horizon budget : Nat) (enoughHorizon : remaining point ≤ horizon) (enoughBudget : cap horizon fallback program ≤ budget)

include enoughHorizon enoughBudget in
theorem every_actual_state_is_preserved (environment : Opponent code) (n : Nat) :
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point fallback (normalized budget horizon fallback program)))
      ⟨controller point fallback (normalized budget horizon fallback program) environment,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n =
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point fallback program))
      ⟨controller point fallback program environment,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n := by
  let old := Residual.scheduleAt point.source point.cut (schedule point fallback program)
  let next := Residual.scheduleAt point.source point.cut (schedule point fallback (normalized budget horizon fallback program))
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Residual.run]
    rw [ih]
    let actual := Residual.run code old ⟨controller point fallback program environment,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n
    change Feedback.advance code (next n) ⟨controller point fallback (normalized budget horizon fallback program) environment,point.entry.budget⟩ actual =
      Feedback.advance code (old n) ⟨controller point fallback program environment,point.entry.budget⟩ actual
    by_cases exhausted : actual.remaining = 0
    · cases next n <;> cases old n <;> simp only [Feedback.advance,word,decision,exhausted,if_pos]
    · have inside : n < remaining point := by
        have left := Residual.remaining_is_the_seed_budget code old
          ⟨controller point fallback program environment,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n
        change actual.remaining = remaining point-n at left
        omega
      have length := Replay.history_length point.source point.entry point.cut (schedule point fallback program)
        (controller point fallback program environment) n
      have decisions := normalized_controller_keeps_each_consumed_decision point fallback program budget horizon n
        (inside.trans_le enoughHorizon) environment actual.history actual.past actual.frame length
      have sameWork : next n = old n := by
        simp only [next,old,Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
        rw [every_consumed_rule_is_exact horizon fallback program budget enoughBudget n (inside.trans_le enoughHorizon)]
      rw [Residual.advance_is_its_actual_choice,Residual.advance_is_its_actual_choice]
      rw [sameWork]
      exact congrArg (fun move => Residual.forced code (old n) move actual) decisions

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code) (raw : Program model.source.code)

abbrev sourceCap := cap (Whole.Complete.horizon domain) original raw
abbrev representative := normalized (sourceCap model domain original raw) (Whole.Complete.horizon domain) original raw

/-- Every finite original program supplies its own exact representative, including zero and dynamic debit. -/
theorem complete_evaluation_is_preserved (world : Replanning.Point model domain) (environment : Opponent model.source.code) :
    Finite.actualEvaluation model world.val original (representative model domain original raw) environment =
      Finite.actualEvaluation model world.val original raw environment := by
  have runs := every_actual_state_is_preserved world.val original raw (Whole.Complete.horizon domain)
    (sourceCap model domain original raw)
    (Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property) (Nat.le_refl _) environment
  exact Transport.full_evaluation_congr (Replanning.native model world.val) world.val.entry world.val.cut
    (schedule world.val original raw) (schedule world.val original (representative model domain original raw))
    (controller world.val original raw environment) (controller world.val original (representative model domain original raw) environment)
    (fun ordinal _ => Replay.source_events world.val.source world.val.entry world.val.cut
      (schedule world.val original raw) (schedule world.val original (representative model domain original raw))
      (controller world.val original raw environment) (controller world.val original (representative model domain original raw) environment)
      runs rfl rfl ordinal) (runs _) rfl

theorem every_supported_representative_is_generated
    (supported : ∀ n < Whole.Complete.horizon domain,(stage model.source.code original raw n).supported) :
    representative model domain original raw ∈ programs model.source.code (sourceCap model domain original raw) (Whole.Complete.horizon domain) :=
  every_supported_normalization_is_generated model.source.code original raw (sourceCap model domain original raw)
    (Whole.Complete.horizon domain) supported

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.SelfBudget

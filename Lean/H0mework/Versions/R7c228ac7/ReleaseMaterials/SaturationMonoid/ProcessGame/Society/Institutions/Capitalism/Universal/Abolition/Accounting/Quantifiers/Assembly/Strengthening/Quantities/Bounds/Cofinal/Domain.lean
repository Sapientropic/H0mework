import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Stages

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → C → Script

/-- The clock is the one on the actual current, even when a policy
continues to submit microsteps forever. -/
def ClockCofinal (source : C) (policy : Policy) : Prop :=
  ∀ time : ℚ, ∃ stage, time ≤ (stageAt source policy stage).raw.clock

structure Paid (source : C) (policy : Policy) (Issue : Nat → C → Script → Type u)
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word)) : Prop where
  allStages : ∀ stage,
    Settled (stageAt source policy stage) (stageBody source policy stage)
  passes : ∀ stage, inspect stage (stageAt source policy stage) (stageBody source policy stage) = none
  time : ClockCofinal source policy

inductive Failure (source : C) (policy : Policy) (Issue : Nat → C → Script → Type u)
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word)) : Prop
  | original (stage : Nat) (issue : Nonempty
      (Obstruction (stageAt source policy stage) (stageBody source policy stage)))
  | requirement (stage : Nat) (issue : ∃ original,
      inspect stage (stageAt source policy stage) (stageBody source policy stage) = some original)
  | boundedClock (bound : ℚ) (bounded : ∀ stage, (stageAt source policy stage).raw.clock < bound)

theorem failure_refutes {source : C} {policy : Policy} {Issue : Nat → C → Script → Type u}
    {inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word)}
    (failure : Failure source policy Issue inspect) : ¬ Paid source policy Issue inspect := by
  intro paid
  cases failure with
  | original stage issue =>
      obtain ⟨original⟩ := issue
      exact original.refutes (paid.allStages stage).toFeasible
  | requirement stage issue =>
      obtain ⟨original, found⟩ := issue
      rw [paid.passes stage] at found
      contradiction
  | boundedClock bound bounded =>
      obtain ⟨stage, reached⟩ := paid.time bound
      exact (not_lt_of_ge reached) (bounded stage)

theorem a_policy_fails_iff_an_actual_stage_or_clock_bound_explains_it
    (source : C) (policy : Policy) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word)) :
    ¬ Paid source policy Issue inspect ↔ Failure source policy Issue inspect := by
  constructor
  · intro fails
    classical
    by_cases stages : ∀ stage, Settled (stageAt source policy stage) (stageBody source policy stage)
    · by_cases passed : ∀ stage, inspect stage (stageAt source policy stage) (stageBody source policy stage) = none
      · have noClock : ¬ ClockCofinal source policy := fun time => fails ⟨stages, passed, time⟩
        obtain ⟨bound, stop⟩ := not_forall.mp noClock
        exact .boundedClock bound fun stage => lt_of_not_ge (fun reached => stop ⟨stage, reached⟩)
      · obtain ⟨stage, stop⟩ := not_forall.mp passed
        cases seen : inspect stage (stageAt source policy stage) (stageBody source policy stage) with
        | none => exact (stop seen).elim
        | some issue => exact .requirement stage ⟨issue, seen⟩
    · obtain ⟨stage, stop⟩ := not_forall.mp stages
      exact .original stage ((infeasible_iff_original_obstruction _ _).mp
        (fun feasible => stop (settle _ _ feasible)))
  · exact failure_refutes

theorem a_paid_stage_writes_the_original_whole_ledger_into_the_next_stage
    (source : C) (policy : Policy) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (paid : Paid source policy Issue inspect) (stage : Nat) :
    Recorded source (stageScript source policy stage) ∧
      Settled (stageAt source policy stage) (stageBody source policy stage) ∧
      stageAt source policy (stage + 1) = endAt (stageAt source policy stage) (stageBody source policy stage) :=
  ⟨(every_stage_retains_all_original_claims_and_generates_its_next source policy stage).1,
    paid.allStages stage, next_stage_is_the_literal_original_next source policy stage⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal

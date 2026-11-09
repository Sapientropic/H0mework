import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Adaptive
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.ExitCounterexample
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Strategy" => History Observation → Word

def stages (origin : C) (read : C → Observation) (strategy : Strategy) (rival : Nat → Word)
    (round : Nat) (_cut : C) : Word :=
  strategy (play origin read strategy rival round).position.seen ++ rival round

theorem stages_are_the_original_play (origin : C) (read : C → Observation) (strategy : Strategy)
    (rival : Nat → Word) (round : Nat) :
    Quantities.Execution.stageScript origin (stages origin read strategy rival) round =
      (play origin read strategy rival round).script := by
  induction round with
  | zero => rfl
  | succ round earlier => simp only [Quantities.Execution.stageScript, play, earlier, stages]

theorem stage_cut_is_the_original_play_cut (origin : C) (read : C → Observation) (strategy : Strategy)
    (rival : Nat → Word) (round : Nat) :
    Quantities.Execution.stageAt origin (stages origin read strategy rival) round =
      (play origin read strategy rival round).position.window.current := by
  rw [Quantities.Execution.stageAt, stages_are_the_original_play, play_is_the_original_execution]

def ProtectsCofinally (origin : C) (command : List Party) (community : Party → Community)
    (read : C → Observation) (strategy : Strategy) : Prop :=
  ProtectsWithExit origin command community read strategy ∧
    ∀ rival, Quantities.Bounds.Cofinal.ClockCofinal origin (stages origin read strategy rival)

/-- A true positive clock quantum upgrades the finite safety contract to
unbounded actual time. No count of refusals is used as elapsed time. -/
theorem a_uniform_original_clock_gain_gives_cofinal_protection
    {origin : C} {command : List Party} {community : Party → Community} {read : C → Observation}
    {strategy : Strategy} (protects : ProtectsWithExit origin command community read strategy)
    (quantum : ℚ) (positive : 0 < quantum)
    (advance : ∀ rival round,
      quantum ≤ (play origin read strategy rival (round + 1)).position.window.current.raw.clock -
        (play origin read strategy rival round).position.window.current.raw.clock) :
    ProtectsCofinally origin command community read strategy := by
  refine ⟨protects, fun rival =>
    Quantities.Bounds.Cofinal.a_positive_paid_clock_quantum_crosses_every_physical_horizon
      origin (stages origin read strategy rival) quantum positive ?_⟩
  intro round
  unfold Quantities.elapsed
  rw [← Quantities.Execution.next_stage_is_the_literal_original_next,
    stage_cut_is_the_original_play_cut, stage_cut_is_the_original_play_cut]
  exact advance rival round

/-- Failure of cofinality can occur even when each finite cut is safe.
Its obstruction names a real clock bound on one original input path. -/
theorem no_cofinal_protection_iff_first_failure_or_a_real_clock_bound
    (origin : C) (command : List Party) (community : Party → Community) (read : C → Observation)
    (strategy : Strategy) :
    ¬ ProtectsCofinally origin command community read strategy ↔
      (Nonempty (Σ rival : List Word, FirstFailureWithExit origin command community read strategy rival)) ∨
      ∃ (rival : Nat → Word) (bound : ℚ), ∀ round,
        (play origin read strategy rival round).position.window.current.raw.clock < bound := by
  classical
  constructor
  · intro denied
    by_cases safe : ProtectsWithExit origin command community read strategy
    · have fails : ¬ ∀ rival, Quantities.Bounds.Cofinal.ClockCofinal origin
          (stages origin read strategy rival) := fun time => denied ⟨safe, time⟩
      obtain ⟨rival, clock⟩ := not_forall.mp fails
      obtain ⟨bound, unavailable⟩ := not_forall.mp clock
      refine Or.inr ⟨rival, bound, fun round => lt_of_not_ge fun reached => unavailable ⟨round, ?_⟩⟩
      rwa [stage_cut_is_the_original_play_cut]
    · exact Or.inl (a_failed_contract_has_an_original_first_counterexample (RequiresExit origin command community)
        (FailureWithExit origin command community) (inspectWithExit origin command community) safe)
  · rintro (⟨⟨rival, issue⟩⟩ | ⟨rival, bound, below⟩) cofinal
    · exact issue.failure.refutes (cofinal.1 (submitted rival) issue.round)
    · obtain ⟨round, enough⟩ := cofinal.2 rival bound
      rw [stage_cut_is_the_original_play_cut] at enough
      exact (not_lt_of_ge enough) (below round)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

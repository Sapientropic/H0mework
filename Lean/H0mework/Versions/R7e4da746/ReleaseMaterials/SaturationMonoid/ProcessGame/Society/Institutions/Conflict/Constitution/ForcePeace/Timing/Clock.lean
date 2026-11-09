import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Timing.Ordinal
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Quantities.Execution (endAt the_actual_script_never_runs_the_clock_backwards)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument

variable {origin : Root.Cut Party Good Port Technology Instrument} {command : List Party}
  {community : Party → Community} {window : Window Party Good Port Technology Instrument} {mode : WaitingDomain}

def WaitBreach.clock (breach : WaitBreach origin command community window mode) : ℚ :=
  let here := window.run breach.before
  match breach.issue with
  | .attack _ | .signature .. | .material .. => here.current.raw.clock
  | .standing .. | .missedDeadline .. | .shortage .. => (here.nextCut breach.input).raw.clock

def WaitBreach.position (breach : WaitBreach origin command community window mode) : Nat :=
  match breach.issue with
  | .attack damage => damage.position.val
  | .signature .. | .material .. => 0
  | .standing .. | .missedDeadline .. | .shortage .. =>
      (Boundary.Actual.items (window.run breach.before).current breach.input).length

theorem WaitBreach.clock_is_after_the_original_source (breach : WaitBreach origin command community window mode) :
    window.current.raw.clock ≤ breach.clock := by
  have current : window.current.raw.clock ≤ (window.run breach.before).current.raw.clock := by
    rw [Window.run_current]
    exact the_actual_script_never_runs_the_clock_backwards _ _
  have next : (window.run breach.before).current.raw.clock ≤
      ((window.run breach.before).nextCut breach.input).raw.clock :=
    the_actual_script_never_runs_the_clock_backwards _ [breach.input]
  rcases breach with ⟨before, input, permitted, issue⟩
  cases issue <;> first | exact current | exact current.trans next

variable (origin : Root.Cut Party Good Port Technology Instrument) (command : List Party) (community : Party → Community)
  (window : Window Party Good Port Technology Instrument) (mode : WaitingDomain)

def obstructionClocks : Set ℝ :=
  Set.range fun breach : WaitBreach origin command community window mode => (breach.clock : ℝ)

theorem the_original_source_bounds_all_obstruction_clocks :
    BddBelow (obstructionClocks origin command community window mode) := by
  refine ⟨(window.current.raw.clock : ℝ), ?_⟩
  rintro time ⟨breach, rfl⟩
  change (window.current.raw.clock : ℝ) ≤ (breach.clock : ℝ)
  exact_mod_cast breach.clock_is_after_the_original_source

/-- When a physical bound is finite it is the lower envelope of the real
obstruction clocks. The envelope may be approached by distinct histories. -/
theorem the_original_clock_envelope_is_tight
    (reached : Nonempty (WaitBreach origin command community window mode)) :
    let bound := sInf (obstructionClocks origin command community window mode)
    (∀ breach : WaitBreach origin command community window mode, bound ≤ (breach.clock : ℝ)) ∧
    ∀ tolerance : ℝ, 0 < tolerance → ∃ breach : WaitBreach origin command community window mode,
      (breach.clock : ℝ) < bound + tolerance := by
  let clocks := obstructionClocks origin command community window mode
  let bound := sInf clocks
  have nonempty : clocks.Nonempty := by
    obtain ⟨breach⟩ := reached
    exact ⟨_, breach, rfl⟩
  refine ⟨fun breach => csInf_le (the_original_source_bounds_all_obstruction_clocks _ _ _ _ _) ⟨breach, rfl⟩, ?_⟩
  intro tolerance positive
  by_contra absent
  have lower : bound + tolerance ≤ bound :=
    le_csInf nonempty (by
      rintro _ ⟨breach, rfl⟩
      exact le_of_not_gt (fun closer => absent ⟨breach, closer⟩))
  linarith

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

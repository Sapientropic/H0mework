import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Ordinal
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (allowed : Position Party Good Port Technology Instrument CivilView OpponentView →
    Turn → Reparation.Actual.Input Party Good Port Technology Instrument → Prop)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)

local notation "Hit" => game.JointBreach allowed plan

def jointObstructionClocks : Set ℝ :=
  Set.range fun breach : Hit => (breach.clock : ℝ)

abbrev jointClockBound : ℝ := sInf (game.jointObstructionClocks allowed plan)

theorem the_submission_clock_bounds_all_joint_obstruction_clocks :
    BddBelow (game.jointObstructionClocks allowed plan) := by
  refine ⟨((endAt game.seed game.past).raw.clock : ℝ), ?_⟩
  rintro time ⟨breach, rfl⟩
  change ((endAt game.seed game.past).raw.clock : ℝ) ≤ (breach.clock : ℝ)
  exact_mod_cast breach.clock_is_after_submission

theorem joint_clock_bound_is_tight (found : Nonempty Hit) :
    let bound := game.jointClockBound allowed plan
    (∀ breach : Hit, bound ≤ (breach.clock : ℝ)) ∧
      ∀ tolerance : ℝ, 0 < tolerance → ∃ breach : Hit, (breach.clock : ℝ) < bound + tolerance := by
  let bound := game.jointClockBound allowed plan
  have clocks : (game.jointObstructionClocks allowed plan).Nonempty := by
    obtain ⟨breach⟩ := found
    exact ⟨_, breach, rfl⟩
  refine ⟨fun breach => csInf_le (game.the_submission_clock_bounds_all_joint_obstruction_clocks allowed plan)
    ⟨breach, rfl⟩, ?_⟩
  intro tolerance positive
  by_contra absent
  have lower : bound + tolerance ≤ bound := le_csInf clocks (by
    rintro _ ⟨breach, rfl⟩
    exact le_of_not_gt (fun closer => absent ⟨breach, closer⟩))
  linarith

abbrev JointFirstAtClock (clock : ℝ) :=
  FirstVisitItem Hit (fun breach => (breach.clock : ℝ) = clock) JointBreach.visit JointBreach.position

inductive JointClockFrontier
  | unbounded (none : IsEmpty Hit)
  | approached (strict : ∀ breach : Hit, game.jointClockBound allowed plan < (breach.clock : ℝ))
      (near : ∀ tolerance : ℝ, 0 < tolerance →
        ∃ breach : Hit, (breach.clock : ℝ) < game.jointClockBound allowed plan + tolerance)
  | attained (first : game.JointFirstAtClock allowed plan (game.jointClockBound allowed plan))
      (lower : ∀ breach : Hit, game.jointClockBound allowed plan ≤ (breach.clock : ℝ))

def jointClockFrontier : game.JointClockFrontier allowed plan := by
  classical
  by_cases found : Nonempty Hit
  · let bound := game.jointClockBound allowed plan
    have tight := game.joint_clock_bound_is_tight allowed plan found
    by_cases attained : ∃ breach : Hit, (breach.clock : ℝ) = bound
    · exact .attained (firstVisitItem JointBreach.visit JointBreach.position attained) tight.1
    · exact .approached (fun breach => lt_of_le_of_ne (tight.1 breach)
        (fun equal => attained ⟨breach, equal.symm⟩)) tight.2
  · exact .unbounded ⟨fun breach => found ⟨breach⟩⟩

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

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
local notation "bound" => game.jointClockBound allowed plan

/-- Equality is the last boundary at which the endangered slot can be
addressed. The visit counts the original prefix, including inherited inputs. -/
def JointSafeBoundary (time : ℝ) (visit position : Nat) : Prop :=
  ∀ breach : Hit, time < (breach.clock : ℝ) ∨ time = (breach.clock : ℝ) ∧
    (visit < breach.visit ∨ visit = breach.visit ∧ position ≤ breach.position)

theorem unsafe_joint_boundary_has_an_earlier_actual_breach (time : ℝ) (visit position : Nat) :
    ¬ game.JointSafeBoundary allowed plan time visit position ↔
      ∃ breach : Hit, (breach.clock : ℝ) < time ∨ time = (breach.clock : ℝ) ∧
        (breach.visit < visit ∨ breach.visit = visit ∧ breach.position < position) := by
  classical
  constructor
  · intro deniedBoundary
    obtain ⟨breach, denied⟩ := not_forall.mp deniedBoundary
    refine ⟨breach, ?_⟩
    rcases lt_trichotomy time (breach.clock : ℝ) with before | same | after
    · exact (denied (.inl before)).elim
    · right
      refine ⟨same, ?_⟩
      rcases lt_trichotomy visit breach.visit with before | tied | after
      · exact (denied (.inr ⟨same, .inl before⟩)).elim
      · exact .inr ⟨tied.symm, lt_of_not_ge (fun earlier => denied (.inr ⟨same, .inr ⟨tied, earlier⟩⟩))⟩
      · exact .inl after
    · exact .inl after
  · rintro ⟨breach, bad⟩ safe
    rcases bad with before | ⟨same, before⟩
    · rcases safe breach with later | ⟨same, _⟩
      · exact (not_lt_of_ge before.le) later
      · exact (ne_of_gt before) same
    · rcases safe breach with later | ⟨_, later⟩
      · exact (ne_of_lt later) same
      · rcases before with earlyVisit | ⟨earlyVisit, earlyPosition⟩
        · rcases later with lateVisit | ⟨lateVisit, _⟩
          · exact (not_lt_of_ge earlyVisit.le) lateVisit
          · exact (ne_of_gt earlyVisit) lateVisit
        · rcases later with lateVisit | ⟨_, latePosition⟩
          · exact (ne_of_gt lateVisit) earlyVisit
          · exact (not_le_of_gt earlyPosition) latePosition

theorem every_boundary_strictly_before_the_joint_clock_is_safe (found : Nonempty Hit)
    (time : ℝ) (visit position : Nat) (earlier : time < bound) :
    game.JointSafeBoundary allowed plan time visit position :=
  fun breach => .inl (earlier.trans_le ((game.joint_clock_bound_is_tight allowed plan found).1 breach))

theorem every_boundary_strictly_after_the_joint_clock_has_a_breach (found : Nonempty Hit)
    (time : ℝ) (visit position : Nat) (later : bound < time) :
    ¬ game.JointSafeBoundary allowed plan time visit position := by
  apply (game.unsafe_joint_boundary_has_an_earlier_actual_breach allowed plan time visit position).mpr
  obtain ⟨breach, near⟩ := (game.joint_clock_bound_is_tight allowed plan found).2 (time - bound) (sub_pos.mpr later)
  exact ⟨breach, .inl (by linarith)⟩

theorem the_unattained_joint_clock_is_safe_at_every_position (visit position : Nat)
    (strict : ∀ breach : Hit, bound < (breach.clock : ℝ)) :
    game.JointSafeBoundary allowed plan bound visit position :=
  fun breach => .inl (strict breach)

theorem the_attained_joint_clock_ends_at_its_first_original_visit_and_item
    (first : game.JointFirstAtClock allowed plan bound)
    (lower : ∀ breach : Hit, bound ≤ (breach.clock : ℝ)) (visit position : Nat) :
    game.JointSafeBoundary allowed plan bound visit position ↔
      visit < first.breach.visit ∨ visit = first.breach.visit ∧ position ≤ first.breach.position := by
  constructor
  · intro safe
    rcases safe first.breach with before | atClock
    · exact (not_lt_of_ge (le_of_eq first.belongs)) before |>.elim
    · exact atClock.2
  · intro byAddress breach
    by_cases same : (breach.clock : ℝ) = bound
    · right
      refine ⟨same.symm, ?_⟩
      have earlier := first.firstVisit breach same
      rcases byAddress with before | ⟨sameVisit, before⟩
      · exact .inl (before.trans_le earlier)
      · rcases lt_or_eq_of_le earlier with later | atVisit
        · exact .inl (by rw [sameVisit]; exact later)
        · exact .inr ⟨sameVisit.trans atVisit, before.trans (first.firstItem breach same atVisit.symm)⟩
    · exact .inl (lt_of_le_of_ne (lower breach) (Ne.symm same))

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Timing.Contact

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

variable {origin : Root.Cut Party Good Port Technology Instrument} {command : List Party}
  {community : Party → Community} {window : Window Party Good Port Technology Instrument} {mode : WaitingDomain}

local notation "Hit" => WaitBreach origin command community window mode

/-- This boundary is the last place to replace a competing dispatch.
Equality permits replacement at the first threatened material slot. -/
def SafeBoundary (time : ℝ) (visit position : Nat) : Prop :=
  ∀ breach : Hit, time < (breach.clock : ℝ) ∨ (time = (breach.clock : ℝ) ∧
    (visit < breach.before.length ∨ visit = breach.before.length ∧ position ≤ breach.position))

theorem every_boundary_before_the_clock_envelope_is_safe {bound time : ℝ} (visit position : Nat)
    (lower : ∀ breach : Hit, bound ≤ (breach.clock : ℝ)) (earlier : time < bound) :
    SafeBoundary (origin := origin) (command := command) (community := community)
      (window := window) (mode := mode) time visit position :=
  fun breach => .inl (earlier.trans_le (lower breach))

theorem every_boundary_after_the_clock_envelope_has_an_actual_earlier_breach {bound time : ℝ}
    (near : ∀ tolerance : ℝ, 0 < tolerance → ∃ breach : Hit, (breach.clock : ℝ) < bound + tolerance)
    (later : bound < time) :
    ∃ breach : Hit, (breach.clock : ℝ) < time := by
  obtain ⟨breach, before⟩ := near (time - bound) (sub_pos.mpr later)
  exact ⟨breach, by linarith⟩

theorem the_attained_clock_boundary_is_exactly_the_first_original_visit_and_item {bound : ℝ}
    (first : FirstAtClock (origin := origin) (command := command) (community := community)
      (window := window) (mode := mode) bound)
    (lower : ∀ breach : Hit, bound ≤ (breach.clock : ℝ)) (visit position : Nat) :
    SafeBoundary (origin := origin) (command := command) (community := community)
      (window := window) (mode := mode) bound visit position ↔
      visit < first.breach.before.length ∨ visit = first.breach.before.length ∧ position ≤ first.breach.position := by
  constructor
  · intro safe
    rcases safe first.breach with before | atTime
    · have impossible : bound < bound := by simpa only [first.atClock] using before
      exact (lt_irrefl bound impossible).elim
    · exact atTime.2
  · intro byPosition breach
    by_cases same : (breach.clock : ℝ) = bound
    · right
      refine ⟨same.symm, ?_⟩
      have earlier := first.firstVisit breach same
      rcases byPosition with visitEarlier | ⟨visitSame, positionEarlier⟩
      · exact .inl (visitEarlier.trans_le earlier)
      · rcases lt_or_eq_of_le earlier with later | atVisit
        · exact .inl (by rw [visitSame]; exact later)
        · exact .inr ⟨visitSame.trans atVisit, positionEarlier.trans (first.firstItem breach same atVisit.symm)⟩
    · exact .inl (lt_of_le_of_ne (lower breach) (Ne.symm same))

theorem the_unattained_clock_boundary_is_safe_at_every_position {bound : ℝ}
    (lower : ∀ breach : Hit, bound < (breach.clock : ℝ)) (visit position : Nat) :
    SafeBoundary (origin := origin) (command := command) (community := community)
      (window := window) (mode := mode) bound visit position :=
  fun breach => .inl (lower breach)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

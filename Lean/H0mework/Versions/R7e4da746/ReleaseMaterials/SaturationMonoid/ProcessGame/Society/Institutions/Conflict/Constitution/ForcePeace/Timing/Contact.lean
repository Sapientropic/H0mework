import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Timing.Clock

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

/-- Physical time ties are broken by the original visit and material
position, both read from the same native witness. -/
structure FirstAtClock (clock : ℝ) where
  breach : Hit
  atClock : (breach.clock : ℝ) = clock
  firstVisit : ∀ other : Hit, (other.clock : ℝ) = clock → breach.before.length ≤ other.before.length
  firstItem : ∀ other : Hit, (other.clock : ℝ) = clock → other.before.length = breach.before.length →
    breach.position ≤ other.position

def firstAtClock {clock : ℝ} (attained : ∃ breach : Hit, (breach.clock : ℝ) = clock) :
    FirstAtClock (origin := origin) (command := command) (community := community) (window := window)
      (mode := mode) clock := by
  classical
  let hasVisit (tick : Nat) := ∃ breach : Hit, (breach.clock : ℝ) = clock ∧ breach.before.length = tick
  have visit : ∃ tick, hasVisit tick := by
    obtain ⟨breach, atClock⟩ := attained
    exact ⟨breach.before.length, breach, atClock, rfl⟩
  let tick := Nat.find visit
  let hasItem (item : Nat) := ∃ breach : Hit,
    ((breach.clock : ℝ) = clock ∧ breach.before.length = tick) ∧ breach.position = item
  have item : ∃ pos, hasItem pos := by
    obtain ⟨breach, exact⟩ := Nat.find_spec visit
    exact ⟨breach.position, breach, exact, rfl⟩
  let breach := Classical.choose (Nat.find_spec item)
  obtain ⟨⟨atClock, atVisit⟩, atItem⟩ := Classical.choose_spec (Nat.find_spec item)
  refine ⟨breach, atClock, ?_, ?_⟩
  · intro other sameClock
    exact atVisit.trans_le (Nat.find_min' visit (show hasVisit other.before.length from ⟨other, sameClock, rfl⟩))
  · intro other sameClock sameVisit
    exact atItem.trans_le (Nat.find_min' item
      (show hasItem other.position from ⟨other, ⟨sameClock, sameVisit.trans atVisit⟩, rfl⟩))

inductive ClockFrontier
  | noBreach (all : IsEmpty Hit)
  | approached (bound : ℝ) (strict : ∀ breach : Hit, bound < (breach.clock : ℝ))
      (near : ∀ tolerance : ℝ, 0 < tolerance → ∃ breach : Hit, (breach.clock : ℝ) < bound + tolerance)
  | attained (bound : ℝ) (earliest : FirstAtClock (origin := origin) (command := command)
      (community := community) (window := window) (mode := mode) bound)
      (safeEarlier : ∀ breach : Hit, bound ≤ (breach.clock : ℝ))

/-- Choose the exact safety frontier of the actual source. At a clock
limit with no first item, every larger tolerance has an original witness. -/
def clockFrontier :
    ClockFrontier (origin := origin) (command := command) (community := community) (window := window) (mode := mode) := by
  classical
  by_cases found : Nonempty Hit
  · let bound := sInf (obstructionClocks origin command community window mode)
    have envelope := the_original_clock_envelope_is_tight origin command community window mode found
    by_cases attained : ∃ breach : Hit, (breach.clock : ℝ) = bound
    · exact .attained bound (firstAtClock attained) envelope.1
    · exact .approached bound (fun breach => lt_of_le_of_ne (envelope.1 breach) (fun equal => attained ⟨breach, equal.symm⟩)) envelope.2
  · exact .noBreach ⟨fun breach => found ⟨breach⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

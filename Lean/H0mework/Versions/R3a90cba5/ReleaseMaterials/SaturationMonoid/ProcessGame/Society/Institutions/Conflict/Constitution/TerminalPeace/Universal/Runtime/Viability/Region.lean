import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Path

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)

def ReachesAt (region : Raw → Prop) (bound : ℚ) (raw : Raw) (length : Nat) : Prop :=
  ∃ finish, Nonempty (Path input origin roster raw length finish) ∧ region finish ∧ bound < finish.clock

def Postfixed (region : Raw → Prop) : Prop :=
  ∀ raw, region raw → ∀ bound, ∃ length, ReachesAt input origin roster region bound raw length

/-- The union of all regions that can return to themselves beyond any
finite original-clock bound. Membership supplies no preselected path. -/
def Live (raw : Raw) : Prop :=
  ∃ region, Postfixed input origin roster region ∧ region raw

variable {input origin roster} {raw : RawCurrent Party Good Technology Instrument}

theorem Live.reaches (live : Live input origin roster raw) (bound : ℚ) :
    ∃ length, ReachesAt input origin roster (Live input origin roster) bound raw length := by
  obtain ⟨region, again, atRaw⟩ := live
  obtain ⟨length, finish, path, inside, beyond⟩ := again raw atRaw bound
  exact ⟨length, finish, path, ⟨region, again, inside⟩, beyond⟩

theorem live_iff_reaches_live_at_every_bound :
    Live input origin roster raw ↔
      ∀ bound, ∃ length, ReachesAt input origin roster (Live input origin roster) bound raw length := by
  refine ⟨Live.reaches, fun reaches => ?_⟩
  let region : Raw → Prop := fun current => Live input origin roster current ∨ current = raw
  refine ⟨region, ?_, Or.inr rfl⟩
  intro current inside bound
  have available : ∃ length, ReachesAt input origin roster (Live input origin roster) bound current length := by
    rcases inside with live | same
    · exact live.reaches bound
    · subst current
      exact reaches bound
  obtain ⟨length, finish, path, live, beyond⟩ := available
  exact ⟨length, finish, path, Or.inl live, beyond⟩

theorem Live.before_move (move : Move input origin roster raw)
    (later : Live input origin roster move.next) : Live input origin roster raw := by
  apply live_iff_reaches_live_at_every_bound.mpr
  intro bound
  obtain ⟨length, finish, ⟨tail⟩, live, beyond⟩ := later.reaches bound
  exact ⟨length + 1, finish, ⟨.cons move tail⟩, live, beyond⟩

theorem Live.before_path {finish : Raw} {length : Nat}
    (path : Path input origin roster raw length finish)
    (later : Live input origin roster finish) : Live input origin roster raw := by
  induction path with
  | nil => exact later
  | cons move _ early => exact Live.before_move move (early later)

theorem Trajectory.every_actual_state_is_live (trajectory : Trajectory input origin roster raw)
    (ordinal : Nat) : Live input origin roster (trajectory.state ordinal) := by
  let region : Raw → Prop := fun current => ∃ n, trajectory.state n = current
  refine ⟨region, ?_, ⟨ordinal, rfl⟩⟩
  intro current inside bound
  obtain ⟨cut, rfl⟩ := inside
  obtain ⟨later, after, beyond⟩ := trajectory.cofinal cut bound
  have exactLength := Nat.add_sub_of_le after
  have path := trajectory.segment cut (later - cut)
  rw [exactLength] at path
  exact ⟨later - cut, trajectory.state later, ⟨path⟩, ⟨later, rfl⟩, beyond⟩

theorem Trajectory.initial_is_live (trajectory : Trajectory input origin roster raw) :
    Live input origin roster raw := by
  rw [← trajectory.initial]
  exact trajectory.every_actual_state_is_live 0

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

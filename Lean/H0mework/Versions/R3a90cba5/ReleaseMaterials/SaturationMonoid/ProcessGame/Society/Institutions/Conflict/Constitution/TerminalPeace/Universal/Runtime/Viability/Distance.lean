import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Region
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument} {roster : List Party}
  {raw : RawCurrent Party Good Technology Instrument}

/-- Count actual paid words until a live endpoint above this bound.
This is a mathematical minimum on a reachable fibre. -/
def Live.distance (live : Live input origin roster raw) (bound : ℚ) : Nat := by
  classical
  exact Nat.find (live.reaches bound)

theorem Live.distance_reaches (live : Live input origin roster raw) (bound : ℚ) :
    ReachesAt input origin roster (Live input origin roster) bound raw (live.distance bound) := by
  classical
  exact Nat.find_spec (live.reaches bound)

theorem Live.distance_le (live : Live input origin roster raw) {bound : ℚ} {length : Nat}
    (actual : ReachesAt input origin roster (Live input origin roster) bound raw length) :
    live.distance bound ≤ length := by
  classical
  exact Nat.find_min' (live.reaches bound) actual

structure Step (live : Live input origin roster raw) (bound : ℚ) where
  move : Move input origin roster raw
  retains : Live input origin roster move.next
  spendsOne : retains.distance bound + 1 = live.distance bound

/-- Select the first actual move of a shortest viable segment. The
remainder is checked against the same clock target. -/
def Live.chooseStep (live : Live input origin roster raw) (bound : ℚ)
    (unreached : raw.clock ≤ bound) : Step live bound := by
  apply Classical.choice
  obtain ⟨finish, ⟨path⟩, there, beyond⟩ := live.distance_reaches bound
  generalize shortest : live.distance bound = length at path
  cases path with
  | nil =>
    exact ((not_lt_of_ge unreached) beyond).elim
  | @cons _ _ length move tail =>
    have nextLive := Live.before_path tail there
    have tailDistance : nextLive.distance bound ≤ length :=
      nextLive.distance_le ⟨finish, ⟨tail⟩, there, beyond⟩
    have joined : live.distance bound ≤ nextLive.distance bound + 1 := by
      obtain ⟨target, ⟨remainder⟩, retained, passed⟩ := nextLive.distance_reaches bound
      exact live.distance_le ⟨target, ⟨.cons move remainder⟩, retained, passed⟩
    exact ⟨⟨move, nextLive, by omega⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

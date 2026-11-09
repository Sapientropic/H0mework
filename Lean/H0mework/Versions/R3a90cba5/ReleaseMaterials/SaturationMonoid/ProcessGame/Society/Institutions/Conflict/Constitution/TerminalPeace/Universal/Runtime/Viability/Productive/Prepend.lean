import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Region

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw : RawCurrent Party Good Technology Instrument} {roster : List Party}

def Trajectory.prepend (first : Move input origin roster raw)
    (later : Trajectory input origin roster first.next) : Trajectory input origin roster raw where
  state := fun | 0 => raw | n + 1 => later.state n
  initial := rfl
  move := fun | 0 => first | n + 1 => later.move n
  next_eq := fun | 0 => later.initial | n + 1 => later.next_eq n
  cofinal := by
    intro cut bound
    obtain ⟨n, after, beyond⟩ := later.cofinal cut bound
    exact ⟨n + 1, after.trans (Nat.le_succ n), beyond⟩

def Trajectory.firstMove (route : Trajectory input origin roster raw) :
    Move input origin roster raw where
  word := (route.move 0).word
  registered := (congrArg (fun current => Supply.Registered input current (route.move 0).word)
    route.initial).mp (route.move 0).registered
  paid := (congrArg (fun current => Supply.Period input origin current roster (route.move 0).word)
    route.initial).mp (route.move 0).paid
  personal := (congrArg (fun current => ∀ person ∈ roster, ∃ word,
    Supply.Registered input current word ∧ Supply.Period input origin current [person] word)
    route.initial).mp (route.move 0).personal

theorem Trajectory.firstMove_next (route : Trajectory input origin roster raw) :
    route.firstMove.next = route.state 1 := by
  rw [route.next_eq 0]
  exact congrArg (fun current => input.law.next current (route.move 0).word) route.initial.symm

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

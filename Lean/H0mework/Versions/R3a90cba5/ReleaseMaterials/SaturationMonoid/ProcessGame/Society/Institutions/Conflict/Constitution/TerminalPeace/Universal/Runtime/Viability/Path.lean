import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Unbounded

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)

/-- A move reads one finite registered word and its actual paid period.
Every original person also has a registered personal period at that cut. -/
structure Move (raw : RawCurrent Party Good Technology Instrument) where
  word : RawEvent Party Good Port Technology Instrument
  registered : Supply.Registered input raw word
  paid : Supply.Period input origin raw roster word
  personal : ∀ person ∈ roster, ∃ word, Supply.Registered input raw word ∧
    Supply.Period input origin raw [person] word

namespace Move

variable {input origin roster} {raw : RawCurrent Party Good Technology Instrument} (move : Move input origin roster raw)

def next : RawCurrent Party Good Technology Instrument := input.law.next raw move.word

theorem clock_advances : raw.clock < move.next.clock := by
  change raw.clock < raw.clock + max 0 (input.law.duration raw)
  rw [max_eq_right move.paid.positiveClock.le]
  exact lt_add_of_pos_right _ move.paid.positiveClock

end Move

inductive Path : RawCurrent Party Good Technology Instrument → Nat → RawCurrent Party Good Technology Instrument → Type
  | nil (raw : RawCurrent Party Good Technology Instrument) : Path raw 0 raw
  | cons {raw finish : RawCurrent Party Good Technology Instrument} {length : Nat} (move : Move input origin roster raw)
      (rest : Path move.next length finish) : Path raw (length + 1) finish

namespace Path

variable {input origin roster} {raw finish : RawCurrent Party Good Technology Instrument} {length : Nat}

def snoc : {raw finish : RawCurrent Party Good Technology Instrument} → {length : Nat} →
    (path : Path input origin roster raw length finish) →
    (move : Move input origin roster finish) → Path input origin roster raw (length + 1) move.next
  | _, _, _, .nil _, move => .cons move (.nil _)
  | _, _, _, .cons first rest, move => .cons first (snoc rest move)

theorem clock_never_decreases (path : Path input origin roster raw length finish) :
    raw.clock ≤ finish.clock := by
  induction path with
  | nil => exact le_rfl
  | cons first _ later => exact first.clock_advances.le.trans later

end Path

/-- The source successor at every ordinal is fixed by the word at that
ordinal. Cofinality concerns the original physical clock. -/
structure Trajectory (start : RawCurrent Party Good Technology Instrument) where
  state : Nat → RawCurrent Party Good Technology Instrument
  initial : state 0 = start
  move : (ordinal : Nat) → Move input origin roster (state ordinal)
  next_eq : ∀ ordinal, state (ordinal + 1) = (move ordinal).next
  cofinal : ∀ cut (bound : ℚ), ∃ ordinal ≥ cut, bound < (state ordinal).clock

namespace Trajectory

variable {input origin roster} {start : RawCurrent Party Good Technology Instrument}
  (trajectory : Trajectory input origin roster start)

def segment (cut : Nat) : (length : Nat) →
    Path input origin roster (trajectory.state cut) length (trajectory.state (cut + length))
  | 0 => by simpa only [Nat.add_zero] using
      (Path.nil (input := input) (origin := origin) (roster := roster) (trajectory.state cut))
  | length + 1 =>
    let move := trajectory.move (cut + length)
    let arrives : trajectory.state (cut + (length + 1)) = move.next :=
      (congrArg trajectory.state (Nat.add_assoc cut length 1).symm).trans (trajectory.next_eq (cut + length))
    arrives.symm ▸ (segment cut length).snoc move

end Trajectory

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

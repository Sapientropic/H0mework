import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Replay
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin current : RawCurrent Party Good Technology Instrument}
  {roster : List Party} {word : RawEvent Party Good Port Technology Instrument}
  (paid : Period input origin current roster word)
  (timing : input.law.TimeIndependent) (reserveLaw : input.law.ReserveInsensitive)
  (accumulating : Balance.FiniteChecks .accumulating input.law current word)
  (quantum : ℚ) (positive : 0 < quantum)
  (sourceClock : ∀ (reserve : Party → Good → ℚ), (∀ person good, 0 ≤ reserve person good) →
    ∀ clock round, quantum ≤ input.law.duration ((current.addReserve reserve).retime clock round))

include paid timing reserveLaw accumulating positive sourceClock

theorem Period.replay_clock_bound (n : Nat) :
    current.clock + (n : ℚ) * quantum ≤ ((repeatPeriod input current word).currentAt n).clock := by
  induction n with
  | zero => simp [RawProgram.currentAt, repeatPeriod]
  | succ n earlier =>
    let reached := (repeatPeriod input current word).currentAt n
    have bound : quantum ≤ input.law.duration reached :=
      (paid.replay timing reserveLaw accumulating quantum positive sourceClock n).2.2.2.2.1
    have advance := bound.trans (le_max_right 0 (input.law.duration reached))
    change current.clock + ((n + 1 : Nat) : ℚ) * quantum ≤
      reached.clock + max 0 (input.law.duration reached)
    push_cast
    linarith only [earlier, advance]

/-- The clock is cofinal on the generated production path. The lower
bound is a local law on its material fibre, independent of future payments. -/
theorem Period.replay_passes_every_real_horizon (horizon : ℚ) :
    ∃ n, horizon < ((repeatPeriod input current word).currentAt n).clock := by
  obtain ⟨n, reaches⟩ := exists_nat_gt ((horizon - current.clock) / quantum)
  have actual := paid.replay_clock_bound timing reserveLaw accumulating quantum positive sourceClock n
  have strict := (div_lt_iff₀ positive).mp reaches
  exact ⟨n, by linarith only [actual, strict]⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

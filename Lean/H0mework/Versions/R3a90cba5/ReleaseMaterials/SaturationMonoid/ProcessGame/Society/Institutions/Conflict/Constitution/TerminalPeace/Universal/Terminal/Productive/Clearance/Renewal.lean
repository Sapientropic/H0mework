import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Productive.Accumulation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Move

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw : RawCurrent Party Good Technology Instrument} {roster : List Party}

/-- The registered words survive nonnegative changes to their own stock
coordinates with the original technology, claims and clock law. -/
def RegistrationOnReserves (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (raw : RawCurrent Party Good Technology Instrument) : Prop :=
  ∀ (extra : Party → Good → ℚ), (∀ payer good, 0 ≤ extra payer good) →
    ∀ clock round word, Supply.Registered input raw word →
      Supply.Registered input ((raw.addReserve extra).retime clock round) word

variable (move : Move input origin roster raw) {quantum : ℚ} (law : move.AccumulationLaw quantum)
  (extra : Party → Good → ℚ) (nonnegative : ∀ payer good, 0 ≤ extra payer good)
  (clock : ℚ) (round : Nat)

local notation "Start" => RawCurrent.retime (raw.addReserve extra) clock round
local notation "Replay" => RawProgram.currentAt (repeatPeriod input Start move.word)

include law nonnegative

private theorem replay_preserves_the_restored_opening (n : Nat) :
    ∃ tick visit, Replay n =
      (raw.addReserve (fun person good => move.earnedReserve n person good + extra person good)).retime tick visit := by
  have actual := Balance.checked_productive_period input.law raw move.word law.accumulating
  induction n with
  | zero =>
    refine ⟨clock, round, ?_⟩
    change Start = _
    simp only [earnedReserve, accumulatedReserve, zero_add]
  | succ n older =>
    obtain ⟨tick, visit, exactCut⟩ := older
    let stock := fun person good => move.earnedReserve n person good + extra person good
    have stocked (person : Party) (good : Good) : 0 ≤ stock person good :=
      add_nonneg (accumulatedReserve_nonnegative _ actual.2 n person good) (nonnegative person good)
    refine ⟨tick + max 0 (input.law.duration ((raw.addReserve stock).retime tick visit)), visit + 1, ?_⟩
    change input.law.next (Replay n) move.word = _
    rw [exactCut, next_of_productive_period input law.timing law.reserve raw move.word _ actual.1
      (fun item listed => (move.paid.own item listed).valid) stock stocked tick visit]
    simp only [stock, earnedReserve, accumulatedReserve, add_assoc]

private theorem paid_after_restoring (stable : RegistrationOnReserves input raw) (n : Nat) :
    (∀ word, Supply.Registered input raw word → Supply.Registered input (Replay n) word) ∧
    Supply.Period input origin (Replay n) roster move.word ∧
    (∀ person ∈ roster, ∃ word, Supply.Registered input (Replay n) word ∧
      Supply.Period input origin (Replay n) [person] word) ∧ quantum ≤ input.law.duration (Replay n) := by
  have actual := Balance.checked_productive_period input.law raw move.word law.accumulating
  obtain ⟨tick, visit, reached⟩ := replay_preserves_the_restored_opening move law extra nonnegative clock round n
  let stock := fun person good => move.earnedReserve n person good + extra person good
  have stocked (person : Party) (good : Good) : 0 ≤ stock person good :=
    add_nonneg (accumulatedReserve_nonnegative _ actual.2 n person good) (nonnegative person good)
  rw [reached]
  have duration := law.duration stock stocked tick visit
  have advances := law.positive.trans_le duration
  refine ⟨stable stock stocked tick visit,
    move.paid.after_reserve_and_clock law.timing law.reserve stock stocked tick visit advances, ?_, duration⟩
  intro person listed
  obtain ⟨word, original, paid⟩ := move.personal person listed
  exact ⟨word, stable stock stocked tick visit word original,
    paid.after_reserve_and_clock law.timing law.reserve stock stocked tick visit advances⟩

/-- Reparation may move stock between accounts. The original funded
period still generates an exact cofinal run on the new reserve. -/
noncomputable def trajectory_after_restoring (stable : RegistrationOnReserves input raw) :
    Trajectory input origin roster Start where
  state := Replay
  initial := rfl
  move n :=
    let localChecks := paid_after_restoring move law extra nonnegative clock round stable n
    ⟨move.word, localChecks.1 move.word move.registered, localChecks.2.1, localChecks.2.2.1⟩
  next_eq _ := rfl
  cofinal cut bound := by
    have clock_bound (n : Nat) : clock + (n : ℚ) * quantum ≤ (Replay n).clock := by
      induction n with
      | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; rfl
      | succ n earlier =>
        have tick := (paid_after_restoring move law extra nonnegative clock round stable n).2.2.2
        have advances := tick.trans (le_max_right 0 (input.law.duration (Replay n)))
        change clock + ((n + 1 : Nat) : ℚ) * quantum ≤
          (Replay n).clock + max 0 (input.law.duration (Replay n))
        rw [Nat.cast_succ]
        linarith only [earlier, advances]
    obtain ⟨n, beyond⟩ := exists_nat_gt ((bound - clock) / quantum)
    have crossed := (div_lt_iff₀ law.positive).mp beyond
    have monotone := mul_le_mul_of_nonneg_right
      (show (n : ℚ) ≤ ((max n cut : Nat) : ℚ) by exact_mod_cast le_max_left n cut) law.positive.le
    exact ⟨max n cut, le_max_right n cut, by linarith only [clock_bound (max n cut), crossed, monotone]⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Move

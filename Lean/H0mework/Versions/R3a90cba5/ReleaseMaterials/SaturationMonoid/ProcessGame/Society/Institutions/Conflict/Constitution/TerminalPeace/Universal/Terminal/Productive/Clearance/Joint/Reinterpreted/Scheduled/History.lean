import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Scheduled.Motion
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.Scheduled

open Capitalism.Universal.Source.Program
open Reparation.Actual (Script)
open FixedPoint (RevisionAnswers)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}
  {quantum : ℚ}

variable (catalogue : MenuAt Party Good Port Technology Instrument)
  (approvals : RevisionAnswers Party Good Port Technology Instrument)
  (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

def dispatch (before : State loss front quantum) (submission : Option (Submission before.current)) : Motion before :=
  match submission with
  | none => hold before
  | some (.payment key amount) => tryPayment before answers key amount catalogue addresses covered
  | some (.production offer code) => tryProduction before approvals offer code

structure Round (before : State loss front quantum) where
  due : DueWrite before
  motion : Motion due.next

def Round.next {before : State loss front quantum} (round : Round before) : State loss front quantum :=
  round.motion.next

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem Round.elapsed {before : State loss front quantum} (round : Round before) :
    before.current.physical.raw.clock + quantum ≤ round.next.current.physical.raw.clock :=
  round.due.elapsed.trans round.motion.clock

/-- The due write is generated before the submitted motion is read.
Neither a rejected signature nor an invalid proposed trial can replace it. -/
def advance (before : State loss front quantum)
    (request : (atDue : Current loss front) → Option (Submission atDue)) : Round before :=
  let due := writeDue before
  ⟨due, dispatch catalogue approvals answers addresses covered due.next (request due.next.current)⟩

variable (initial : State loss front quantum)
  (policy : (n : Nat) → (atDue : Current loss front) → Option (Submission atDue))

def history : Nat → State loss front quantum
  | 0 => initial
  | n + 1 => (advance catalogue approvals answers addresses covered (history n) (policy n)).next

local notation "Reached" => history catalogue approvals answers addresses covered initial policy

def roundAt (n : Nat) : Round (Reached n) :=
  advance catalogue approvals answers addresses covered (Reached n) (policy n)

theorem original_addresses_remain (n : Nat) :
    (Reached n).current.ledger.stack.balances.map Prod.fst = initial.current.ledger.stack.balances.map Prod.fst :=
  (Reached n).current.origins.trans initial.current.origins.symm

theorem every_round_consumes_the_original_successor (n : Nat) :
    (Reached (n + 1)).current =
      ((roundAt catalogue approvals answers addresses covered initial policy n).motion.event.map Event.next).getD
        (roundAt catalogue approvals answers addresses covered initial policy n).due.next.current :=
  (roundAt catalogue approvals answers addresses covered initial policy n).motion.actual

theorem clock_lower (n : Nat) :
    initial.current.physical.raw.clock + (n : ℚ) * quantum ≤ (Reached n).current.physical.raw.clock := by
  induction n with
  | zero => simp [history]
  | succ n earlier =>
    have paid := (roundAt catalogue approvals answers addresses covered initial policy n).elapsed
    change (Reached n).current.physical.raw.clock + quantum ≤ (Reached (n + 1)).current.physical.raw.clock at paid
    rw [Nat.cast_succ]
    linarith only [earlier, paid]

theorem the_unsettled_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (Reached n).current.physical.raw.clock := by
  have positive := initial.recipe.law.positive
  obtain ⟨n, passed⟩ := exists_nat_gt ((bound - initial.current.physical.raw.clock) / quantum)
  have advanced := (div_lt_iff₀ positive).mp passed
  have later := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_left n start)) positive.le
  exact ⟨max n start, le_max_right _ _, by
    linarith only [advanced, later, clock_lower catalogue approvals answers addresses covered initial policy (max n start)]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.Scheduled

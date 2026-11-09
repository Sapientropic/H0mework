import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Offer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Source.Program
open Reparation Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

abbrev JointOffer (source : Conflict.Root.Cut Party Good Port Technology Instrument) :=
  (key : Key Party Good) → Option (JointReceipt source key)

variable (offer : JointOffer seed) (origin : Occurrence seed community) (before : Balance)

def rowDemand : ℚ := by
  classical
  exact match offer origin.key with
  | none => 0
  | some receipt => if jointLater origin receipt then before.remaining else 0

theorem rowDemand_nonnegative : 0 ≤ rowDemand offer origin before := by
  classical
  unfold rowDemand
  split
  · exact le_rfl
  · split
    · exact before.nonnegative
    · exact le_rfl

structure RowAllocation (available : ℚ) where
  after : Balance
  motion : Transport.Motion (law origin) (.live before) (.live after)
  amount : ℚ
  exactAmount : amount = min available (rowDemand offer origin before)
  afterExact : after.remaining = before.remaining - amount

variable {offer origin before}

namespace RowAllocation

theorem amount_nonnegative {available : ℚ} (allocated : RowAllocation offer origin before available)
    (nonnegative : 0 ≤ available) : 0 ≤ allocated.amount := by
  rw [allocated.exactAmount]
  exact le_min nonnegative (rowDemand_nonnegative _ _ _)

theorem amount_le_available {available : ℚ} (allocated : RowAllocation offer origin before available) :
    allocated.amount ≤ available :=
  allocated.exactAmount.trans_le (min_le_left _ _)

end RowAllocation

variable (offer origin before)

private def noPayment (available : ℚ) (zero : min available (rowDemand offer origin before) = 0) :
    RowAllocation offer origin before available :=
  ⟨before, .inr (.wait (.live before)), 0, zero.symm, (sub_zero _).symm⟩

/-- The original FIFO charge is capped by the eligible original balance
and the remaining actual delivery. A move retains the literal row. -/
def allocateRow (available : ℚ) (nonnegative : 0 ≤ available)
    (bounded : ∀ receipt, offer origin.key = some receipt → available ≤ receipt.quantity) :
    RowAllocation offer origin before available := by
  classical
  cases selected : offer origin.key with
  | none =>
    exact noPayment offer origin before available (by simp [rowDemand, selected, min_eq_right nonnegative])
  | some receipt =>
    by_cases later : jointLater origin receipt
    · have due : rowDemand offer origin before = before.remaining := by simp [rowDemand, selected, later]
      let payment := min available before.remaining
      by_cases positive : 0 < payment
      · let share : JointShare origin := ⟨receipt, payment, positive,
          (min_le_left _ _).trans (bounded receipt selected), later⟩
        have within : share.amount ≤ before.remaining := min_le_right _ _
        exact ⟨before.subtract share.amount within, jointCredit origin before share within,
          payment, by rw [due], rfl⟩
      · have zero : payment = 0 := (le_of_not_gt positive).antisymm (le_min nonnegative before.nonnegative)
        exact noPayment offer origin before available (by rw [due]; exact zero)
    · exact noPayment offer origin before available (by simp [rowDemand, selected, later, min_eq_right nonnegative])

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

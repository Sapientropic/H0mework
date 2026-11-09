import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (tariff : Tariff Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum)
  (policy : CoalitionPolicy Party Good Port Technology Instrument)

/-- Read a charge as the physical difference from the same due
production. The time, payer, and review word come from the actual step. -/
def postedCost (ordinal : Nat) (good : Good) : ℚ :=
  let current := (history tariff replies opening policy ordinal).1
  match stepAt tariff replies opening policy ordinal with
  | .reviewed wire _ paid => current.move.next.stock wire.payer good - paid.next.physical.raw.stock wire.payer good
  | _ => 0

private theorem postedCost_eq (ordinal : Nat) (good : Good) :
    postedCost tariff replies opening policy ordinal good =
      ((stepAt tariff replies opening policy ordinal).paidWire.map fun wire =>
        amount Good (bill tariff wire).expenses good).getD 0 := by
  unfold postedCost
  cases stepAt tariff replies opening policy ordinal with
  | renewed | revised => rfl
  | reviewed wire signed paid =>
    have debit := paid.stock wire.payer good
    have payer : wire.payer = (bill tariff wire).payer := rfl
    change _ - paid.round.next.physical.raw.stock wire.payer good = amount Good (bill tariff wire).expenses good
    rw [ReviewBid.fee, if_pos payer] at debit
    linarith only [debit]

private theorem sum_posted (indices : List Nat) (good : Good) :
    (indices.map fun n => postedCost tariff replies opening policy n good).sum =
      ((indices.filterMap fun n => (stepAt tariff replies opening policy n).paidWire).map fun wire =>
        amount Good (bill tariff wire).expenses good).sum := by
  induction indices with
  | nil => rfl
  | cons n rest prior =>
    rw [List.map_cons, List.sum_cons, prior, postedCost_eq, List.filterMap_cons]
    cases (stepAt tariff replies opening policy n).paidWire <;> simp

/-- Any chosen subhistory counts each original ordinal once. Its
actual debit covers the whole concatenated word, with a new filing
charge per paid fragment even when the coalition changes payers. -/
theorem repeated_paid_fragments_cannot_discount_the_actual_charge
    (take : Nat → Bool) (cutoff : Nat) (good : Good) :
    let ordinals := (List.range cutoff).filter take
    let fragments := (ordinals.filterMap fun n => (stepAt tariff replies opening policy n).paidWire).map Wire.attempted
    let posted := (ordinals.map fun n => postedCost tariff replies opening policy n good).sum
    posted + amount Good tariff.filing good =
      amount Good (tariff.parts fragments.flatten).bundle good +
        (fragments.length : ℚ) * amount Good tariff.filing good := by
  dsimp only
  rw [sum_posted]
  simpa only [List.map_map, Function.comp_def, bill] using
    tariff.split_amount ((((List.range cutoff).filter take).filterMap
      (fun n => (stepAt tariff replies opening policy n).paidWire)).map Wire.attempted) good

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum
local notation "Policy" => CoalitionPolicy Party Good Port Technology Instrument

def withoutAttacks (policy : Policy) : Policy :=
  fun n seen => {policy n seen with packets := []}

variable (tariff : Tariff Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

/-- Without a material charge, erasing the attack lane leaves even the
dependent root current unchanged, at every cut of the unpaid prefix. -/
theorem an_unpaid_prefix_is_the_original_ledger
    (policy : CoalitionPolicy Party Good Port Technology Instrument) (cutoff : Nat)
    (unpaid : ∀ (i : Nat), i < cutoff → (stepAt tariff replies opening policy i).paidWire = none) :
    history tariff replies opening policy cutoff = history tariff replies opening (withoutAttacks policy) cutoff := by
  induction cutoff with
  | zero => rfl
  | succ n prior =>
    have same := prior fun i before => unpaid i (Nat.lt_succ_of_lt before)
    let reached := history tariff replies opening policy n
    have last := no_payment_preserves_the_exact_due_write tariff replies reached.1 (policy n reached.2)
      (unpaid n (Nat.lt_succ_self n))
    change (let effect := transition tariff replies reached.1 (policy n reached.2)
            (effect.1, effect.2 :: reached.2)) =
      (let quiet := history tariff replies opening (withoutAttacks policy) n
       let effect := transition tariff replies quiet.1 (withoutAttacks policy n quiet.2)
       (effect.1, effect.2 :: quiet.2))
    rw [← same]
    change (let effect := transition tariff replies reached.1 (policy n reached.2)
            (effect.1, effect.2 :: reached.2)) =
      (let effect := transition tariff replies reached.1 {policy n reached.2 with packets := []}
       (effect.1, effect.2 :: reached.2))
    unfold transition
    rw [last]

/-- Any changed read at a cut has a preceding original material write
by the very payer whose personal authorization admitted that packet. -/
theorem any_changed_read_traces_to_a_payers_actual_write {View : Type*}
    (policy : CoalitionPolicy Party Good Port Technology Instrument)
    (read : State × List Observation → View) (cutoff : Nat)
    (changed : read (history tariff replies opening policy cutoff) ≠
      read (history tariff replies opening (withoutAttacks policy) cutoff)) :
    ∃ i < cutoff, ∃ (wire : Wire Party Good Port Technology Instrument)
        (signed : Admitted tariff replies (history tariff replies opening policy i).1 wire)
        (paid : PaidReview (history tariff replies opening policy i).1 (bill tariff wire)),
      stepAt tariff replies opening policy i = Step.reviewed wire signed paid := by
  classical
  have positive : ∃ i < cutoff, (stepAt tariff replies opening policy i).paidWire ≠ none := by
    by_contra noPayment
    apply changed
    apply congrArg read
    exact an_unpaid_prefix_is_the_original_ledger tariff replies opening policy cutoff
      (fun i earlier => not_ne_iff.mp fun paid => noPayment ⟨i, earlier, paid⟩)
  obtain ⟨i, before, positive⟩ := positive
  cases issued : (stepAt tariff replies opening policy i).paidWire with
  | none => exact (positive issued).elim
  | some wire =>
    obtain ⟨signed, paid, actual⟩ := (stepAt tariff replies opening policy i).paidWire_has_its_actual_receipt issued
    exact ⟨i, before, wire, signed, paid, actual⟩

/-- Free presentations preserve the entire partition of possible
source histories induced by any action-facing read. -/
theorem zero_tenders_leave_every_information_fibre_unchanged {View : Type*}
    (policy : CoalitionPolicy Party Good Port Technology Instrument)
    (read : (Nat → State × List Observation) → View) (other : State)
    (otherTariff : Tariff Party Good Port Technology Instrument)
    (otherReplies : Replies Party Good Port Technology Instrument)
    (otherPolicy : Policy) :
    read (history tariff replies opening policy) = read (history otherTariff otherReplies other otherPolicy) ↔
      read (history tariff replies opening (fun n seen => withoutZero (policy n seen))) =
        read (history otherTariff otherReplies other (fun n seen => withoutZero (otherPolicy n seen))) := by
  simp only [any_adaptive_zero_tenders_erase_from_the_whole_trace]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

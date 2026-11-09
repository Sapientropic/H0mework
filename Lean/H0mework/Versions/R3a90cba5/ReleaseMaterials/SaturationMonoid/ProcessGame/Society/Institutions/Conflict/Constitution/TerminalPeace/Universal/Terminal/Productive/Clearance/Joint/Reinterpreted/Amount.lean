import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Reparation (Key)
open Reparation.Actual (Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

variable (before : Current loss front) (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (key : Key Party Good) (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

def feasibleAmounts : Set ℝ :=
  {value | ∃ q : ℚ, Funding before answers key q ∧ (q : ℝ) = value}

private theorem feasible_bounded : BddAbove (feasibleAmounts before answers key) := by
  refine ⟨(liveBalance before key : ℝ), ?_⟩
  rintro _ ⟨_, accepted, rfl⟩
  exact_mod_cast accepted.within

abbrev paymentUpper := sSup (feasibleAmounts before answers key)

theorem paymentUpper_is_exact (some : (feasibleAmounts before answers key).Nonempty) :
    IsLUB (feasibleAmounts before answers key) (paymentUpper before answers key) :=
  isLUB_csSup some (feasible_bounded before answers key)

theorem a_funded_full_balance_is_the_exact_upper
    (funded : Funding before answers key (liveBalance before key)) :
    paymentUpper before answers key = (liveBalance before key : ℝ) := by
  have included : (liveBalance before key : ℝ) ∈ feasibleAmounts before answers key :=
    ⟨_, funded, rfl⟩
  have tight := paymentUpper_is_exact before answers key ⟨_, included⟩
  apply le_antisymm
  · apply tight.2
    rintro _ ⟨_, accepted, rfl⟩
    exact_mod_cast accepted.within
  · exact tight.1 included

structure AmountWritten (q : ℚ) where
  actual : PaidWrite before answers key q
  same : pay before answers key q addresses covered = .inr actual

private def writeAmount (q : ℚ) (funded : Funding before answers key q) :
    AmountWritten before answers key addresses covered q :=
  let existsWrite := (pays_exactly_at_a_funded_position before answers key q addresses covered).mpr funded
  ⟨Classical.choose existsWrite, Classical.choose_spec existsWrite⟩

inductive AmountOutcome
  | attained (q : ℚ) (actual : AmountWritten before answers key addresses covered q)
      (tight : (q : ℝ) = paymentUpper before answers key)
  | approaching (some : (feasibleAmounts before answers key).Nonempty)
      (unattained : paymentUpper before answers key ∉ feasibleAmounts before answers key)
      (near : ∀ ε : ℝ, 0 < ε →
        (q : ℚ) × {_actual : AmountWritten before answers key addresses covered q //
          paymentUpper before answers key - ε < (q : ℝ) ∧ (q : ℝ) < paymentUpper before answers key})
  | blocked (each : ∀ q : ℚ, {refused : Refused before (PaymentIssue before answers key q) //
      pay before answers key q addresses covered = .inl refused})

/-- Resolve all possible signed amounts at this actual cut. No assumption
of continuity is made about an owner's reply or the new law's need floor. -/
def resolve : AmountOutcome before answers key addresses covered := by
  classical
  let values := feasibleAmounts before answers key
  let upper := paymentUpper before answers key
  by_cases some : values.Nonempty
  · by_cases achieved : upper ∈ values
    · let q := Classical.choose achieved
      have read := Classical.choose_spec achieved
      exact .attained q (writeAmount before answers key addresses covered q read.1) read.2
    · refine .approaching some achieved (fun ε positive => ?_)
      let near := exists_lt_of_lt_csSup some (sub_lt_self upper positive)
      let value := Classical.choose near
      have found := Classical.choose_spec near
      let q := Classical.choose found.1
      have read := Classical.choose_spec found.1
      refine ⟨q, writeAmount before answers key addresses covered q read.1, ?_, ?_⟩
      · rw [read.2]
        exact found.2
      · rw [read.2]
        apply lt_of_le_of_ne (le_csSup (feasible_bounded before answers key) found.1)
        intro equal
        apply achieved
        change sSup (feasibleAmounts before answers key) ∈ feasibleAmounts before answers key
        rw [← equal]
        exact found.1
  · refine .blocked fun q => ?_
    cases actual : pay before answers key q addresses covered with
    | inl refused => exact ⟨refused, rfl⟩
    | inr paid =>
      have funded := (pays_exactly_at_a_funded_position before answers key q addresses covered).mp ⟨paid, actual⟩
      exact (some ⟨q, q, funded, rfl⟩).elim

theorem resolve_selects_the_funded_full_balance
    (funded : Funding before answers key (liveBalance before key)) :
    ∃ (actual : AmountWritten before answers key addresses covered (liveBalance before key))
        (tight : (liveBalance before key : ℝ) = paymentUpper before answers key),
      resolve before answers key addresses covered = .attained (liveBalance before key) actual tight := by
  have upper := a_funded_full_balance_is_the_exact_upper before answers key funded
  have achieved : paymentUpper before answers key ∈ feasibleAmounts before answers key := by
    rw [upper]
    exact ⟨_, funded, rfl⟩
  cases selected : resolve before answers key addresses covered with
  | attained amount actual tight =>
    have equal : amount = liveBalance before key := by exact_mod_cast tight.trans upper
    subst amount
    exact ⟨actual, tight, rfl⟩
  | approaching _ unattained _ => exact (unattained achieved).elim
  | blocked every =>
    let denied := every (liveBalance before key)
    obtain ⟨paid, actual⟩ :=
      (pays_exactly_at_a_funded_position before answers key _ addresses covered).mpr funded
    have contradiction := actual.symm.trans denied.2
    cases contradiction

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

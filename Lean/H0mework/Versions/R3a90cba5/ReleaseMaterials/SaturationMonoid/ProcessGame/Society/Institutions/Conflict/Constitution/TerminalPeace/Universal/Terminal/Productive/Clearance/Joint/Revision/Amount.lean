import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Protected

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Reparation (Key)
open Reparation.Actual (Occurrence ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (front : Script Party Good Port Technology Instrument)
  (key : Key Party Good) (purpose : Port)

local notation "Feasible" => InspectablePayment loss answers front key purpose
local notation "Check" => compileProtectedInstallment loss answers front key purpose

def paymentAmounts : Set ℝ := {a | ∃ quantity : ℚ, Feasible quantity ∧ (quantity : ℝ) = a}

private theorem paymentAmounts_bddAbove : BddAbove (paymentAmounts loss answers front key purpose) := by
  refine ⟨(maximumInstallment loss answers front key : ℝ), ?_⟩
  rintro _ ⟨quantity, payable, rfl⟩
  have upper := (material_installment_iff loss answers front key quantity payable.1.positive).mpr
    ⟨payable.1.owing, payable.1.stock⟩
  exact_mod_cast upper

abbrev tightPayment := sSup (paymentAmounts loss answers front key purpose)

theorem tightPayment_is_the_exact_upper_bound
    (some : (paymentAmounts loss answers front key purpose).Nonempty) :
    IsLUB (paymentAmounts loss answers front key purpose) (tightPayment loss answers front key purpose) :=
  isLUB_csSup some (paymentAmounts_bddAbove loss answers front key purpose)

variable (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front)

structure WrittenAmount where
  quantity : ℚ
  paid : PaidInstallment loss answers (reserveAt loss front) front purpose key quantity
  keepsNeeds : ProtectsNeeds loss (front ++ installment purpose key quantity)
  selected : Check quantity safe ready = .written paid keepsNeeds

private def writeChosenAmount (quantity : ℚ) (viable : Feasible quantity) :
    {written : WrittenAmount loss answers front key purpose safe ready // written.quantity = quantity} := by
  cases check : Check quantity safe ready with
  | refused issue _ _ => exact (issue.refutes loss answers front key purpose quantity viable).elim
  | written paid keepsNeeds => exact ⟨⟨quantity, paid, keepsNeeds, check⟩, rfl⟩

inductive AmountResolution
  | attained (written : WrittenAmount loss answers front key purpose safe ready)
      (exactUpper : (written.quantity : ℝ) = tightPayment loss answers front key purpose)
  | approached (existsPayment : (paymentAmounts loss answers front key purpose).Nonempty)
      (unattained : tightPayment loss answers front key purpose ∉ paymentAmounts loss answers front key purpose)
      (near : ∀ ε : ℝ, 0 < ε →
        {written : WrittenAmount loss answers front key purpose safe ready //
          tightPayment loss answers front key purpose - ε < (written.quantity : ℝ) ∧
            (written.quantity : ℝ) < tightPayment loss answers front key purpose})
  | blocked (every : ∀ quantity : ℚ,
      {issue : ProtectedIssue loss answers front key purpose quantity //
        ∃ visit same, Check quantity safe ready = .refused issue visit same})

/-- Exact amount selection allows signed rational instalments to have an
unattained upper bound. Each approximation still calls the guarded original
writer with its own original signatures and position. -/
def resolveAmount : AmountResolution loss answers front key purpose safe ready := by
  classical
  let values := paymentAmounts loss answers front key purpose
  let upper := tightPayment loss answers front key purpose
  by_cases some : values.Nonempty
  · by_cases achieved : upper ∈ values
    · let quantity := Classical.choose achieved
      have viable := Classical.choose_spec achieved
      let written := writeChosenAmount loss answers front key purpose safe ready quantity viable.1
      exact .attained written.val
        ((congrArg (fun q : ℚ => (q : ℝ)) written.property).trans viable.2)
    · refine .approached some achieved (fun ε positive => ?_)
      have below : upper - ε < sSup values := sub_lt_self _ positive
      let close := exists_lt_of_lt_csSup some below
      let value := Classical.choose close
      have found := Classical.choose_spec close
      let quantity := Classical.choose found.1
      have viable := Classical.choose_spec found.1
      let written := writeChosenAmount loss answers front key purpose safe ready quantity viable.1
      have read : (written.val.quantity : ℝ) = value := (congrArg (fun q : ℚ => (q : ℝ)) written.property).trans viable.2
      refine ⟨written.val, read.symm ▸ found.2, ?_⟩
      rw [read]
      apply lt_of_le_of_ne (le_csSup (paymentAmounts_bddAbove loss answers front key purpose) found.1)
      intro equal
      exact achieved ((congrArg (fun point : ℝ => point ∈ values) equal).mp found.1)
  · refine .blocked (fun quantity => ?_)
    cases check : Check quantity safe ready with
    | refused issue visit same => exact ⟨issue, visit, same, rfl⟩
    | written paid keepsNeeds =>
      have feasible := (compileProtectedInstallment_pays_iff loss answers front key purpose quantity safe ready).mp
        ⟨paid, keepsNeeds, check⟩
      exact (some ⟨quantity, quantity, feasible, rfl⟩).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

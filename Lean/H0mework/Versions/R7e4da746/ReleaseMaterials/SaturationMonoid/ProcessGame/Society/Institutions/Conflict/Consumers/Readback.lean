import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.NamedPayment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

noncomputable section

private abbrev Shift := Conflict.Root.Shift source front levy settle 1

private theorem funding_read :
    ∃ funding, Conflict.Root.readFunding source.native.input.law levy settle = some funding ∧
      funding.position = position ∧ funding.bearer = false ∧
      funding.quantity = 6 ∧ funding.principal = 6 := by
  rw [sourceInput]
  let funding : Conflict.Root.Funding compact.law levy settle :=
    ⟨position, false, 6, 6, rfl, rfl, by decide, by decide, by decide +kernel, by decide +kernel⟩
  exact ⟨funding, by with_unfolding_all rfl, rfl, rfl, rfl, rfl⟩

theorem the_original_incidence_reader_selects_the_old_row :
    ∃ shift : Shift, Conflict.Root.readShift source front levy settle 1 = .shifted shift ∧
      shift.funding.position = position ∧ shift.funding.bearer = false ∧ shift.funding.quantity = 6 := by
  obtain ⟨funding, found, named, bearer, quantity, principal⟩ := funding_read
  have matched : Conflict.Root.SameOldSlot source (front ++ [levy, settle]) funding.position 1 funding.principal := by
    rw [named, principal]
    exact the_paid_conflict_reaches_the_named_old_principal
  have accepted := (Conflict.Root.inspect_accepts_iff source conflict).mpr conflictPaid
  have safe : Settlement.NonFinancial front := by decide +kernel
  cases prior : Settlement.checkFinancial front with
  | rejected request present financial => exact (financial (safe request present)).elim
  | accepted material =>
    cases executed : Conflict.Root.inspect source (front ++ [levy, settle]) with
    | rejected failure =>
      change (Conflict.Root.inspect source (front ++ [levy, settle])).accepted = true at accepted
      rw [executed] at accepted
      cases accepted
    | paid actual =>
      refine ⟨⟨funding, material, actual, matched⟩, ?_, named, bearer, quantity⟩
      unfold Conflict.Root.readShift
      split
      · rename_i absent
        rw [found] at absent
        cases absent
      · rename_i other returned
        have same : other = funding := Option.some.inj (returned.symm.trans found)
        cases same
        simp only [prior, executed, dif_pos matched]

theorem exact_binding_word (shift : Shift) (named : shift.funding.position = position)
    (bearer : shift.funding.bearer = false) (quantity : shift.funding.quantity = 6) :
    shift.returnedWord (2 / 3) = restored 4 := by
  have nonzero : (2 / 3 : ℚ) ≠ 0 := by decide +kernel
  have unit : shift.unit = false := by
    unfold Conflict.Root.Shift.unit
    rw [named, sourceInput]
    rfl
  have payer : shift.funding.position.debtor = true := congrArg (·.debtor) named
  have port : source.native.input.law.stockPort (Conflict.Root.terminal source shift.originalWord).raw.technology
      true false = false := by rw [sourceInput]; rfl
  have amount : (2 / 3 : ℚ) * 6 = 4 := by decide +kernel
  unfold Conflict.Root.Shift.returnedWord Conflict.Root.Shift.returnRequest restored
  simp only [if_neg nonzero, payer, bearer, quantity, unit, port, amount]
  rfl

theorem the_reader_reimburses_the_same_bearer_at_the_exact_binding_rate :
    ∃ shift : Shift, Conflict.Root.readShift source front levy settle 1 = .shifted shift ∧
      (shift.atRate (2 / 3)).accepted = true ∧
      decisionStock (Conflict.Root.terminal source (shift.returnedWord (2 / 3))) =
        decisionStock (Conflict.Root.terminal source peace) ∧
      HEq (nativeAccount (Conflict.Root.terminal source (shift.returnedWord (2 / 3))))
        (nativeAccount (Conflict.Root.terminal source conflict)) := by
  obtain ⟨shift, actual, named, bearer, quantity⟩ := the_original_incidence_reader_selects_the_old_row
  have same := exact_binding_word shift named bearer quantity
  have paid : Conflict.Root.Paid source (shift.returnedWord (2 / 3)) := same.symm ▸ bindingReturnPaid
  refine ⟨shift, actual, (Conflict.Root.inspect_accepts_iff source _).mpr paid, ?_, ?_⟩
  · rw [same]
    exact sub_eq_zero.mp binding_return_is_a_paid_tie
  · exact (shift.actual_return_is_charged_to_the_original_debtor _ paid).2.2.2

theorem every_smaller_executable_return_leaves_positive_pressure
    (shift : Shift) (named : shift.funding.position = position) (quantity : shift.funding.quantity = 6)
    (rate : ℚ) (below : rate < 2 / 3) (paid : Conflict.Root.Paid source (shift.returnedWord rate)) :
    decisionStock (Conflict.Root.terminal source peace) <
      decisionStock (Conflict.Root.terminal source (shift.returnedWord rate)) := by
  have unit : shift.unit = false := by
    unfold Conflict.Root.Shift.unit
    rw [named, sourceInput]
    rfl
  have read : shift.debtorStock = decisionStock := by
    funext cut
    unfold Conflict.Root.Shift.debtorStock decisionStock
    rw [named, unit]
    rfl
  have effect := shift.exact_change_of_paid_gap ⟨peace, peacePaid⟩ rate paid
  rw [read, quantity] at effect
  change decisionStock (Conflict.Root.terminal source (shift.returnedWord rate)) -
    decisionStock (Conflict.Root.terminal source peace) =
      (decisionStock (Conflict.Root.terminal source conflict) -
        decisionStock (Conflict.Root.terminal source peace)) - rate * 6 at effect
  rw [old_war_peace_gap] at effect
  linarith

#print axioms the_original_incidence_reader_selects_the_old_row
#print axioms the_reader_reimburses_the_same_bearer_at_the_exact_binding_rate
#print axioms every_smaller_executable_return_leaves_positive_pressure

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

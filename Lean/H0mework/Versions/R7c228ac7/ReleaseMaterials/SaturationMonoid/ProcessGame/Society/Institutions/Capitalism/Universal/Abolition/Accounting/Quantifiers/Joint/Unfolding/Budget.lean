import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Current

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (window seed))

theorem actual_word_retains_declarations (current : Current seed grossClaim)
    (word : RawEvent Party Good Port Technology Instrument) :
    (advance seed grossClaim current word).productiveDeclared = current.productiveDeclared ∧
      (advance seed grossClaim current word).grossDeclared = current.grossDeclared := ⟨rfl,rfl⟩

theorem actual_word_keeps_paid_productive_paid (current : Current seed grossClaim)
    (paid : productivePaid seed grossClaim current) (word : RawEvent Party Good Port Technology Instrument) :
    productivePaid seed grossClaim (advance seed grossClaim current word) := by
  intro key original
  have bound := actual_word_never_refills_productive seed grossClaim current word key
  rw [paid key original] at bound
  exact le_antisymm bound ((advance seed grossClaim current word).productive_nonnegative key)

theorem actual_word_keeps_paid_gross_paid (current : Current seed grossClaim)
    (paid : grossPaid seed grossClaim current) (word : RawEvent Party Good Port Technology Instrument) :
    grossPaid seed grossClaim (advance seed grossClaim current word) := by
  intro key original
  have bound := actual_word_never_refills_gross seed grossClaim current word key
  rw [paid key original] at bound
  exact le_antisymm bound ((advance seed grossClaim current word).gross_nonnegative key)

theorem actual_word_never_increases_productive_budget (current : Current seed grossClaim)
    (word : RawEvent Party Good Port Technology Instrument) :
    productiveBudget seed grossClaim (advance seed grossClaim current word) ≤ productiveBudget seed grossClaim current := by
  cases active : current.productiveDeclared with
  | false => simp only [productiveBudget,(actual_word_retains_declarations seed grossClaim current word).1,active,if_false,Bool.false_eq_true,le_refl]
  | true =>
      by_cases paid : productivePaid seed grossClaim current
      · have after := actual_word_keeps_paid_productive_paid seed grossClaim current paid word
        simp only [productiveBudget,(actual_word_retains_declarations seed grossClaim current word).1,active,if_true,paid,after,le_refl]
      · by_cases after : productivePaid seed grossClaim (advance seed grossClaim current word) <;>
          simp only [productiveBudget,(actual_word_retains_declarations seed grossClaim current word).1,active,if_true,paid,after,if_false] <;> decide

theorem actual_word_never_increases_gross_budget (current : Current seed grossClaim)
    (word : RawEvent Party Good Port Technology Instrument) :
    grossBudget seed grossClaim (advance seed grossClaim current word) ≤ grossBudget seed grossClaim current := by
  cases active : current.grossDeclared with
  | false => simp only [grossBudget,(actual_word_retains_declarations seed grossClaim current word).2,active,if_false,Bool.false_eq_true,le_refl]
  | true =>
      by_cases paid : grossPaid seed grossClaim current
      · have after := actual_word_keeps_paid_gross_paid seed grossClaim current paid word
        simp only [grossBudget,(actual_word_retains_declarations seed grossClaim current word).2,active,if_true,paid,after,le_refl]
      · by_cases after : grossPaid seed grossClaim (advance seed grossClaim current word) <;>
          simp only [grossBudget,(actual_word_retains_declarations seed grossClaim current word).2,active,if_true,paid,after,if_false] <;> decide

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Current

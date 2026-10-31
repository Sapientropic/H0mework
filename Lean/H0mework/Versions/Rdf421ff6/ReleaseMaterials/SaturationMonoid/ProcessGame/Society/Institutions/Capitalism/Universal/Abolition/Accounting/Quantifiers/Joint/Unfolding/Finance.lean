import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Finance

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
  (claim : Entitlement.Source.Claim (window seed))

theorem genuine_financial_settlement_cannot_discharge_either_physical_obligation
    (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (financial : ∀ request ∈ word, ¬ Responsibility.NonFinancialOperation request.operation) :
    (advance seed claim current word).productive = current.productive ∧
      (advance seed claim current word).gross = current.gross ∧
      (advance seed claim current word).raw = (actualLaw seed).next current.raw word := by
  have unchanged := Allocation.a_financial_word_keeps_both_allocations_literal seed
    current.productive current.productiveDeclared current.grossDeclared
    current.gross current.gross_nonnegative current.raw word financial
  refine ⟨?_,unchanged.2,rfl⟩
  funext key
  change max 0 (current.productive key - max 0 ((analysis seed claim current word).netProductive key)) = _
  change max 0 (current.productive key - max 0
    ((Allocation.run seed current.productive current.productiveDeclared current.grossDeclared
      current.gross current.gross_nonnegative current.raw word).netProductive key)) = _
  rw [unchanged.1]
  simp only [max_self,sub_zero,max_eq_right (current.productive_nonnegative key)]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Current

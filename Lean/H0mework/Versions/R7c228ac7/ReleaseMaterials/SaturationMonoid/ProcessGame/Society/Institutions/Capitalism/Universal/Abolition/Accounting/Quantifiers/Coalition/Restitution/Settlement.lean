import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.FullAccount
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Guarantee
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Finance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

open Source.Program Innovation

noncomputable section

attribute [local irreducible] Entitlement.Duty.scope Joint.actualLaw

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

theorem a_paid_original_matrix_has_no_remaining_restitution_position
    (current : Joint.Current seed claim) (paid : Joint.Current.grossPaid seed claim current) :
    liability seed claim current = 0 := by
  unfold liability position
  have empty : ((Entitlement.Duty.scope (Joint.window seed)).map fun key => incidence key (current.gross key)).sum = 0 := by
    apply List.sum_eq_zero
    intro value listed
    obtain ⟨key,original,rfl⟩ := List.mem_map.mp listed
    rw [paid key original,map_zero]
  rw [empty,neg_zero]

theorem retiring_an_original_finite_claim_cannot_mint_restitution_credit
    (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (financial : ∀ request ∈ word, ¬ Responsibility.NonFinancialOperation request.operation)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) : credits seed claim current word key = 0 := by
  have conserved := the_actual_allocation_conserves_every_original_cell seed claim current word key
  have unchanged := Joint.Current.genuine_financial_settlement_cannot_discharge_either_physical_obligation
    seed claim current word financial
  rw [unchanged.2.1] at conserved
  linarith

theorem primitive_resources_generate_actual_restitution_with_zero_residual
    (word : RawEvent Party Good Port Technology Instrument)
    (resources : Joint.Planning.Resources seed claim
      (Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)) word) :
    let original := Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)
    Joint.Planning.ActualSuccess seed claim original word ∧
      liability seed claim (Joint.Current.advance seed claim original word) = 0 ∧
      originalControl (Joint.window seed) + returned seed claim original word = 0 := by
  dsimp only
  have actual := Joint.Planning.primitive_resources_generate_one_actual_payment_of_both_original_obligations
    seed claim _ word resources
  have empty := a_paid_original_matrix_has_no_remaining_restitution_position seed claim _ actual.grossPaid
  have balance := original_control_return_and_unpaid_liability_cancel_in_the_actual_next seed claim word
  dsimp only at balance
  rw [empty,add_zero] at balance
  exact ⟨actual,empty,balance⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

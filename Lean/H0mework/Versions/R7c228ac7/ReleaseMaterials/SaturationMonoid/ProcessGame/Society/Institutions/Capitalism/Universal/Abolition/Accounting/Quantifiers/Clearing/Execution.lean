import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing.Programme

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument) (controller victim : Party)
  (good : Good) (quantity : ℚ) (instrument : Instrument) (principal : ℚ)
  (resources : Resources law before controller victim good quantity instrument principal)

local notation "reader" => PublicFunction.physicalLaw law
local notation "returned" => refund law controller victim good quantity instrument
local notation "paid" => payment law controller victim instrument principal

include resources

omit [DecidableEq Instrument] in
theorem primitive_resources_authorize_the_actual_return : (reader).Valid before returned := by
  refine ⟨⟨True.intro,rfl⟩,(fun _ _ => Or.inl rfl),True.intro,?_,?_,?_⟩
  · simpa [RawLaw.debit,refund,locate,NonnegativeBundle] using resources.refund_nonnegative
  · simpa [RawLaw.credit,refund,locate,NonnegativeBundle] using resources.refund_nonnegative
  · simpa [RawLaw.debit,refund,locate,flowAt,amount] using resources.refund_stock

theorem the_return_preserves_the_entire_original_claim_matrix :
    ((reader).step before returned).claims = before.claims := by
  rw [RawLaw.step,if_pos (primitive_resources_authorize_the_actual_return law before controller victim
    good quantity instrument principal resources)]
  rfl

theorem the_return_really_supplies_the_original_debtor :
    ((reader).step before returned).stock victim (law.settlementUnit instrument) =
      before.stock victim (law.settlementUnit instrument) +
        if good = law.settlementUnit instrument then quantity else 0 := by
  rw [RawLaw.step,if_pos (primitive_resources_authorize_the_actual_return law before controller victim
    good quantity instrument principal resources)]
  simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,refund,locate,flowAt,amount,
    resources.distinct]

theorem primitive_resources_authorize_the_actual_old_claim_payment :
    (reader).Valid ((reader).step before returned) paid := by
  refine ⟨⟨True.intro,rfl⟩,(fun _ _ => Or.inl rfl),?_,?_,?_,?_⟩
  · change 0 ≤ principal ∧ principal ≤ ((reader).step before returned).claims instrument victim controller ∧
      0 < law.settlementRate instrument
    rw [the_return_preserves_the_entire_original_claim_matrix law before controller victim good quantity instrument principal resources]
    exact ⟨resources.principal_nonnegative,resources.old_claim,resources.rate_positive⟩
  · simpa [RawLaw.debit,payment,locate,NonnegativeBundle,PublicFunction.physicalLaw] using
      mul_nonneg resources.principal_nonnegative resources.rate_positive.le
  · simpa [RawLaw.credit,payment,locate,NonnegativeBundle,PublicFunction.physicalLaw] using
      mul_nonneg resources.principal_nonnegative resources.rate_positive.le
  · have funded : principal * law.settlementRate instrument ≤
        ((reader).step before returned).stock victim (law.settlementUnit instrument) := by
      rw [the_return_really_supplies_the_original_debtor law before controller victim good quantity instrument principal resources]
      exact resources.repayment_stock
    simpa [RawLaw.debit,payment,locate,flowAt,amount,PublicFunction.physicalLaw] using funded

theorem primitive_resources_generate_the_whole_actual_clearing :
    ∀ item ∈ (reader).rawItems before (word law controller victim good quantity instrument principal),
      (reader).Valid item.before item.request := by
  have first := primitive_resources_authorize_the_actual_return law before controller victim good quantity instrument principal resources
  have second := primitive_resources_authorize_the_actual_old_claim_payment law before controller victim good quantity instrument principal resources
  simpa [RawLaw.rawItems,RawLaw.execute,word] using And.intro first second

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing

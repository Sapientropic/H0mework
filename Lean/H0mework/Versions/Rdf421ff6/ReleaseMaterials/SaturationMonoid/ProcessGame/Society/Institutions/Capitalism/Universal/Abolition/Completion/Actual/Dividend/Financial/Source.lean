import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

local notation "first" => Dividend.seed input depth count prefixLimit renewalLimit oldPast
local notation "actual" => Dividend.publicCurrent input depth count prefixLimit renewalLimit oldPast current
local notation "reference" => Dividend.oldEndpoint input depth count prefixLimit renewalLimit oldPast current
local notation "periods" => Dividend.horizon input depth count prefixLimit renewalLimit oldPast current
local notation "publicItems" => traceItems input first current.past
local notation "oldItems" => referenceItems input (Root.Actual.Current.raw first) periods

def claimDifference : ClaimChange (Party := Party) (Instrument := Instrument) :=
  inventoryClaims (Physical.Public.interpreter input) publicItems - inventoryClaims input.law oldItems

def gainVector : MaterialChange (Party := Party) (Good := Good) :=
  inventoryMaterial (Physical.Public.interpreter input) publicItems - inventoryMaterial input.law oldItems +
    value input.law (claimDifference input depth count prefixLimit renewalLimit oldPast current)

def delta (person : Party) (good : Good) : ℚ :=
  gainVector input depth count prefixLimit renewalLimit oldPast current (person, good)

theorem the_financial_difference_is_the_literal_endpoint_matrix_difference
    (instrument : Instrument) (debtor creditor : Party) :
    claimDifference input depth count prefixLimit renewalLimit oldPast current (instrument, debtor, creditor) =
      (actual).raw.claims instrument debtor creditor - (reference).claims instrument debtor creditor := by
  have publicBalance := the_actual_public_prefix_has_its_exact_original_claim_change input first current.past instrument debtor creditor
  have old := the_frozen_reference_has_its_exact_original_claim_change input (first).raw periods instrument debtor creditor
  change (actual).raw.claims instrument debtor creditor = _ at publicBalance
  change (reference).claims instrument debtor creditor = _ at old
  rw [publicBalance, old]
  simp only [claimDifference, Finsupp.sub_apply]
  ring

/-- The complete account uses each physical flow once and the original
instrument's signed claim change once. The common initial matrix cancels;
its original claims and origins are never erased or replaced. -/
theorem the_full_dividend_includes_the_original_stock_and_financial_changes
    (person : Party) (good : Good) :
    delta input depth count prefixLimit renewalLimit oldPast current person good =
      (actual).raw.stock person good - (reference).stock person good +
        value input.law (claimDifference input depth count prefixLimit renewalLimit oldPast current) (person, good) := by
  unfold delta gainVector
  simp only [Finsupp.add_apply, Finsupp.sub_apply]
  rw [the_actual_public_prefix_counts_its_original_material_flows_once,
    the_frozen_reference_counts_its_original_material_flows_once]
  rw [← Dividend.the_dividend_is_the_actual_public_stock_minus_its_frozen_reference]
  rfl

def cells : List (Party × Good) :=
  (gainVector input depth count prefixLimit renewalLimit oldPast current).support.toList

def quotedClaims : List (ClaimKey (Party := Party) (Instrument := Instrument)) :=
  (claimDifference input depth count prefixLimit renewalLimit oldPast current).support.toList

theorem no_unlisted_bearer_or_good_has_a_hidden_full_account_change
    (person : Party) (good : Good)
    (absent : (person, good) ∉ cells input depth count prefixLimit renewalLimit oldPast current) :
    delta input depth count prefixLimit renewalLimit oldPast current person good = 0 := by
  have outside : (person, good) ∉ (gainVector input depth count prefixLimit renewalLimit oldPast current).support := by
    simpa only [cells, Finset.mem_toList] using absent
  exact not_ne_iff.mp (fun nonzero => outside (Finsupp.mem_support_iff.mpr nonzero))

#print axioms the_financial_difference_is_the_literal_endpoint_matrix_difference
#print axioms the_full_dividend_includes_the_original_stock_and_financial_changes
#print axioms no_unlisted_bearer_or_good_has_a_hidden_full_account_change

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial

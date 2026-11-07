import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay

open Source.Program Innovation
open Abolition.Completion.Actual.Dividend
noncomputable section
attribute [local irreducible] Joint.actualLaw

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

/-- A restriction of the already computed source execution, not another run. -/
def items : Joint.Current seed claim → List (RawEvent Party Good Port Technology Instrument) →
    List (ExecutionItem Party Good Port Technology Instrument)
  | _,[] => []
  | current,input :: rest =>
      (Joint.actualLaw seed).rawItems current.raw (Joint.Boundary.executed seed claim current input) ++
        items (Joint.Boundary.next seed claim current input) rest

theorem every_item_is_an_actual_source_valid_item (current : Joint.Current seed claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    ∀ item ∈ items seed claim current inputs, (Joint.actualLaw seed).Valid item.before item.request := by
  induction inputs generalizing current with
  | nil => simp only [items,List.not_mem_nil,false_implies,implies_true]
  | cons input rest inherited =>
      intro item original
      rcases List.mem_append.mp original with first | later
      · exact Joint.Boundary.all_executed_items_are_actual seed claim current input item first
      · exact inherited _ item later

theorem every_original_financial_position_follows_its_actual_effect
    (current : Joint.Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (instrument : Instrument) (debtor creditor : Party) :
    (Joint.Boundary.afterInputs seed claim current inputs).raw.claims instrument debtor creditor =
      current.raw.claims instrument debtor creditor +
        Financial.inventoryClaims (Joint.actualLaw seed) (items seed claim current inputs) (instrument,debtor,creditor) := by
  induction inputs generalizing current with
  | nil => simp only [Joint.Boundary.afterInputs,items,Financial.inventoryClaims,List.map_nil,List.sum_nil,Finsupp.zero_apply,add_zero]
  | cons input rest inherited =>
      let executed := Joint.Boundary.executed seed claim current input
      have first := (Joint.actualLaw seed).execute_financial_balance current.raw 0 executed instrument debtor creditor
      rw [← Financial.inventory_claims_are_the_original_financial_delta] at first
      change (Joint.Boundary.next seed claim current input).raw.claims instrument debtor creditor = _ at first
      change (Joint.Boundary.afterInputs seed claim (Joint.Boundary.next seed claim current input) rest).raw.claims instrument debtor creditor = _
      rw [inherited,first]
      simp only [items,Financial.inventoryClaims,List.map_append,List.sum_append,Finsupp.add_apply,RawLaw.rawItems,executed]
      ring

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Protected

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

open Source.Program Innovation

noncomputable section

attribute [local irreducible] Joint.actualLaw

private theorem retained_sum {Vector : Type} [AddCommGroup Vector]
    (source execution control restitution remaining : Vector)
    (balanced : control + restitution + remaining = 0) :
    source + execution + remaining = (source - control) + (execution - restitution) := by
  calc
    _ = (source - control) + (execution - restitution) + (control + restitution + remaining) := by abel
    _ = _ := by rw [balanced,add_zero]

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

def originalIncome := Profit.fullIncome seed.input.law
  (seed.input.law.rawItems (Joint.window seed).before (Joint.window seed).word)

def actualIncome (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :=
  Profit.fullIncome (Joint.actualLaw seed) ((Joint.actualLaw seed).rawItems current.raw word)

/-- These are signed, actual positions retained after removing exactly the
classified control legs; they are not constrained to be nonpositive. -/
def retainedOriginalIncome :=
  Profit.production seed.input.law (seed.input.law.rawItems (Joint.window seed).before (Joint.window seed).word) +
    (Profit.transfers seed.input.law (seed.input.law.rawItems (Joint.window seed).before (Joint.window seed).word) -
      originalControl (Joint.window seed))

def retainedActualIncome (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :=
  Profit.production (Joint.actualLaw seed) ((Joint.actualLaw seed).rawItems current.raw word) +
    (Profit.transfers (Joint.actualLaw seed) ((Joint.actualLaw seed).rawItems current.raw word) -
      returned seed claim current word)

theorem retained_original_income_keeps_the_actual_full_account :
    retainedOriginalIncome seed = originalIncome seed - originalControl (Joint.window seed) := by
  unfold retainedOriginalIncome originalIncome
  rw [← add_sub_assoc,← Profit.every_original_inventory_separates_production_and_existing_positions]

theorem retained_actual_income_keeps_the_actual_full_account
    (current : Joint.Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
    retainedActualIncome seed claim current word = actualIncome seed claim current word - returned seed claim current word := by
  unfold retainedActualIncome actualIncome
  rw [← add_sub_assoc,← Profit.every_original_inventory_separates_production_and_existing_positions]

theorem full_account_keeps_actual_production_other_transfers_and_original_native_positions
    (word : RawEvent Party Good Port Technology Instrument) :
    let original := Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)
    originalIncome seed + actualIncome seed claim original word +
      liability seed claim (Joint.Current.advance seed claim original word) =
        retainedOriginalIncome seed + retainedActualIncome seed claim original word := by
  dsimp only
  have balanced := original_control_return_and_unpaid_liability_cancel_in_the_actual_next seed claim word
  dsimp only at balanced
  rw [retained_original_income_keeps_the_actual_full_account,
    retained_actual_income_keeps_the_actual_full_account]
  exact retained_sum _ _ _ _ _ balanced

theorem every_coalition_keeps_contributions_and_original_financial_positions_separate
    (word : RawEvent Party Good Port Technology Instrument) (members : Party → Bool) (good : Good) :
    let original := Joint.Current.declareGross seed claim (Joint.Current.initial seed claim)
    read members good (originalIncome seed + actualIncome seed claim original word +
      liability seed claim (Joint.Current.advance seed claim original word)) =
        read members good (retainedOriginalIncome seed) + read members good (retainedActualIncome seed claim original word) := by
  dsimp only
  rw [full_account_keeps_actual_production_other_transfers_and_original_native_positions,map_add]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

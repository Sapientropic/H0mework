import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Society

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]

/-- A coalition is a restriction of the original finite effect. Neither a
population list nor a price for exchanging different goods is required. -/
def read (members : Party → Bool) (good : Good) :
    Profit.Vector (Party := Party) (Good := Good) →+ ℚ :=
  Finsupp.liftAddHom fun key =>
    if members key.1 = true ∧ key.2 = good then AddMonoidHom.id ℚ else 0

omit [DecidableEq Party] in
theorem read_single (members : Party → Bool) (good : Good)
    (key : Party × Good) (quantity : ℚ) :
    read members good (Finsupp.single key quantity) =
      if members key.1 = true ∧ key.2 = good then quantity else 0 := by
  simp only [read,Finsupp.liftAddHom_apply_single]
  split <;> rfl

omit [DecidableEq Party] in
theorem read_nonpositive (members : Party → Bool) (good : Good)
    (effect : Profit.Vector (Party := Party) (Good := Good))
    (nonpositive : ∀ key, effect key ≤ 0) : read members good effect ≤ 0 := by
  unfold read
  rw [Finsupp.liftAddHom_apply]
  apply Finset.sum_nonpos
  intro key _
  by_cases selected : members key.1 = true ∧ key.2 = good
  · simpa only [if_pos selected,AddMonoidHom.id_apply] using nonpositive key
  · simp only [if_neg selected,AddMonoidHom.zero_apply,le_refl]

variable {Port Technology Instrument : Type}

/-- Full coalition income uses the actual original material and financial
changes. In particular, issuance and assignments need not vanish for a coalition. -/
theorem full_account_is_actual_material_and_native_change
    (members : Party → Bool) (good : Good)
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    read members good (Profit.fullIncome law items) =
      read members good (Financial.inventoryMaterial law items) +
      read members good (Financial.value law (Financial.inventoryClaims law items)) := by
  exact map_add (read members good) _ _

theorem productive_contribution_and_transfers_are_counted_separately
    (members : Party → Bool) (good : Good)
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    read members good (Profit.fullIncome law items) =
      read members good (Profit.production law items) +
      read members good (Profit.transfers law items) := by
  rw [Profit.every_original_inventory_separates_production_and_existing_positions,map_add]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition

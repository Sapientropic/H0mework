import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Address
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- Both legs of the fraction are measured in the same actual material
unit. The denominator is net received stock at the original advance cut. -/
def retainedShare (source : C) (advance allocation : Script) (bearer : Party) (good : Good) : ℚ :=
  stockChange source (advance ++ allocation) bearer good / stockChange source advance bearer good

def requiredShare (source : C) (advance allocation : Script) (word : Word) (bearer : Party) (good : Good) : ℚ :=
  let paid := advance ++ allocation
  minimumReserve (fundedLaw source paid) (stockBaseline source paid) word bearer good /
    stockChange source advance bearer good

/-- The allocation is a real root prefix. Its other signed stock changes,
policy, claims and technology still participate in admission. -/
theorem actual_retention_iff_tight_share_and_other_original_requirements
    (source : C) (advance allocation : Script) (word : Word) (bearer : Party) (good : Good)
    (received : 0 < stockChange source advance bearer good)
    (kept : 0 ≤ stockChange source (advance ++ allocation) bearer good) :
    let paid := advance ++ allocation
    Accepted (fundedLaw source paid) (Execution.endAt source paid).raw word ↔
      Guards (fundedLaw source paid) (stockChange source paid) (stockBaseline source paid) word ∧
      (∀ otherPerson otherGood, (otherPerson, otherGood) ≠ (bearer, good) →
        FitsAt (fundedLaw source paid) otherPerson otherGood (stockChange source paid otherPerson otherGood)
          (stockBaseline source paid) word) ∧
      requiredShare source advance allocation word bearer good ≤ retainedShare source advance allocation bearer good := by
  dsimp only
  rw [real_funding_admits_the_original_word_iff_exact_stock_and_gates, fits_through_iff_all_addresses]
  have chosen := a_nonnegative_reserve_fits_at_its_original_address_iff_tight
    (fundedLaw source (advance ++ allocation)) bearer good _ kept (stockBaseline source (advance ++ allocation)) word
  have scale :
      requiredShare source advance allocation word bearer good ≤ retainedShare source advance allocation bearer good ↔
      minimumReserve (fundedLaw source (advance ++ allocation)) (stockBaseline source (advance ++ allocation))
        word bearer good ≤ stockChange source (advance ++ allocation) bearer good :=
    div_le_div_iff_of_pos_right received
  constructor
  · rintro ⟨gates, fit⟩
    exact ⟨gates, fun party unit _ => fit party unit, scale.mpr (chosen.mp (fit bearer good))⟩
  · rintro ⟨gates, other, threshold⟩
    refine ⟨gates, fun party unit => ?_⟩
    by_cases same : (party, unit) = (bearer, good)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact chosen.mpr (scale.mp threshold)
    · exact other party unit same

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

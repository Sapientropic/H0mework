import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Linear
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (reading : LinearReadout Party Good)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (word : RawEvent Party Good Port Technology Instrument)
  (settlements : ∀ request ∈ word, ∃ instrument debtor holder quantity,
    request.operation = .settle instrument debtor holder quantity)

include settlements in
theorem every_fixed_nonnegative_readout_has_the_same_zero_extra_settlement_value :
    value reading input before (word.map Compile.RawInput.primitive) = 0 := by
  unfold value
  have zeroItems : ((Programme.items input before (word.map Compile.RawInput.primitive)).map
      (itemValue reading (Physical.Public.interpreter input))).sum = 0 := by
    apply List.sum_eq_zero
    intro amount member
    obtain ⟨item,listed,rfl⟩ := List.mem_map.mp member
    unfold itemValue
    apply List.sum_eq_zero
    intro amount member
    obtain ⟨channel,member,rfl⟩ := List.mem_map.mp member
    rw [source_settlement_inventories_have_no_hidden_resource_debit input before word settlements item listed channel]
    rfl
  rw [zeroItems,Programme.pure_microsteps_have_zero_elapsed_cost]
  simp only [mul_zero,add_zero]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost

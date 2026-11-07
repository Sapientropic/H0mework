import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Cost.Lower

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

variable (code : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))

theorem the_full_source_readout_dominates_its_fuel_projection :
    Cost.value reading input before code ≤ Cost.value fullReading input before code := by
  apply add_le_add
  · apply List.sum_le_sum
    intro item member
    unfold Cost.itemValue
    apply List.sum_le_sum
    intro channel member
    unfold Cost.weightedFlow
    apply List.sum_le_sum
    intro entry member
    apply mul_le_mul_of_nonneg_right _ (Cost.actualPart_is_the_original_nonnegative_flow
      (Physical.Public.interpreter input) item.before item.request channel entry member)
    cases entry.1.2 <;> norm_num [reading,fullReading]
  · apply mul_le_mul_of_nonneg_right _ (Programme.clockCost_nonnegative input before code)
    norm_num [reading,fullReading]

theorem all_complete_programmes_exceed_the_floor_in_the_full_source_readout
    (cleared : RawCleared code) : 1 < Cost.value fullReading input before code :=
  (every_complete_original_programme_pays_strictly_more_than_the_floor code cleared).trans_le
    (the_full_source_readout_dominates_its_fuel_projection code)

theorem full_value_of_an_original_prefix_and_suffix
    (start : Actual.Current (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))
    (first second : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit)) :
    Cost.value fullReading input start (first ++ second) = Cost.value fullReading input start first +
      Cost.value fullReading input (Programme.run input start first) second := by
  simp only [Cost.value,Programme.items_append,List.map_append,List.sum_append,Programme.elapsed_append]
  ring

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment

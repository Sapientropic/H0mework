import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.NativeMinimum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader)

/-- The actual source prefix is common to every continuation at this cut.
This is not a minimum over alternative histories before the cut. -/
def initialMaterial (_source : Clearing.Position input depth count reader) :=
  Physical.Public.stateAt input depth count 0 0 [] []

def fullHistoryCost (reading : Cost.LinearReadout Party Good)
    (continuation : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) : ℚ :=
  Cost.value reading input (initialMaterial source) (source.past ++ continuation)

theorem the_cost_origin_is_the_same_actual_source_cut :
    Programme.run input (initialMaterial source) source.past = Cost.Canonical.before source :=
  Programme.the_comparison_programme_is_the_literal_original_source_suffix input source.past depth count 0 0 [] []

theorem the_actual_common_past_is_not_deleted_from_total_cost
    (reading : Cost.LinearReadout Party Good)
    (continuation : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    fullHistoryCost source reading continuation =
      Cost.value reading input (initialMaterial source) source.past +
        Cost.value reading input (Cost.Canonical.before source) continuation := by
  unfold fullHistoryCost
  rw [the_complete_source_cost_is_the_actual_prefix_plus_its_continuation,
    the_cost_origin_is_the_same_actual_source_cut]

attribute [local irreducible] fullHistoryCost initialMaterial Cost.value
  Cost.Canonical.programme Cost.Canonical.before

theorem a_minimum_at_the_actual_cut_remains_a_minimum_with_its_actual_past
    (reading : Cost.LinearReadout Party Good)
    (left right : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (minimum : Cost.value reading input (Cost.Canonical.before source) left ≤
      Cost.value reading input (Cost.Canonical.before source) right) :
    fullHistoryCost source reading left ≤ fullHistoryCost source reading right := by
  calc
    _ = Cost.value reading input (initialMaterial source) source.past +
        Cost.value reading input (Cost.Canonical.before source) left :=
      the_actual_common_past_is_not_deleted_from_total_cost source reading left
    _ ≤ Cost.value reading input (initialMaterial source) source.past +
        Cost.value reading input (Cost.Canonical.before source) right :=
      by simpa only [add_comm] using
        (_root_.add_le_add_left minimum (Cost.value reading input (initialMaterial source) source.past))
    _ = fullHistoryCost source reading right :=
      (the_actual_common_past_is_not_deleted_from_total_cost source reading right).symm

theorem the_actual_native_minimum_preserves_all_already_incurred_source_costs
    (reading : Cost.LinearReadout Party Good)
    (rival : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    fullHistoryCost source reading (Cost.Canonical.programme source) ≤ fullHistoryCost source reading rival := by
  exact a_minimum_at_the_actual_cut_remains_a_minimum_with_its_actual_past source reading
    (Cost.Canonical.programme source) rival
    (Cost.Canonical.every_fixed_nonnegative_readout_is_globally_minimal_over_all_source_programmes source reading rival)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root

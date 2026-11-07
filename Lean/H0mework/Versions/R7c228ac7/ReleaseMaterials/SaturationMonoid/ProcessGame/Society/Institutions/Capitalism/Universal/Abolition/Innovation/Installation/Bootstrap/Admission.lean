import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Inventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

local instance (origin current : Raw) (members : List Party)
    (word : RawEvent Party Good Bool Nat Unit) :
    Decidable (Review.Guarded.Checks (Macro.Public.Scope.checkInput input) origin current members word) := by
  unfold Review.Guarded.Checks
  infer_instance

theorem the_original_checks_cover_any_member_subset (origin current : Raw)
    (word : RawEvent Party Good Bool Nat Unit) (all members : List Party)
    (included : ∀ person ∈ members, person ∈ all)
    (checked : Review.Guarded.Checks (Macro.Public.Scope.checkInput input) origin current all word) :
    Review.Guarded.Checks (Macro.Public.Scope.checkInput input) origin current members word := by
  refine ⟨checked.1, ?_, checked.2.2.1, ?_, checked.2.2.2.2.1, ?_, checked.2.2.2.2.2.2⟩
  · intro cell original
    apply checked.2.1 cell
    obtain ⟨person, present, requirement⟩ := List.mem_flatMap.mp original
    exact List.mem_flatMap.mpr ⟨person, included person present, requirement⟩
  · intro person present
    exact checked.2.2.2.1 person (included person present)
  · intro person present
    exact checked.2.2.2.2.2.1 person (included person present)

set_option maxHeartbeats 1200000 in
theorem every_first_source_variant_pays_the_original_common_work :
    ∀ current ∈ firstRawVariants,
      Review.Guarded.Checks (Macro.Public.Scope.checkInput input) Control.Scenario.seed current [0,1,2]
        (Functions.Revision.PublicPlan.executable Control.Scenario.commonWork) := by
  have verified : firstRawVariants.all (fun current => decide
      (Review.Guarded.Checks (Macro.Public.Scope.checkInput input) Control.Scenario.seed current [0,1,2]
        (Functions.Revision.PublicPlan.executable Control.Scenario.commonWork))) = true := by decide +kernel
  intro current original
  exact of_decide_eq_true ((List.all_eq_true.mp verified) current original)

theorem every_first_source_variant_pays_any_actual_member_inventory
    (current : Raw) (original : current ∈ firstRawVariants) (members : List Party) :
    Review.Guarded.Checks (Macro.Public.Scope.checkInput input) Control.Scenario.seed current members
      (Functions.Revision.PublicPlan.executable Control.Scenario.commonWork) := by
  apply the_original_checks_cover_any_member_subset _ _ _ [0,1,2] members
  · intro person _
    have present : ∀ person : Party, person ∈ ([0,1,2] : List Party) := by decide +kernel
    exact present person
  · exact every_first_source_variant_pays_the_original_common_work current original

theorem the_actual_first_source_pays_the_whole_public_scope
    (snapshot : CursorAt)
    (original : (Physical.stateAt input 0 count 0 0 snapshot.past).raw ∈ firstRawVariants) :
    Functions.Revision.PublicPlan.Checks input 0 count 0 0 snapshot Control.Scenario.commonWork := by
  change Review.Guarded.Checks (Macro.Public.Scope.checkInput input) (Actual.origin input 0 count)
    (Physical.stateAt input 0 count 0 0 snapshot.past).raw _ _
  rw [show Actual.origin input 0 count = Control.Scenario.seed from
    the_original_physical_seed_is_the_actual_capital_successor]
  exact every_first_source_variant_pays_any_actual_member_inventory _ original _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Steps
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Enactment
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Inputs
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.PreRead

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem every_pre_read_request_is_consumed_on_the_original_actual_root
    (nature : RequestAt) (index : Nat) (within : index ≤ 5) :
    (actualPublicVisit nature index).snapshot = Physical.Prefix.cursor ((beforeReadInputs nature).take (index + 1)) := by
  induction index with
  | zero =>
      refine (the_first_actual_public_visit_keeps_the_literal_source_body nature).trans ?_
      rw [the_pre_read_source_inventory_is_the_original_five_requests]
      rfl
  | succ index inherited =>
      have earlier := inherited (show index ≤ 5 by omega)
      let position : Fin 5 := ⟨index, by omega⟩
      have source : selected nature ((firstOrigin nature).germ.snapshot.past ++
          (actualPublicVisit nature index).snapshot.past) = .primitive (preReadRequest nature position) := by
        have projected := congrArg (fun snapshot : CursorAt => selected nature
          ((firstOrigin nature).germ.snapshot.past ++ snapshot.past)) earlier
        have sourcePast := congrArg (fun past : List InputAt => selected nature
          ((firstOrigin nature).germ.snapshot.past ++ past))
            (Physical.Prefix.past_readback ((beforeReadInputs nature).take (index + 1)))
        exact projected.trans (sourcePast.trans (every_pre_read_position_selects_its_original_next_primitive nature _
          (the_original_first_prefix_has_no_unperformed_public_execution nature) position))
      have next := the_actual_primitive_visit_has_its_same_next_source_cursor nature (actualAdmission nature)
        (the_first_admission_is_the_actual_source_compiler_choice nature) index (preReadRequest nature position) source
      exact next.trans ((congrArg (fun cursor : CursorAt =>
          Physical.next (Physical.receive cursor (.primitive (preReadRequest nature position)))) earlier).trans
        ((Physical.Prefix.cursor_append _ _).symm.trans
          (congrArg Physical.Prefix.cursor (the_next_pre_read_prefix_adds_exactly_its_source_request nature position).symm)))

theorem the_open_nature_is_an_actual_original_attempt_after_paid_preparation (nature : RequestAt) :
    (actualPublicVisit nature 4).snapshot = Physical.Prefix.cursor
      ([.execute Control.Scenario.commonWork] ++ preparation.map Compile.RawInput.primitive ++ [.primitive nature]) := by
  have actual := every_pre_read_request_is_consumed_on_the_original_actual_root nature 4 (by omega)
  have inputShape : (beforeReadInputs nature).take (4 + 1) =
      [.execute Control.Scenario.commonWork] ++ preparation.map Compile.RawInput.primitive ++ [.primitive nature] := by
    rw [the_pre_read_source_inventory_is_the_original_five_requests,
      the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
    rfl
  exact actual.trans (congrArg Physical.Prefix.cursor inputShape)

theorem the_actual_probe_precedes_the_same_root_local_observation (nature : RequestAt) :
    (actualPublicVisit nature 5).snapshot = Physical.Prefix.cursor (beforeReadInputs nature) := by
  have actual := every_pre_read_request_is_consumed_on_the_original_actual_root nature 5 (by omega)
  have length : (beforeReadInputs nature).length = 6 := by
    rw [the_pre_read_source_inventory_is_the_original_five_requests]
    rfl
  exact actual.trans (congrArg Physical.Prefix.cursor
    (List.take_of_length_le (show (beforeReadInputs nature).length ≤ 5 + 1 by omega)))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

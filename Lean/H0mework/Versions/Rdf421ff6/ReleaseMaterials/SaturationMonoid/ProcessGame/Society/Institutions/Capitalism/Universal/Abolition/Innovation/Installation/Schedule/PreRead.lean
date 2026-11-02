import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Inputs
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Readback

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Abolition.Root.Registered

def preReadRequest (nature : RequestAt) (position : Fin 5) : RequestAt :=
  ([Control.Scenario.issue,Control.Scenario.payout,quotedMechanism.investmentRequest,
    nature,Control.Scenario.production 0] : List RequestAt).get ⟨position.val, position.isLt⟩

theorem the_pre_read_source_inventory_is_the_original_five_requests (nature : RequestAt) :
    beforeReadInputs nature = [.execute Control.Scenario.commonWork,
      .primitive Control.Scenario.issue,.primitive Control.Scenario.payout,
      .primitive quotedMechanism.investmentRequest,.primitive nature,
      .primitive (Control.Scenario.production 0)] := by
  rw [beforeReadInputs, the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
  rfl

theorem every_pre_read_position_selects_its_original_next_primitive
    (nature : RequestAt) (oldPast : List InputAt)
    (original : ∀ raw ∈ oldPast, beforePublic raw = true) (position : Fin 5) :
    selected nature (oldPast ++ (beforeReadInputs nature).take (position.val + 1)) =
      .primitive (preReadRequest nature position) := by
  rw [the_pre_read_source_inventory_is_the_original_five_requests]
  have selectAt (rest : List InputAt) : publicPast (oldPast ++ .execute Control.Scenario.commonWork :: rest) =
      .execute Control.Scenario.commonWork :: rest :=
    (the_first_actual_public_execution_recovers_its_original_source_cut oldPast _ rest original).2
  fin_cases position <;>
    simp only [Nat.zero_add, List.take_succ_cons, List.take_zero] <;>
    unfold selected selectedWith <;>
    rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, selectAt] <;>
    rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2] <;> rfl

theorem the_next_pre_read_prefix_adds_exactly_its_source_request
    (nature : RequestAt) (position : Fin 5) :
    (beforeReadInputs nature).take (position.val + 2) =
      (beforeReadInputs nature).take (position.val + 1) ++ [.primitive (preReadRequest nature position)] := by
  rw [the_pre_read_source_inventory_is_the_original_five_requests]
  fin_cases position <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

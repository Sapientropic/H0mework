import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Payment.Primitive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_first_settlement_prefix_has_the_original_work_raw (oldPast : List InputAt) (version : Nat) :
    (Physical.Public.stateAt input 0 count 0 0 oldPast
      (submittedInputs oldPast (Control.Scenario.discovery version) ++
        [.primitive (riskLiability version),.execute Control.Scenario.commonWork])).raw =
      (performanceWork (Physical.stateAt input 0 count 0 0 oldPast).raw version).next.raw := by
  have same := the_original_performance_prefix_has_its_actual_raw oldPast version [.execute Control.Scenario.commonWork]
    (by intro raw member; obtain rfl := List.mem_singleton.mp member; intro impossible; cases impossible)
  have association := congrArg (fun past : List InputAt => (Physical.Public.stateAt input 0 count 0 0 oldPast past).raw)
    (List.append_assoc (submittedInputs oldPast (Control.Scenario.discovery version))
      [.primitive (riskLiability version)] [.execute Control.Scenario.commonWork]).symm
  exact association.trans same

theorem the_last_settlement_prefix_has_the_original_first_payment_raw (oldPast : List InputAt) (version : Nat) :
    (Physical.Public.stateAt input 0 count 0 0 oldPast
      (submittedInputs oldPast (Control.Scenario.discovery version) ++
        [.primitive (riskLiability version),.execute Control.Scenario.commonWork,.primitive (firstSettlement version)])).raw =
      (performanceFirstSettlement (Physical.stateAt input 0 count 0 0 oldPast).raw version).next.raw := by
  have same := the_original_performance_prefix_has_its_actual_raw oldPast version
    [.execute Control.Scenario.commonWork,.primitive (firstSettlement version)]
    (by
      intro raw member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> intro impossible <;> cases impossible)
  have association := congrArg (fun past : List InputAt => (Physical.Public.stateAt input 0 count 0 0 oldPast past).raw)
    (List.append_assoc (submittedInputs oldPast (Control.Scenario.discovery version)) [.primitive (riskLiability version)]
      [.execute Control.Scenario.commonWork,.primitive (firstSettlement version)]).symm
  exact association.trans same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

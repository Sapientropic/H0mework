import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Grouping
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing.Restoration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Entitlement.Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def originalLeg (leg : window.Leg) : Profit.Vector (Party := Party) (Good := Good) :=
  (Financial.fullChange window.input.law leg.item.val.before leg.item.val.request).filter
    (fun key => key.2 = leg.good)

def originalControl : Profit.Vector (Party := Party) (Good := Good) :=
  ((Entitlement.Source.demands window).map fun demand => originalLeg window demand.leg).sum

theorem an_original_demand_is_the_actual_transfer_in_its_original_unit
    (demand : Entitlement.Source.Demand window) :
    originalLeg window demand.leg = incidence (Entitlement.Duty.demandKey window demand) demand.quantity := by
  exact Clearing.the_original_transfer_has_its_exact_material_unit_restriction
    window.input.law demand.leg.item.val.before demand.leg.item.val.request
    demand.leg.sender demand.leg.recipient demand.leg.goods demand.leg.good
    demand.leg.operation demand.leg.accepted

theorem every_source_control_leg_is_counted_once_in_the_original_matrix :
    originalControl window = position (Entitlement.Duty.scope window) (Entitlement.Duty.quantity window) := by
  unfold originalControl
  have same : ((Entitlement.Source.demands window).map fun demand => originalLeg window demand.leg) =
      ((Entitlement.Source.demands window).map fun demand =>
        incidence (Entitlement.Duty.demandKey window demand) demand.quantity) := by
    apply List.map_congr_left
    intro demand _
    exact an_original_demand_is_the_actual_transfer_in_its_original_unit window demand
  rw [same]
  exact (grouping_preserves_every_original_transfer incidence (Entitlement.Duty.scope window)
    (Entitlement.Duty.every_group_is_enumerated_once window)
    (Entitlement.Source.demands window) (Entitlement.Duty.demandKey window)
    Entitlement.Source.Demand.quantity (fun demand member =>
      List.mem_dedup.mpr (List.mem_map.mpr ⟨demand,member,rfl⟩))).symm

theorem reading_a_source_demand_keeps_its_actual_leg
    (leg : window.Leg) (demand : Entitlement.Source.Demand window)
    (readout : Entitlement.Source.readDemand window leg = some demand) : demand.leg = leg := by
  unfold Entitlement.Source.readDemand at readout
  split at readout
  · cases readout
    rfl
  · cases readout

theorem an_exercised_original_grant_is_not_control_debt
    (leg : window.Leg) (grant : Entitlement.Source.ExercisedGrant window leg) :
    Entitlement.Source.readDemand window leg = none := by
  unfold Entitlement.Source.readDemand
  split
  · rename_i controlled
    exact False.elim ((Entitlement.Source.an_unconsented_control_return_has_no_exercised_financial_grant
      window leg controlled) ⟨grant⟩)
  · rfl

theorem a_signed_original_gift_keeps_its_own_source
    (leg : window.Leg) (signed : leg.item.val.request.signer = leg.sender) :
    Entitlement.Source.readDemand window leg = none :=
  an_exercised_original_grant_is_not_control_debt window leg (.sourceSignature signed)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution

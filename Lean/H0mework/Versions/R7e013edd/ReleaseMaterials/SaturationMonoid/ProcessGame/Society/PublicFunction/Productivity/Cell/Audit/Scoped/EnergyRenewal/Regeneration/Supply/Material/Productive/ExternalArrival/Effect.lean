import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Packet

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Effect
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def quantity : ℚ := Packet.before.stock 1 .feedstock-Packet.after.stock 1 .feedstock
def elapsed : ℚ := Packet.after.clock-Packet.before.clock
def rounds : Nat := Packet.after.round-Packet.before.round

theorem original_source_pays_three_units_and_six_steps : quantity=3 ∧ elapsed=6 ∧ rounds=6 := by
  and_intros <;> decide +kernel

def credit (before : Current) : Current := {before with
  stock:=fun p g => before.stock p g + if p=customer ∧ g=.feed then quantity else 0
  clock:=before.clock+elapsed
  round:=before.round+rounds}

open private Supply.Session.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open private Finance.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance

def receive {plan : Plan} (state : Finance.State plan) : Finance.State plan :=
  let old:=state.session
  let current:=credit old.current
  let session : Session plan:=Supply.Session.mk old.origin old.received old.window current old.target old.history
    (by exact old.finance) (by exact old.providerFinance)
  Finance.State.mk session state.account

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Effect

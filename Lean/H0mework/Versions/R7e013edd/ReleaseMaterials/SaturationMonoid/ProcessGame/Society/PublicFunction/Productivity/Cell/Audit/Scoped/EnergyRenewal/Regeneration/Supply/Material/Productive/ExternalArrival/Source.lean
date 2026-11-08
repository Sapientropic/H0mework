import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Wire
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
namespace Upstream
open Protocol.SymbolicAuthentication
abbrev actual := (ProviderMaterialSource.trace 3 true true).before.current

/-- Specialization of an existing occurrence, not an independently funded seed. -/
def current : ProviderCurrent where
  stock := fun p g => match p.val,g with
    | 0,.feedstock => source_value% (actual.stock 0 .feedstock)
    | 0,.service => source_value% (actual.stock 0 .service)
    | 0,.waste => source_value% (actual.stock 0 .waste)
    | 0,.energy => source_value% (actual.stock 0 .energy)
    | 0,.labor => source_value% (actual.stock 0 .labor)
    | 1,.feedstock => source_value% (actual.stock 1 .feedstock)
    | 1,.service => source_value% (actual.stock 1 .service)
    | 1,.waste => source_value% (actual.stock 1 .waste)
    | 1,.energy => source_value% (actual.stock 1 .energy)
    | 1,.labor => source_value% (actual.stock 1 .labor)
    | _,.feedstock => source_value% (actual.stock 2 .feedstock)
    | _,.service => source_value% (actual.stock 2 .service)
    | _,.waste => source_value% (actual.stock 2 .waste)
    | _,.energy => source_value% (actual.stock 2 .energy)
    | _,.labor => source_value% (actual.stock 2 .labor)
  claims := fun _ p q => match p.val,q.val with
    | 0,0 => source_value% (actual.claims () 0 0)
    | 0,1 => source_value% (actual.claims () 0 1)
    | 0,_ => source_value% (actual.claims () 0 2)
    | 1,0 => source_value% (actual.claims () 1 0)
    | 1,1 => source_value% (actual.claims () 1 1)
    | 1,_ => source_value% (actual.claims () 1 2)
    | _,0 => source_value% (actual.claims () 2 0)
    | _,1 => source_value% (actual.claims () 2 1)
    | _,_ => source_value% (actual.claims () 2 2)
  technology := source_value% actual.technology
  clock := source_value% actual.clock
  round := source_value% actual.round

theorem exact_occurrence : current=actual := by
  apply RawCurrent.ext
  · funext p g;fin_cases p <;> cases g <;> source_refl
  · funext i p q;cases i;fin_cases p <;> fin_cases q <;> source_refl
  all_goals source_refl

theorem actually_produced : current.stock 1 .feedstock=3 ∧
    current.stock 2 .waste=0 ∧ current.stock 2 .energy=0 ∧ current.stock 2 .labor=0 := by
  rw [exact_occurrence]
  have h:=ProviderMaterialSource.three_actual_productions_and_transfers_generate_three_new_feedstock_units
  exact ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

def contribute (quantity : ℚ) : ProviderAction := ⟨1,[],.reserve 1,[],.use 1 [(.feedstock,quantity)] .contribution⟩
abbrev law := RecycledQuorumMaterial.law

theorem export_paid (before : ProviderCurrent) (quantity : ℚ)
    (nonnegative : 0≤quantity) (funded : quantity≤before.stock 1 .feedstock) :
    law.Valid before (contribute quantity) := by
  simp [law,RecycledQuorumMaterial.law,Mandate.law,Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
    Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,RawLaw.requiredPorts,
    RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,contribute,flowAt,locate,amount,nonnegative,funded]
end Upstream

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival

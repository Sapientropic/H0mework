import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Production
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Canonical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev AuditInput := ProgrammeSource.Input Party Good Cell.Port Cell.Technology Unit
abbrev ProviderInput := ProgrammeSource.Input ProviderParty ProviderGood ProviderPort ProviderTechnology Unit
def auditSources (input : AuditInput) := input
def providerSources (input : ProviderInput) := input
abbrev AuditAccount := (Financial.Family.process auditSources).GeneratedState
abbrev ProviderAccount := (Financial.Family.process providerSources).GeneratedState

def auditGenesis : AuditAccount :=
  (Financial.Family.Embedding.accountAt auditSources Cell.source.input 2).account

/-- These are the original source and cut, not a loan reconstructed from a raw balance. -/
def providerNativeInput : ProviderInput := providerOrigin.model.source.input
def providerNativeOrdinal : Nat := providerDepth+2

theorem provider_input_is_the_original_source :
    providerNativeInput=providerOrigin.model.source.input := rfl

theorem provider_ordinal_is_the_original_cut : providerNativeOrdinal=providerDepth+2 := rfl

def providerGenesis : ProviderAccount :=
  (Financial.Family.Embedding.accountAt providerSources providerNativeInput providerNativeOrdinal).account

theorem audit_genesis_keeps_the_full_original_account :
    auditGenesis.current=Financial.Family.Embedding.state auditSources Cell.source.input
      (Cell.Finance.account 2).current :=
  Financial.Family.Embedding.accountAt_full_state _ _ _

theorem provider_genesis_keeps_the_full_original_account :
    providerGenesis.current=Financial.Family.Embedding.state providerSources providerNativeInput
      (Financial.accountAt providerNativeInput providerNativeOrdinal).current :=
  Financial.Family.Embedding.accountAt_full_state _ _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement

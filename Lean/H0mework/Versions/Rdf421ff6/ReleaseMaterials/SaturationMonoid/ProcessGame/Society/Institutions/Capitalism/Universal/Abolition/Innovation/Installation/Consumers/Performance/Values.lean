import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

def performanceWork (before : Raw) (version : Nat) := Physical.Public.compile input
  (⟨trialRawAfterRiskLiability before (Control.Scenario.discovery version) (riskLiability version),.seeking,[]⟩ : PhysicalState)
  (.execute Control.Scenario.commonWork)

def performanceFirstSettlement (before : Raw) (version : Nat) :=
  Physical.Public.compile input (performanceWork before version).next (.primitive (firstSettlement version))

def performanceLastSettlement (before : Raw) (version : Nat) :=
  Physical.Public.compile input (performanceFirstSettlement before version).next (.primitive (lastSettlement version))

def performanceFinalRaw (before : Raw) (version : Nat) := (performanceLastSettlement before version).next.raw

def PaidPerformance (before : Raw) (version : Nat) : Prop :=
  (performanceWork before version).isAccepted = true ∧
    (performanceFirstSettlement before version).isAccepted = true ∧
    (performanceLastSettlement before version).isAccepted = true ∧
    (∀ debtor ∈ ([0,1,2] : List Party), ∀ creditor ∈ ([0,1,2] : List Party),
      (performanceFinalRaw before version).claims () debtor creditor = before.claims () debtor creditor) ∧
    (performanceFinalRaw before version).technology = version ∧
    (performanceFinalRaw before version).clock = 4 ∧
    ((performanceWork before version).next.raw.stock (if version = 0 then 1 else 0) .material -
      (performanceFirstSettlement before version).next.raw.stock (if version = 0 then 1 else 0) .material =
        if version = 0 then 2 else 6) ∧
    ((performanceFirstSettlement before version).next.raw.stock 0 .material -
      (performanceFinalRaw before version).stock 0 .material = if version = 0 then 6 else 3)

instance (before : Raw) (version : Nat) : Decidable (PaidPerformance before version) := by
  unfold PaidPerformance
  infer_instance

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

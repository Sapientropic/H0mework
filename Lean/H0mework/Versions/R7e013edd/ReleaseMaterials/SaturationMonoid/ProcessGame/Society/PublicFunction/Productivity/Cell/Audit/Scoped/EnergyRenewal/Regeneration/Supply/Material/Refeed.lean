import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open Institutions.Capitalism.Universal.Source.Program
namespace Refeed
open Protocol.SymbolicAuthentication

abbrev donor : Actor := .inr 2
abbrev wasteOwner : Actor := .inr 1
abbrev fund : ProviderAction := WorkerInputLaw.energyLabor
abbrev collect : ProviderAction := WorkerInputLaw.waste
abbrev recycle : ProviderAction := RecycledQuorumMaterial.recycle
abbrev transport : ProviderAction := UpstreamFeedLaw.request

/-- The existing donor producer and transport, on the current material carrier. -/
def word : List ProviderAction := [fund,collect,recycle,transport]
theorem original_producer_and_original_transport :
    word=DonorRegenerationLaw.word++[UpstreamFeedLaw.request] := rfl

/-- These are the actual primitive recipe inputs, without the old network's reserve requirement. -/
structure Inputs (current : ProviderCurrent) : Prop where
  energy : 1 ≤ current.stock 0 .energy
  labor : 1 ≤ current.stock 0 .labor
  waste : 1 ≤ current.stock 1 .waste
  donorFeed : 0 ≤ current.stock 2 .feedstock
  donorWaste : 0 ≤ current.stock 2 .waste
  donorEnergy : 0 ≤ current.stock 2 .energy
  donorLabor : 0 ≤ current.stock 2 .labor
  willing : current.technology.technology=true

def after (current : ProviderCurrent) : ProviderCurrent := {current with
  stock := fun p g => current.stock p g + (if p=0 ∧ g=.feedstock then 1 else 0) -
    (if (p=0 ∧ (g=.energy ∨ g=.labor)) ∨ (p=1 ∧ g=.waste) then 1 else 0)
  clock := current.clock+1
  round := current.round+1}

theorem actual_phases (current : ProviderCurrent) (inputs : Inputs current) :
    ∀ item∈providerLaw.rawItems current word,providerLaw.Valid item.before item.request := by
  obtain ⟨energy,labor,waste,df,dw,de,dl,willing⟩ := inputs
  have phases : providerLaw.Valid current fund ∧
      providerLaw.Valid (providerLaw.paidStep current fund) collect ∧
      providerLaw.Valid (providerLaw.paidStep (providerLaw.paidStep current fund) collect) recycle ∧
      providerLaw.Valid (providerLaw.paidStep (providerLaw.paidStep
        (providerLaw.paidStep current fund) collect) recycle) transport := by
    simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
      RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
      providerLaw,UpstreamProductionLaw.law,WorkerInputLaw.law,FuelMandateLaw.law,FuelMandateLaw.base,
      RenewedQuorumMaterial.base,Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,
      Mandate.eraseOperation,Mandate.TaskUse,Repayment.Recovery.base,Repayment.Recovery.scope,
      Repayment.Recovery.task,RawLaw.paidStep,RawLaw.nextClaims,flowAt,locate,amount,
      fund,collect,recycle,transport,WorkerInputLaw.energyLabor,WorkerInputLaw.waste,
      RenewedQuorumMaterial.give,RecycledQuorumMaterial.waste,RecycledQuorumMaterial.recycle,
      UpstreamFeedLaw.request,FuelMandateLaw.give,willing] at *
    all_goals repeat' constructor
    all_goals linarith
  obtain ⟨a,b,c,d⟩ := phases
  intro item member
  simp only [word,RawLaw.rawItems,RawLaw.execute,RawLaw.step,if_pos a,if_pos b,if_pos c,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact a
  · exact b
  · exact c
  · exact d

theorem actual_next (current : ProviderCurrent) (inputs : Inputs current) :
    providerLaw.next current word=after current := by
  have paid := actual_phases current inputs
  have a := paid ⟨0,current,fund⟩ (by simp [word,RawLaw.rawItems,RawLaw.execute])
  have b := paid ⟨1,providerLaw.paidStep current fund,collect⟩ (by
    simp [word,RawLaw.rawItems,RawLaw.execute,RawLaw.step,if_pos a])
  have c := paid ⟨2,providerLaw.paidStep (providerLaw.paidStep current fund) collect,recycle⟩ (by
    simp [word,RawLaw.rawItems,RawLaw.execute,RawLaw.step,if_pos a,if_pos b])
  have d := paid ⟨3,providerLaw.paidStep (providerLaw.paidStep
    (providerLaw.paidStep current fund) collect) recycle,transport⟩ (by
    simp [word,RawLaw.rawItems,RawLaw.execute,RawLaw.step,if_pos a,if_pos b,if_pos c])
  simp only [word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos a,if_pos b,if_pos c,if_pos d]
  apply RawCurrent.ext
  · funext p g
    fin_cases p <;> cases g <;>
      simp [after,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,providerLaw,WorkerInputLaw.law,
        FuelMandateLaw.law,FuelMandateLaw.base,RenewedQuorumMaterial.base,Mandate.law,
        Repayment.Recovery.base,flowAt,locate,amount,fund,collect,recycle,transport,
        WorkerInputLaw.energyLabor,WorkerInputLaw.waste,RenewedQuorumMaterial.give,
        RecycledQuorumMaterial.waste,RecycledQuorumMaterial.recycle,UpstreamFeedLaw.request,FuelMandateLaw.give]
  all_goals rfl

/-- Resume from paid residual resources. Never resubmit an already funded worker stage. -/
def stages (current : Current) (deny : Bool) : List (Current → JointAction) :=
  if 1≤current.stock donor .feed then [fun state => liftProvider state transport]
  else
    let funding := current.stock donor .energy<1 ∨ current.stock donor .labor<1
    let bootstrap := if funding ∧ current.stock supplier .energy<1 then
      (if current.stock supplier .feed<1 then [fun _ => feed] else []) ++ [production] else []
    bootstrap ++
      (if funding then [fun state => liftProvider state fund] else []) ++
      (if current.stock donor .waste<1 then [fun state => liftProvider state collect] else []) ++
      [fun state => if deny then {liftProvider state recycle with signer:=customer} else liftProvider state recycle,
       fun state => liftProvider state transport]

theorem stages_historical (current : Current) (deny : Bool) :
    ∀ stage∈stages current deny,∀ before,Historical (stage before) := by
  unfold stages
  dsimp only
  repeat' split
  all_goals simp [Historical,feed,production,liftProvider,liftProviderOperation,
    fund,collect,recycle,transport,WorkerInputLaw.energyLabor,WorkerInputLaw.waste,
    RenewedQuorumMaterial.give,RecycledQuorumMaterial.waste,RecycledQuorumMaterial.recycle,
    UpstreamFeedLaw.request,FuelMandateLaw.give]
end Refeed
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply

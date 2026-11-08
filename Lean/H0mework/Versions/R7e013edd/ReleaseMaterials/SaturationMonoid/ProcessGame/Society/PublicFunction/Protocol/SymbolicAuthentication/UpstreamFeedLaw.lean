import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action material)
abbrev request := FuelMandateLaw.give

structure Resources (current : Current) : Prop where
  material : ResupplyLaw.Restorable (material current)
  empty : current.stock 0 .feedstock = 0
  donor : 1 ≤ current.stock 2 .feedstock
  labor : 1 ≤ current.stock 0 .labor
  energy : 0 ≤ current.stock 0 .energy
  waste : 2 ≤ current.stock 1 .waste
instance (current : Current) : Decidable (Resources current) :=
  decidable_of_iff (ResupplyLaw.Restorable (material current) ∧ current.stock 0 .feedstock = 0 ∧
      1 ≤ current.stock 2 .feedstock ∧ 1 ≤ current.stock 0 .labor ∧
      0 ≤ current.stock 0 .energy ∧ 2 ≤ current.stock 1 .waste)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩,
      fun h => ⟨h.material,h.empty,h.donor,h.labor,h.energy,h.waste⟩⟩

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good + (if party = 0 ∧ good = .feedstock then 1 else 0) -
    (if party = 2 ∧ good = .feedstock then 1 else 0)
  clock := current.clock+1
  round := current.round+1}

set_option linter.unusedSimpArgs false in
theorem valid (current : Current) (resources : Resources current) : UpstreamProductionLaw.law.Valid current request := by
  have willing := resources.material.willing
  change current.technology.technology = true at willing
  have donor := resources.donor
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    request,FuelMandateLaw.give,UpstreamProductionLaw.law,WorkerInputLaw.law,FuelMandateLaw.law,
    FuelMandateLaw.base,RenewedQuorumMaterial.base,Mandate.law,Mandate.eraseCurrent,
    Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,Repayment.Recovery.base,
    Repayment.Recovery.scope,Repayment.Recovery.task,flowAt,locate,amount,willing] at *
  all_goals linarith

set_option linter.unusedSimpArgs false in
theorem actual_next (law : RawLaw Party Good Port (Mandate.State Party Bool) Unit)
    (current : Current) (paid : law.Valid current request) (duration : law.duration current = 1) :
    law.next current [request] = successor current := by
  simp only [RawLaw.next,RawLaw.execute,RawLaw.step,if_pos paid]
  apply RawCurrent.ext
  · funext party good
    fin_cases party <;> cases good <;>
      simp [successor,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,request,FuelMandateLaw.give,
        flowAt,locate,amount]
  all_goals simp [successor,RawLaw.paidStep,RawLaw.nextClaims,request,FuelMandateLaw.give,duration]

theorem new_inputs (current : Current) (resources : Resources current) :
    UpstreamProductionLaw.Inputs (successor current) := by
  obtain ⟨possible,empty,donor,labor,energy,waste⟩ := resources
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := possible
  constructor
  · constructor <;> simp_all [successor,material]
  · simp [successor,empty]
  · simpa [successor] using labor
  · simpa [successor] using energy
  · simpa [successor] using waste

theorem needed_is_preserved (current : Current) (needed : WorkerInputSource.Needed current) :
    WorkerInputSource.Needed (successor current) := by
  simpa [WorkerInputSource.Needed,successor] using needed

theorem worker_inputs_are_still_missing_before_production (current : Current) (resources : Resources current) :
    ¬ WorkerInputLaw.Inputs (successor current) := by
  intro funded
  have deficit := funded.deficit
  simp [successor,resources.empty] at deficit
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedLaw

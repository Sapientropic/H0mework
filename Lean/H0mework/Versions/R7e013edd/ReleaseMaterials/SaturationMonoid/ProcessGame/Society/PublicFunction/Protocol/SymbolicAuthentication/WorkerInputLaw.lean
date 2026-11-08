import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action material)
abbrev law := FuelMandateLaw.law true
abbrev energyLabor : Action := RenewedQuorumMaterial.give 2
abbrev waste : Action := RecycledQuorumMaterial.waste
abbrev word : List Action := [energyLabor,waste]

structure Inputs (current : Current) : Prop where
  material : ResupplyLaw.Restorable (material current)
  energy : 1 ≤ current.stock 0 .energy
  labor : 2 ≤ current.stock 0 .labor
  waste : 2 ≤ current.stock 1 .waste
  fuel : 0 ≤ current.stock 0 .feedstock
  deficit : current.stock 0 .feedstock < 1

instance (current : Current) : Decidable (Inputs current) :=
  decidable_of_iff (ResupplyLaw.Restorable (material current) ∧ 1 ≤ current.stock 0 .energy ∧
    2 ≤ current.stock 0 .labor ∧ 2 ≤ current.stock 1 .waste ∧ 0 ≤ current.stock 0 .feedstock ∧ current.stock 0 .feedstock < 1)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩,
      fun h => ⟨h.material,h.energy,h.labor,h.waste,h.fuel,h.deficit⟩⟩

set_option linter.unusedSimpArgs false in
theorem actual_phases (current : Current) (inputs : Inputs current) :
    law.Valid current energyLabor ∧ law.Valid (law.paidStep current energyLabor) waste := by
  obtain ⟨possible,energy,labor,waste,fuel,deficit⟩ := inputs
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := possible
  change current.technology.technology = true at willing
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    law,FuelMandateLaw.law,FuelMandateLaw.base,RenewedQuorumMaterial.base,
    energyLabor,RenewedQuorumMaterial.give,waste,RecycledQuorumMaterial.waste,RawLaw.paidStep,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
    flowAt,locate,amount,willing,RecycledQuorumMaterial.material] at *
  all_goals repeat' constructor
  all_goals linarith

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good +
    (if party = 2 ∧ (good = .waste ∨ good = .energy ∨ good = .labor) then 1 else 0) -
    (if (party = 0 ∧ (good = .energy ∨ good = .labor)) ∨ (party = 1 ∧ good = .waste) then 1 else 0)
  clock := current.clock+1
  round := current.round+1}

set_option linter.unusedSimpArgs false in
theorem actual_next (current : Current) (inputs : Inputs current) :
    law.next current word = successor current ∧
      ∀ item ∈ law.rawItems current word, law.Valid item.before item.request := by
  obtain ⟨first,second⟩ := actual_phases current inputs
  constructor
  · simp only [word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos first,if_pos second]
    apply RawCurrent.ext
    · funext party good
      fin_cases party <;> cases good <;>
        simp [successor,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,FuelMandateLaw.law,
          FuelMandateLaw.base,RenewedQuorumMaterial.base,energyLabor,RenewedQuorumMaterial.give,
          waste,RecycledQuorumMaterial.waste,Mandate.law,Repayment.Recovery.base,flowAt,locate,amount]
    all_goals rfl
  · intro item member
    simp only [RawLaw.rawItems,word,RawLaw.execute,RawLaw.step,if_pos first,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

theorem upstream_transfers_generate_all_original_worker_and_material_inputs
    (current : Current) (inputs : Inputs current) : FuelMaterialSource.Inputs (successor current) := by
  obtain ⟨possible,energy,labor,waste,fuel,deficit⟩ := inputs
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := possible
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp_all [successor,material]
  · constructor <;> simp_all [successor,material]
    all_goals linarith
  · simpa [successor] using fuel
  · simpa [successor] using deficit
  · simp [successor];linarith
  · simp [successor];linarith

theorem no_new_total_stock_or_claim_is_minted (current : Current) (good : Good) :
    (successor current).stock 0 good+(successor current).stock 1 good+(successor current).stock 2 good =
      current.stock 0 good+current.stock 1 good+current.stock 2 good ∧
      (successor current).claims = current.claims ∧ (successor current).technology = current.technology := by
  refine ⟨?_,rfl,rfl⟩
  cases good <;> simp [successor] <;> ring

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputLaw

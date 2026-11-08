import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action material)
abbrev law := WorkerInputLaw.law
abbrev request : Action := RenewedQuorumMaterial.renew
abbrev word : List Action := [request]

structure Inputs (current : Current) : Prop where
  material : ResupplyLaw.Restorable (material current)
  fuel : current.stock 0 .feedstock = 1
  labor : 1 ≤ current.stock 0 .labor
  energy : 0 ≤ current.stock 0 .energy
  waste : 2 ≤ current.stock 1 .waste
instance (current : Current) : Decidable (Inputs current) :=
  decidable_of_iff (ResupplyLaw.Restorable (material current) ∧ current.stock 0 .feedstock = 1 ∧
    1 ≤ current.stock 0 .labor ∧ 0 ≤ current.stock 0 .energy ∧ 2 ≤ current.stock 1 .waste)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
      fun h => ⟨h.material,h.fuel,h.labor,h.energy,h.waste⟩⟩

theorem request_is_original_and_paid (current : Current) (inputs : Inputs current) : law.Valid current request :=
  FuelMandateLaw.original_valid_requests_still_execute true current request
    (RenewedQuorumMaterial.supply_phases current ⟨inputs.material,by rw [inputs.fuel],inputs.labor,inputs.energy⟩).1

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good - (if party = 0 ∧ good = .feedstock then 1 else 0) +
    (if party = 0 ∧ good = .energy then 2 else 0) + (if party = 0 ∧ good = .labor then 2 else 0)
  clock := current.clock+1
  round := current.round+1}

set_option linter.unusedSimpArgs false in
theorem actual_next (current : Current) (inputs : Inputs current) :
    law.next current word = successor current ∧ ∀ item ∈ law.rawItems current word, law.Valid item.before item.request := by
  have paid := request_is_original_and_paid current inputs
  constructor
  · simp only [word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos paid]
    apply RawCurrent.ext
    · funext party good
      fin_cases party <;> cases good <;> simp [successor,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,
        law,WorkerInputLaw.law,FuelMandateLaw.law,FuelMandateLaw.base,RenewedQuorumMaterial.base,
        request,RenewedQuorumMaterial.renew,Mandate.law,Repayment.Recovery.base,flowAt,locate,amount]
      ring
    all_goals rfl
  · intro item inside
    simp only [word,RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at inside
    cases inside
    exact paid

theorem original_production_generates_the_previously_assumed_worker_inputs
    (current : Current) (inputs : Inputs current) : WorkerInputLaw.Inputs (successor current) := by
  obtain ⟨possible,fuel,labor,energy,waste⟩ := inputs
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := possible
  constructor
  · constructor <;> simp_all [successor,material]
  · simp [successor];linarith
  · simp [successor];linarith
  · simpa [successor] using waste
  · simp [successor,fuel]
  · simp [successor,fuel]

theorem production_debits_real_inputs_and_does_not_mint_finance (current : Current) :
    flowAt (law.debit current request) 0 .feedstock = 1 ∧
      flowAt (law.debit current request) 0 .labor = 1 ∧
      flowAt (law.credit current request) 0 .energy = 2 ∧
      flowAt (law.credit current request) 0 .labor = 3 ∧
      (successor current).claims = current.claims ∧ (successor current).technology = current.technology := by
  simp [RawLaw.debit,RawLaw.credit,law,WorkerInputLaw.law,FuelMandateLaw.law,FuelMandateLaw.base,
    RenewedQuorumMaterial.base,Mandate.law,flowAt,locate,amount,successor]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionLaw

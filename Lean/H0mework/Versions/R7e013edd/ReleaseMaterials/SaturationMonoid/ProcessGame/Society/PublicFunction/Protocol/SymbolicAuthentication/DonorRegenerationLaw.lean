import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action material)
abbrev law := UpstreamProductionLaw.law
abbrev recycle := RecycledQuorumMaterial.recycle
abbrev word : List Action := WorkerInputLaw.word ++ [recycle]

structure Inputs (current : Current) : Prop where
  worker : WorkerInputLaw.Inputs current
  energy : current.stock 0 .energy = 1
  empty : current.stock 0 .feedstock = 0
  donorEmpty : current.stock 2 .feedstock = 0
  waste : 3 ≤ current.stock 1 .waste
instance (current : Current) : Decidable (Inputs current) :=
  decidable_of_iff (WorkerInputLaw.Inputs current ∧ current.stock 0 .energy = 1 ∧ current.stock 0 .feedstock = 0 ∧
      current.stock 2 .feedstock = 0 ∧ 3 ≤ current.stock 1 .waste)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,fun h => ⟨h.worker,h.energy,h.empty,h.donorEmpty,h.waste⟩⟩

abbrev beforeRecycle (current : Current) := law.paidStep (law.paidStep current WorkerInputLaw.energyLabor) WorkerInputLaw.waste

set_option linter.unusedSimpArgs false in
theorem actual_phases (current : Current) (inputs : Inputs current) :
    law.Valid current WorkerInputLaw.energyLabor ∧
      law.Valid (law.paidStep current WorkerInputLaw.energyLabor) WorkerInputLaw.waste ∧
      law.Valid (beforeRecycle current) recycle := by
  have phases := WorkerInputLaw.actual_phases current inputs.worker
  refine ⟨phases.1,phases.2,?_⟩
  apply (FuelMandateLaw.actual_phases (beforeRecycle current) ?_).1
  obtain ⟨possible,energy,labor,waste,fuel,deficit⟩ := inputs.worker
  have donor := inputs.donorEmpty
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := possible
  change current.technology.technology = true at willing
  constructor <;>
    simp [beforeRecycle,law,UpstreamProductionLaw.law,WorkerInputLaw.law,WorkerInputLaw.energyLabor,
      WorkerInputLaw.waste,RenewedQuorumMaterial.give,RecycledQuorumMaterial.waste,RawLaw.paidStep,
      RawLaw.debit,RawLaw.credit,Mandate.law,FuelMandateLaw.law,FuelMandateLaw.base,RenewedQuorumMaterial.base,
      Repayment.Recovery.base,material,flowAt,locate,amount,willing,donor] at *
  all_goals linarith

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good + (if party = 2 ∧ good = .feedstock then 1 else 0) -
    (if (party = 0 ∧ (good = .energy ∨ good = .labor)) ∨ (party = 1 ∧ good = .waste) then 1 else 0)
  clock := current.clock+1
  round := current.round+1}

set_option linter.unusedSimpArgs false in
theorem actual_next (current : Current) (inputs : Inputs current) :
    law.next current word = successor current ∧
      ∀ item ∈ law.rawItems current word, law.Valid item.before item.request := by
  obtain ⟨first,second,third⟩ := actual_phases current inputs
  constructor
  · simp only [word,WorkerInputLaw.word,List.cons_append,List.nil_append,
      RawLaw.next,RawLaw.execute,RawLaw.step,if_pos first,if_pos second,if_pos third]
    apply RawCurrent.ext
    · funext party good
      fin_cases party <;> cases good <;>
        simp [successor,beforeRecycle,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,UpstreamProductionLaw.law,
          WorkerInputLaw.law,WorkerInputLaw.energyLabor,WorkerInputLaw.waste,RenewedQuorumMaterial.give,
          RecycledQuorumMaterial.waste,recycle,RecycledQuorumMaterial.recycle,Mandate.law,
          FuelMandateLaw.law,FuelMandateLaw.base,RenewedQuorumMaterial.base,Repayment.Recovery.base,
          flowAt,locate,amount]
    all_goals rfl
  · intro item member
    simp only [RawLaw.rawItems,word,WorkerInputLaw.word,List.cons_append,List.nil_append,
      RawLaw.execute,RawLaw.step,if_pos first,if_pos second,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact first
    · exact second
    · exact third

theorem new_fuel_has_original_paid_inputs (current : Current) (inputs : Inputs current) :
    UpstreamFeedLaw.Resources (successor current) := by
  obtain ⟨worker,sourceEnergy,empty,donorEmpty,wasteReserve⟩ := inputs
  obtain ⟨possible,energy,labor,waste,fuel,deficit⟩ := worker
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := possible
  constructor
  · constructor <;> simp_all [successor,material]
    all_goals linarith
  · simp [successor,empty]
  · simp [successor,donorEmpty]
  · simp [successor];linarith
  · simp [successor];linarith
  · simp [successor];linarith

theorem new_fuel_leaves_the_worker_deficit_visible (current : Current)
    (inputs : Inputs current) (needed : WorkerInputSource.Needed current) :
    WorkerInputSource.Needed (successor current) ∧ ¬ WorkerInputLaw.Inputs (successor current) ∧
      ¬ UpstreamProductionLaw.Inputs (successor current) := by
  refine ⟨by simpa [successor,WorkerInputSource.Needed] using needed,?_,?_⟩
  · intro ready
    have enough := ready.energy
    simp [successor,inputs.energy] at enough
    linarith
  · intro ready
    have fuel := ready.fuel
    simp [successor,inputs.empty] at fuel
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationLaw

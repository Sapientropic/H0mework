import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMandateLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action)

-- This is an explicit source law, not a permission retroactively installed on an old Bound.
def base (released : Bool) : RawLaw Party Good Port Bool Unit := {RenewedQuorumMaterial.base with
  policy := .opaque fun current request =>
    RenewedQuorumMaterial.base.operationAllowed current request ||
      (released && decide (request.signer = 2) && current.technology && match request.operation with
        | .transfer sender recipient goods => decide (sender = 2 ∧ recipient = 0 ∧ goods = [(.feedstock,1)])
        | _ => false) }
abbrev law (released : Bool) := Mandate.law (base released) Repayment.Recovery.scope
abbrev recycle : Action := RecycledQuorumMaterial.recycle
def give : Action := ⟨2,[],.reserve 2,[],.transfer 2 0 [(.feedstock,1)]⟩
def word : List Action := [recycle,give]

structure Inputs (current : Current) : Prop where
  waste : 1 ≤ current.stock 2 .waste
  energy : 1 ≤ current.stock 2 .energy
  labor : 1 ≤ current.stock 2 .labor
  feed : 0 ≤ current.stock 2 .feedstock
  willing : current.technology.technology = true

instance (current : Current) : Decidable (Inputs current) :=
  decidable_of_iff (1 ≤ current.stock 2 .waste ∧ 1 ≤ current.stock 2 .energy ∧
    1 ≤ current.stock 2 .labor ∧ 0 ≤ current.stock 2 .feedstock ∧ current.technology.technology = true)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
      fun h => ⟨h.waste,h.energy,h.labor,h.feed,h.willing⟩⟩

theorem original_valid_requests_still_execute (released : Bool) (current : Current) (request : Action)
    (valid : RenewedQuorumMaterial.law.Valid current request) : (law released).Valid current request := by
  obtain ⟨⟨signer,policy⟩,ports,claims,debit,credit,stock⟩ := valid
  refine ⟨⟨signer,?_⟩,ports,claims,debit,credit,stock⟩
  cases operation : request.operation with
  | revise actor target => simpa only [law,Mandate.law,RawLaw.operationAllowed,RawPolicy.eval,operation] using policy
  | _ =>
    simp only [RenewedQuorumMaterial.law,Mandate.law,RawLaw.operationAllowed,RawPolicy.eval,operation,
      Bool.and_eq_true] at policy
    simp only [law,Mandate.law,RawLaw.operationAllowed,RawPolicy.eval,operation,base,Bool.and_eq_true]
    exact ⟨Bool.or_eq_true_iff.mpr (Or.inl policy.1),policy.2⟩

theorem original_paid_execution_is_preserved (released : Bool) (current : Current)
    (index : Nat) (requests : List Action)
    (valid : ∀ item ∈ (RenewedQuorumMaterial.law.execute current index requests).items,
      RenewedQuorumMaterial.law.Valid item.before item.request) :
    (law released).execute current index requests = RenewedQuorumMaterial.law.execute current index requests := by
  induction requests generalizing current index with
  | nil => rfl
  | cons request tail ih =>
    have first := valid ⟨index,current,request⟩ (by simp [RawLaw.execute])
    have same : (law released).step current request = RenewedQuorumMaterial.law.step current request := by
      rw [RawLaw.step,if_pos (original_valid_requests_still_execute released current request first),RawLaw.step,if_pos first]
      rfl
    have rest := ih (RenewedQuorumMaterial.law.step current request) (index+1) (by
      intro item member
      exact valid item (by simp only [RawLaw.execute,List.mem_cons];exact Or.inr member))
    simp only [RawLaw.execute,same,rest]

theorem original_material_recovery_is_preserved (released : Bool) (current : Current)
    (inputs : RenewedQuorumMaterial.Inputs current) :
    (law released).next current RenewedQuorumMaterial.word = RenewedQuorumMaterial.successor current ∧
      ∀ item ∈ (law released).rawItems current RenewedQuorumMaterial.word,
        (law released).Valid item.before item.request := by
  have same := original_paid_execution_is_preserved released current 0 RenewedQuorumMaterial.word
    (RenewedQuorumMaterial.actual_items current inputs)
  constructor
  · change { ((law released).execute current 0 RenewedQuorumMaterial.word).final with
      clock := current.clock + 1,round := current.round + 1} = _
    rw [same]
    exact RenewedQuorumMaterial.actual_next current inputs
  · intro item member
    change item ∈ ((law released).execute current 0 RenewedQuorumMaterial.word).items at member
    rw [same] at member
    exact original_valid_requests_still_execute released item.before item.request
      (RenewedQuorumMaterial.actual_items current inputs item member)

set_option linter.unusedSimpArgs false in
theorem actual_phases (current : Current) (inputs : Inputs current) :
    (law true).Valid current recycle ∧ (law true).Valid ((law true).paidStep current recycle) give := by
  obtain ⟨waste,energy,labor,feed,willing⟩ := inputs
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    law,base,recycle,give,RecycledQuorumMaterial.recycle,RawLaw.paidStep,Mandate.law,
    Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    RenewedQuorumMaterial.base,Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
    flowAt,locate,amount,willing]
  all_goals repeat' constructor
  all_goals linarith

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good + (if party = 0 ∧ good = .feedstock then 1 else 0) -
    (if party = 2 ∧ (good = .waste ∨ good = .energy ∨ good = .labor) then 1 else 0)
  clock := current.clock + 1
  round := current.round + 1}

set_option linter.unusedSimpArgs false in
theorem actual_recovery (current : Current) (inputs : Inputs current) :
    (law true).next current word = successor current ∧
      ∀ item ∈ (law true).rawItems current word, (law true).Valid item.before item.request := by
  obtain ⟨first,second⟩ := actual_phases current inputs
  constructor
  · simp only [word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos first,if_pos second]
    apply RawCurrent.ext
    · funext party good
      fin_cases party <;> cases good <;>
        simp [successor,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,base,recycle,give,
          RecycledQuorumMaterial.recycle,Mandate.law,RenewedQuorumMaterial.base,Repayment.Recovery.base,
          flowAt,locate,amount]
    all_goals rfl
  · intro item member
    simp only [RawLaw.rawItems,word,RawLaw.execute,RawLaw.step,if_pos first,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelMandateLaw

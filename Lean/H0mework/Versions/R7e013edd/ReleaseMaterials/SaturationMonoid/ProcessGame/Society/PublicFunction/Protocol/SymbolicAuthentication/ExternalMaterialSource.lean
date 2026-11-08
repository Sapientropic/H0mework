import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialSource
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party)
open Repayment.Recovery (Good)
abbrev Community := RecycledQuorumMaterial.Current
abbrev Actor := Sum Party Unit
abbrev Technology := Mandate.State Party Bool
abbrev Current := RawCurrent Actor Good Technology Unit
abbrev Action := Request Actor Good Actor Technology Unit
abbrev supplier : Actor := .inr ()
abbrev recipient : Actor := .inl 0

-- The upstream account is a different actor in one stock carrier. It is not
-- a replacement initial state for an already running communication cursor.
def load (community : Community) (outside : Good → ℚ) : Current where
  stock := fun actor good => match actor with | .inl party => community.stock party good | .inr _ => outside good
  claims := fun instrument debtor creditor => match debtor,creditor with
    | .inl debtor,.inl creditor => community.claims instrument debtor creditor
    | _,_ => 0
  technology := community.technology
  clock := community.clock
  round := community.round

def community (current : Current) : Community where
  stock := fun party good => current.stock (.inl party) good
  claims := fun instrument debtor creditor => current.claims instrument (.inl debtor) (.inl creditor)
  technology := current.technology
  clock := current.clock
  round := current.round

-- The local interpreter writes back only its own restriction of this carrier.
def install (whole : Current) (part : Community) : Current where
  stock := fun actor good => match actor with | .inl party => part.stock party good | .inr _ => whole.stock actor good
  claims := fun instrument debtor creditor => match debtor,creditor with
    | .inl debtor,.inl creditor => part.claims instrument debtor creditor
    | _,_ => whole.claims instrument debtor creditor
  technology := part.technology
  clock := part.clock
  round := part.round

@[simp] theorem project_load (part : Community) (outside : Good → ℚ) : community (load part outside) = part := rfl
@[simp] theorem project_install (whole : Current) (part : Community) : community (install whole part) = part := rfl
@[simp] theorem install_preserves_external_stock (whole : Current) (part : Community) (good : Good) :
    (install whole part).stock supplier good = whole.stock supplier good := rfl

def law : RawLaw Actor Good Actor Technology Unit where
  technique := fun _ _ => ⟨[(.waste,1),(.energy,1)],[(.feedstock,1)],[(.labor,1)],[supplier]⟩
  controller := fun _ port => port
  allowed := fun _ port signer => decide (port = signer)
  stockPort := fun _ actor _ => actor
  revisionPort := fun _ => supplier
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => .service
  settlementRate := fun _ => 1
  issuerPort := fun _ => supplier
  necessities := fun _ _ => []
  mandatoryMaintenance := fun _ _ => []
  policy := .opaque fun current request => decide (request.signer = supplier) && current.technology.technology &&
    match request.operation with
    | .produce actor => decide (actor = supplier)
    | .transfer sender receiver goods => decide (sender = supplier ∧ receiver = recipient ∧ goods = [(.feedstock,1)])
    | _ => false
  duration := fun _ => 1

def production : Action := ⟨supplier,[],supplier,[],.produce supplier⟩
def delivery : Action := ⟨supplier,[],supplier,[],.transfer supplier recipient [(.feedstock,1)]⟩
def word : List Action := [production,delivery]
def batch (enabled : Bool) : List Action := if enabled then word else []
abbrev next (current : Current) (enabled : Bool) := law.next current (batch enabled)

structure Inputs (current : Current) : Prop where
  waste : 1 ≤ current.stock supplier .waste
  energy : 1 ≤ current.stock supplier .energy
  labor : 1 ≤ current.stock supplier .labor
  feed : 0 ≤ current.stock supplier .feedstock
  willing : current.technology.technology = true

def expected (current : Current) : Current := {current with
  stock := fun actor good => current.stock actor good + (if actor = recipient ∧ good = .feedstock then 1 else 0) -
    (if actor = supplier ∧ (good = .waste ∨ good = .energy ∨ good = .labor) then 1 else 0)
  clock := current.clock + 1
  round := current.round + 1}

set_option linter.unusedSimpArgs false in
theorem actual_phases (current : Current) (inputs : Inputs current) :
    law.Valid current production ∧ law.Valid (law.paidStep current production) delivery := by
  obtain ⟨waste,energy,labor,feed,willing⟩ := inputs
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    law,production,delivery,RawLaw.paidStep,flowAt,locate,amount,supplier,recipient,willing]
  all_goals repeat' constructor
  all_goals linarith

set_option linter.unusedSimpArgs false in
theorem actual_next (current : Current) (inputs : Inputs current) : next current true = expected current := by
  obtain ⟨first,second⟩ := actual_phases current inputs
  simp only [next,batch,Bool.true_eq,ite_true,word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos first,if_pos second]
  apply RawCurrent.ext
  · funext actor good
    cases actor with
    | inl party => fin_cases party <;> cases good <;>
        simp [expected,law,production,delivery,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flowAt,locate,amount,supplier,recipient]
    | inr external => cases external;cases good <;>
        simp [expected,law,production,delivery,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,flowAt,locate,amount,supplier,recipient]
  all_goals rfl

theorem actual_items (current : Current) (inputs : Inputs current) :
    ∀ item ∈ law.rawItems current word,law.Valid item.before item.request := by
  obtain ⟨first,second⟩ := actual_phases current inputs
  intro item member
  simp only [RawLaw.rawItems,word,RawLaw.execute,RawLaw.step,if_pos first,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact first
  · exact second

theorem withholding_preserves_every_stock (current : Current) (actor : Actor) (good : Good) :
    (next current false).stock actor good = current.stock actor good := rfl

set_option linter.unusedSimpArgs false in
theorem every_attempt_preserves_the_whole_claim_matrix (current : Current) (enabled : Bool) :
    (next current enabled).claims = current.claims := by
  cases enabled with
  | false => rfl
  | true =>
    simp only [next,batch,Bool.true_eq,ite_true,word,RawLaw.next,RawLaw.execute,RawLaw.step]
    split_ifs <;> rfl

theorem a_different_signer_cannot_submit_the_upstream_production (current : Current) (actor : Actor)
    (different : actor ≠ supplier) : ¬ law.Valid current {production with signer := actor} := by
  intro valid
  have allowed := valid.1.2
  simp [law,RawLaw.operationAllowed,RawPolicy.eval,production,different] at allowed
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialSource

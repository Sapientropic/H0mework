import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialRepayment

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorLaw
open Institutions.Capitalism.Universal.Source.Program
open Repayment.Recovery (Good)
abbrev Party := Sum Delegation.Funded.Party Unit
abbrev Port := Sum Delegation.Funded.Port Bool
abbrev Current := RawCurrent Party Good (Mandate.State Party Bool) Unit
abbrev Action := Request Party Good Port (Mandate.State Party Bool) Unit
abbrev producer : Party := .inl 1
abbrev creditor : Party := .inl 2
abbrev supplier : Party := .inr ()
abbrev reserve (party : Delegation.Funded.Party) : Port := .inl (.reserve party)
abbrev outside : Port := .inr false
abbrev ballotPort : Port := .inr true

def party? : Party → Option Delegation.Funded.Party | .inl party => some party | .inr _ => none
def port? : Port → Option Delegation.Funded.Port | .inl port => some port | .inr _ => none
def operation? : Operation Party Good Bool Unit → Option (Operation Delegation.Funded.Party Good Bool Unit)
  | .produce actor => return .produce (← party? actor)
  | .transfer sender recipient goods => return .transfer (← party? sender) (← party? recipient) goods
  | .use bearer goods purpose => return .use (← party? bearer) goods purpose
  | .issue instrument issuer beneficiary quantity => return .issue instrument (← party? issuer) (← party? beneficiary) quantity
  | .assign instrument issuer sender recipient quantity => return .assign instrument (← party? issuer) (← party? sender) (← party? recipient) quantity
  | .settle instrument debtor creditor quantity => return .settle instrument (← party? debtor) (← party? creditor) quantity
  | .revise actor target => return .revise (← party? actor) target
  | .present => some .present

def request? (request : Request Party Good Port Bool Unit) : Option (Request Delegation.Funded.Party Good Delegation.Funded.Port Bool Unit) := do
  return ⟨← party? request.signer,← request.consents.mapM party?,← port? request.purpose,
    ← request.gates.mapM port?,← operation? request.operation⟩

def restrict (current : RawCurrent Party Good Bool Unit) : RawCurrent Delegation.Funded.Party Good Bool Unit :=
  ⟨fun party good => current.stock (.inl party) good,
    fun instrument debtor creditor => current.claims instrument (.inl debtor) (.inl creditor),
    current.technology,current.clock,current.round⟩

def base : RawLaw Party Good Port Bool Unit where
  technique := fun technology actor => match actor with
    | .inl party => let recipe := (FuelMandateLaw.base true).technique technology party
                   ⟨recipe.inputs,recipe.outputs,recipe.maintenance,recipe.requiredPorts.map Sum.inl⟩
    | .inr _ => ⟨[(.waste,1),(.energy,1)],[(.feedstock,1)],[(.labor,1)],[outside]⟩
  controller := fun technology port => match port with
    | .inl port => .inl ((FuelMandateLaw.base true).controller technology port)
    | .inr flag => if flag then producer else supplier
  allowed := fun technology port actor => match port,actor with
    | .inl port,.inl actor => (FuelMandateLaw.base true).allowed technology port actor
    | .inr flag,actor => decide (actor = if flag then producer else supplier)
    | _,_ => false
  stockPort := fun technology actor good => match actor with
    | .inl actor => .inl ((FuelMandateLaw.base true).stockPort technology actor good)
    | .inr _ => outside
  revisionPort := fun technology => .inl ((FuelMandateLaw.base true).revisionPort technology)
  revisionCost := (FuelMandateLaw.base true).revisionCost
  settlementUnit := (FuelMandateLaw.base true).settlementUnit
  settlementRate := (FuelMandateLaw.base true).settlementRate
  issuerPort := fun instrument => .inl ((FuelMandateLaw.base true).issuerPort instrument)
  necessities := fun current actor => match actor with
    | .inl actor => (FuelMandateLaw.base true).necessities (restrict current) actor
    | .inr _ => []
  mandatoryMaintenance := fun current actor => match actor with
    | .inl actor => (FuelMandateLaw.base true).mandatoryMaintenance (restrict current) actor
    | .inr _ => []
  duration := fun current => (FuelMandateLaw.base true).duration (restrict current)
  policy := .opaque fun current request => match request? request with
    | some original => (FuelMandateLaw.base true).operationAllowed (restrict current) original
    | none => match request.purpose with
      | .inr true => decide (request.signer = producer ∧ request.consents = [] ∧ request.gates = []) && match request.operation with
        | .use bearer goods purpose => decide (bearer = producer ∧ goods = [(.service,1)] ∧ purpose = .external)
        | _ => false
      | .inr false => decide (request.signer = supplier) && current.technology && match request.operation with
        | .produce actor => decide (actor = supplier)
        | .transfer sender recipient goods => decide (sender = supplier ∧ recipient = producer ∧ goods = [(.feedstock,1)])
        | _ => false
      | .inl _ => false

def task : PublicTaskSpec Party Good :=
  ⟨[⟨producer,[(.service,1)],.necessity⟩,⟨producer,[(.service,1)],.maintenance⟩],1,3,by decide +kernel⟩
def scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port) :=
  ⟨task,.inl .service,.inl .challenge,by decide,[(.service,1)]⟩
abbrev law := Mandate.law base scope

def issue : Action := ⟨producer,[],reserve 1,[],.issue () producer creditor 7⟩
def charge : Action := ⟨producer,[],reserve 1,[],.use producer [(.service,1)] .external⟩
def ballot : Action := {charge with purpose := ballotPort}
def production : Action := ⟨supplier,[],outside,[],.produce supplier⟩
def transfer : Action := ⟨supplier,[],outside,[],.transfer supplier producer [(.feedstock,1)]⟩
def useFeed : Action := ⟨producer,[],reserve 1,[],.produce producer⟩
def cycle : List Action := [production,transfer,useFeed]

def initial : Current where
  stock := fun party good => if party = producer ∧ good = .service then 2
    else if (party = supplier ∧ (good = .waste ∨ good = .energy ∨ good = .labor)) ∨
      (party = producer ∧ (good = .energy ∨ good = .labor)) then 3 else 0
  claims := fun _ _ _ => 0
  technology := ⟨true,0,none,none,none⟩
  clock := 0
  round := 0

-- A second issue is a real policy refusal, not a new interpretation of the old debt.
theorem the_source_really_issues_and_rejects_duplicate_financing :
    law.Valid initial issue ∧ ¬ law.Valid (law.step initial issue) issue := by
  constructor <;> decide +kernel
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorLaw

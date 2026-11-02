import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Consumers.Example
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Payment
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

abbrev Party := Trials.Example.Party
abbrev Good := Trials.Example.Good
abbrev RequestAt := Request Party Good Bool Nat Unit
abbrev Current := RawCurrent Party Good Nat Unit

def law : RawLaw Party Good Bool Nat Unit := { Trials.Example.law with
  technique := fun version _ =>
    ⟨[(.message,1)], [(.material, if version = 0 then 1 else (version : ℚ) + 4),
      (.life,1), (.maintenance,1)] ++ (if version = 0 then [] else [(.result,1)]), [], [true]⟩
  revisionCost := fun _ version => if version = 0 then [] else [(.material,1)] }

def openLaw := PublicFunction.physicalLaw law

def request (actor : Party) (operation : Operation Party Good Nat Unit) : RequestAt :=
  ⟨actor, [], false, [], operation⟩

def production (actor : Party) : RequestAt :=
  ⟨actor, [2], false, [], .produce actor⟩

def life (actor : Party) := request actor (.use actor [(.life,1)] .necessity)
def maintain (actor : Party) := request actor (.use actor [(.maintenance,1)] .maintenance)
def closing := ([0,1,2] : List Party).flatMap fun actor => [life actor,maintain actor]
def commonWork := ([0,1,2] : List Party).flatMap fun actor => [production actor,life actor,maintain actor]

def ownerClaim := request 0 (.issue () 0 2 1)
def controlledNeed : RequestAt := ⟨0,[2],false,[true],.use 0 [(.life,1)] .necessity⟩
def rent := request 0 (.transfer 0 2 [(.material,1)])
def ownerPresent := request 2 .present
def ownerConsume := request 2 (.use 2 [(.material,1)] .external)
def capitalWord := [ownerClaim,production 0,controlledNeed,rent,ownerPresent] ++ closing

def genesis : Current where
  stock := fun actor good => match good with
    | .material => if actor = 1 then 12 else 2
    | .message => 100
    | .life | .maintenance => 3
    | .result => 0
  claims := fun _ _ _ => 0
  technology := 0
  clock := 0
  round := 0

def start := law.next genesis []
def seed := law.next start capitalWord

def issue := request 0 (.issue () 0 1 3)
def payout := request 1 (.transfer 1 0 [(.material,6)])
def repay := request 0 (.settle () 0 1 3)
def observationFee := request 0 (.use 0 [(.message,1)] .contribution)
def migrationFee := request 0 (.use 0 [(.material,1)] .investment)

/-- The original holder's finite source rule exchanges consent for rent.
Its input is the submitted offer, not the future technical result. -/
def offeredRent (version : Nat) : ℚ := if version = 1 then 1 else 0
def controlRent : ℚ := flowAt (law.actualCredit
  ((law.execute start 0 [ownerClaim,production 0,controlledNeed]).final) rent) 2 .material
def ownerConsents (offer : ℚ) : List Party := if controlRent ≤ offer then [2] else []
def discovery (version : Nat) : RequestAt :=
  ⟨0,ownerConsents (offeredRent version),false,[],.revise 0 version⟩

def lawAt (opened : Bool) := if opened then openLaw else law

def trialInvestment : Bundle Good := [(.material,3)]
def exposure : ℚ := amount Good trialInvestment .material -
  amount Good (law.technique 0 0).outputs .material
def riskReward : ℚ := ((1 / 2 : ℚ) * exposure + 1 / 2) / (1 - 1 / 2)
def premiumUnits : ℚ := riskReward / law.settlementRate ()
def coverageUnits : ℚ := exposure / law.settlementRate ()
def successLiability := request 0 (.issue () 0 1 premiumUnits)
def failureLiability := request 1 (.issue () 1 0 coverageUnits)
def successPayment := request 0 (.settle () 0 1 premiumUnits)
def failureCoverage := request 1 (.settle () 1 0 coverageUnits)

/-- Install this signed liability before attempting its material performance.
A refused later settlement therefore retains the original claim. -/
def contributionLiabilityWord (signal : Nat) : RawEvent Party Good Bool Nat Unit :=
  if signal = 1 then [successLiability] else if signal = 0 then [failureLiability] else []

def contributionSettlementWord (signal : Nat) : RawEvent Party Good Bool Nat Unit :=
  if signal = 1 then [repay,successPayment]
  else if signal = 0 then [failureCoverage,repay] else []

def contributionPerformanceWord (signal : Nat) := commonWork ++ contributionSettlementWord signal
def policyAction (signal : Nat) := contributionLiabilityWord signal ++ contributionPerformanceWord signal

abbrev code (opened : Bool) : Distributed.Code Party Good Bool Nat Unit :=
  { Trials.Example.code 12 100 with
    law := lawAt opened
    initial := seed
    actions := commonWork ++ [repay,successLiability,failureLiability,successPayment,failureCoverage]
    actionLimit := 12
    signals := 3
    initialSignal := 0
    memoryReady := fun _ => true
    readLocal := fun _ current => if 0 < current.stock .result then 1 else 0
    afterSend := fun _ _ previous _ => previous
    afterDelivery := fun _ _ _ signal => signal
    afterAction := fun _ _ _ => 2
    sendCost := fun _ _ => [observationFee]
    eventAlphabet := [.adversary (discovery 0),.adversary (discovery 1),.send 0 0,.deliver 0,.activate 0] }

abbrev skeleton (opened : Bool) : Trials.Mechanism Party Good Bool Nat Unit where
  code := code opened
  policy := fun _ _ => []
  terms := ⟨0,1,(),3⟩
  funding := [issue,payout]
  investment := trialInvestment
  investmentPort := false
  probe := [production 0]
  observer := 0
  closing := []

abbrev mechanism (opened : Bool) : Trials.Mechanism Party Good Bool Nat Unit :=
  { skeleton opened with
    policy := fun key _ => policyAction key.2.val
    closing := closing ++ if opened then [migrationFee] else [rent] }

/-- The common opponent receives the closed original history, the current
material prefix and its actual state. It may submit any finite raw response. -/
abbrev Response := List (RawEvent Party Good Bool Nat Unit) →
  RawEvent Party Good Bool Nat Unit → Current → RawEvent Party Good Bool Nat Unit

def retaliation : Response := fun _ _ actual =>
  if 0 < actual.stock 2 .result then [request 2 (.use 2 [(.result,1)] .external)]
  else [ownerPresent]

def word (opened : Bool) (nature : RequestAt) (opponent : Response) : RawEvent Party Good Bool Nat Unit :=
  (mechanism opened).word nature ++
    opponent [[],capitalWord] ((mechanism opened).word nature) ((mechanism opened).after nature)

def execution (opened : Bool) (nature : RequestAt) (opponent : Response) :=
  (lawAt opened).execute seed 0 (word opened nature opponent)

def after (opened : Bool) (nature : RequestAt) (opponent : Response) :=
  (execution opened nature opponent).final

theorem preparation_is_fixed_before_every_actual_discovery :
    (mechanism false).funding = (mechanism true).funding ∧
      (mechanism false).investmentRequest = (mechanism true).investmentRequest ∧
      (mechanism false).code.initial = (mechanism true).code.initial := ⟨rfl,rfl,rfl⟩

theorem the_same_local_policy_is_fixed_before_the_unknown_event :
    HEq (mechanism false).policy (mechanism true).policy := HEq.rfl

theorem the_public_interpreter_is_the_original_physical_restriction :
    lawAt true = PublicFunction.physicalLaw (lawAt false) := rfl

theorem every_response_is_charged_in_its_actual_original_inventory
    (opened : Bool) (nature : RequestAt) (opponent : Response) :
    (execution opened nature opponent).items.map ExecutionItem.request = word opened nature opponent :=
  (lawAt opened).inventory_requests_exact seed 0 _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario

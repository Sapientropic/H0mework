import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Decision
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Example

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

abbrev Party := Fin 3
inductive Good where
  | material | message | life | maintenance | result
  deriving DecidableEq, Repr
abbrev RequestAt := Request Party Good Bool Nat Unit

def law : RawLaw Party Good Bool Nat Unit where
  technique := fun technology _ => ⟨[], if technology = 0 then [] else
    [(.life, 1), (.maintenance, 1), (.result, 1), (.material, technology + 3)], [], []⟩
  controller := fun _ _ => 2
  allowed := fun _ port actor => if port then decide (actor = 2) else true
  stockPort := fun _ _ _ => false
  revisionPort := fun _ => true
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => .material
  settlementRate := fun _ => 2
  issuerPort := fun _ => false
  necessities := fun _ _ => [(.life, 1)]
  mandatoryMaintenance := fun _ _ => [(.maintenance, 1)]
  duration := fun _ => 1

def request (actor : Party) (operation : Operation Party Good Nat Unit) : RequestAt :=
  ⟨actor, [], false, [], operation⟩
def issue := request 0 (.issue () 0 1 3)
def payout := request 1 (.transfer 1 0 [(.material, 6)])
def production (actor : Party) := request actor (.produce actor)
def produce := production 0
def life (actor : Party) := request actor (.use actor [(.life, 1)] .necessity)
def maintain (actor : Party) := request actor (.use actor [(.maintenance, 1)] .maintenance)
def observationFee := request 0 (.use 0 [(.message, 1)] .contribution)
def shock (technology : Nat) := request 2 (.revise 2 technology)
def work := ([0,1,2] : List Party).flatMap fun actor => [production actor, life actor, maintain actor]
def closing := ([0,1,2] : List Party).flatMap fun actor => [life actor, maintain actor]

def initial (funds communication : ℚ) : RawCurrent Party Good Nat Unit where
  stock := fun actor good => match good with
    | .life | .maintenance => 2
    | .material => if actor = 1 then funds else 0
    | .message => if actor = 0 then communication else 0
    | .result => 0
  claims := fun _ debtor creditor => if debtor = 0 ∧ creditor = 1 then 2 else 0
  technology := 0
  clock := 0
  round := 0

abbrev code (funds communication : ℚ) : Distributed.Code Party Good Bool Nat Unit where
  law := law
  initial := initial funds communication
  task := ⟨[⟨0, [(.life, 1)], .necessity⟩, ⟨0, [(.maintenance, 1)], .maintenance⟩], 0, 10, by decide +kernel⟩
  actions := work
  actionLimit := 9
  sites := 1
  signals := 2
  initialSignal := 0
  siteParty := fun _ => 0
  readLocal := fun _ current => if 0 < current.stock .result then 1 else 0
  sendCost := fun _ _ => [observationFee]
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.adversary (shock 0), .adversary (shock 1), .send 0 0, .deliver 0, .activate 0]
  eventLimit := 5
  eligible := fun _ => true
  parties := [0,1,2]
  goods := [.material,.message,.life,.maintenance,.result]
  instruments := [()]
  parties_cover := by
    intro actor
    have bound : actor.val < 3 := actor.isLt
    have values : actor.val = 0 ∨ actor.val = 1 ∨ actor.val = 2 := by omega
    have cases : actor = 0 ∨ actor = 1 ∨ actor = 2 := by
      rcases values with equal | equal | equal
      · exact Or.inl (Fin.ext equal)
      · exact Or.inr (Or.inl (Fin.ext equal))
      · exact Or.inr (Or.inr (Fin.ext equal))
    rcases cases with same | same | same <;> simp [same]
  goods_cover := by intro good; cases good <;> simp
  instruments_cover := by intro instrument; cases instrument; simp

abbrev mechanism (funds communication : ℚ) : Mechanism Party Good Bool Nat Unit where
  code := code funds communication
  policy := fun key _ => if key.2 = 1 then work else []
  terms := ⟨0, 1, (), 3⟩
  funding := [issue, payout]
  investment := [(.material, 3)]
  investmentPort := false
  probe := [produce]
  observer := 0
  closing := closing

def nature (funds communication : ℚ) (productive : Bool) : (mechanism funds communication).Nature :=
  shock (if productive then 1 else 0)

def quotedNature (funds communication : ℚ) (productive : Bool) : (mechanism funds communication).QuotedNature :=
  ⟨shock (if productive then 1 else 0), by
    cases productive
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self⟩

abbrev success := nature 12 1 true
abbrev failure := nature 12 1 false
abbrev noFunds := nature 0 1 true
abbrev noCommunication := nature 12 0 true

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Example

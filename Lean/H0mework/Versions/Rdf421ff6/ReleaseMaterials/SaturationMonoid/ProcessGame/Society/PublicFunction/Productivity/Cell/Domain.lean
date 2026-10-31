import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Incoming
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.NativeServiceRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Family
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program

abbrev Party := Nat

inductive Good where
  | seed | feed | life | spare | waste | energy | labor
  deriving DecidableEq

instance : Fintype Good where
  elems := {.seed, .feed, .life, .spare, .waste, .energy, .labor}
  complete := by intro good; cases good <;> simp

inductive Port where
  | common | machine | revision
  deriving DecidableEq

abbrev Technology := Bool × Bool
abbrev Current := RawCurrent Party Good Technology Unit
abbrev RequestAt := Request Party Good Port Technology Unit

def law : RawLaw Party Good Port Technology Unit where
  technique := fun technology operator =>
    if operator = 3 then
      ⟨[(.waste, 1), (.energy, 1)], [(.spare, 1)], [(.labor, 1)], [.machine]⟩
    else ⟨[(.seed, 1), (.feed, 8), (.energy, 1)],
      [(.seed, 3), (.life, if technology.2 then 5 else 4), (.spare, 1),
        (.waste, if technology.2 then 0 else 1)], [(.labor, 1)], [.machine]⟩
  controller := fun _ _ => 3
  allowed := fun technology port actor =>
    if port = .machine then technology.1 || decide (actor = 3) else true
  stockPort := fun _ _ _ => .common
  revisionPort := fun _ => .revision
  revisionCost := fun before after =>
    if before.1 ≠ after.1 then [(.energy, 1), (.labor, 1)]
    else if before.2 ≠ after.2 then [(.feed, 1), (.energy, 1), (.labor, 1)] else []
  settlementUnit := fun _ => .life
  settlementRate := fun _ => 1
  issuerPort := fun _ => .common
  necessities := fun _ party => if party = 3 then [] else [(.life, 1)]
  mandatoryMaintenance := fun _ party => if party = 3 then [] else [(.spare, 1)]
  duration := fun _ => 1
  policy := .opaque (fun current request => match request.operation with
    | .revise operator target => decide
        (operator = request.signer ∧ request.consents = [] ∧ target.1 = true ∧
          (current.technology.2 = true → target.2 = true))
    | .produce operator | .transfer operator _ _ | .use operator _ _ |
        .settle _ operator _ _ | .issue _ operator _ _ | .assign _ _ operator _ _ =>
        decide (operator = request.signer ∧ request.consents = [])
    | .present => true)

def production (cell : Party) : RequestAt := ⟨cell, [], .common, [], .produce cell⟩
def necessity (cell : Party) : RequestAt := ⟨cell, [], .common, [], .use cell [(.life, 1)] .necessity⟩
def maintenance (cell : Party) : RequestAt := ⟨cell, [], .common, [], .use cell [(.spare, 1)] .maintenance⟩
def transfer (signer sender recipient : Party) (goods : Bundle Good) : RequestAt :=
  ⟨signer, [], .common, [], .transfer sender recipient goods⟩
def audit (cell : Party) : RequestAt := ⟨cell, [], .common, [], .use cell [(.labor, 1)] .contribution⟩
def revise (cell : Party) (improved : Bool) : RequestAt :=
  ⟨cell, [], .common, [], .revise cell (true, improved)⟩
def issue : RequestAt := ⟨0, [], .common, [], .issue () 0 2 1⟩
def payout : RequestAt := transfer 2 2 0 [(.life, 1)]
def repayment : RequestAt := ⟨0, [], .common, [], .settle () 0 2 1⟩

def original : RawEvent Party Good Port Technology Unit :=
  [issue, payout, necessity 0, maintenance 0, necessity 1, maintenance 1,
    necessity 2, maintenance 2, production 0]

def firstCycle (cell : Party) : RawEvent Party Good Port Technology Unit :=
  [production cell, necessity cell, maintenance cell]

def seedChild (child : Party) : RawEvent Party Good Port Technology Unit :=
  [audit 0, transfer 0 0 child [(.seed, 1)],
    transfer 3 3 child [(.feed, if child = 1 then 17 else 16), (.energy, 4), (.labor, 4)]]

def copy (parent child : Party) : RawEvent Party Good Port Technology Unit :=
  [audit parent, transfer parent parent child
    [(.seed, 1), (.feed, 8), (.energy, 1), (.labor, 1), (.life, 1), (.spare, 1)]] ++ firstCycle child

def candidate (current : Current) : RawEvent Party Good Port Technology Unit :=
  match current.round with
  | 2 => [revise 0 false]
  | 3 => [production 0, repayment, necessity 0, maintenance 0]
  | 4 => seedChild 1
  | 5 => [revise 1 true]
  | 6 => firstCycle 1
  | 7 => seedChild 2
  | 8 => firstCycle 2
  | 9 => copy 1 4
  | 10 => copy 2 5
  | _ => []

def Ready (current : Current) : Prop :=
  ∀ item ∈ law.rawItems current (candidate current), law.Valid item.before item.request

instance (current : Current) : Decidable (Ready current) := by unfold Ready; infer_instance

inductive Response (current : Current)
  | ready (accepted : Ready current)
  | blocked (rejected : ¬ Ready current)

def respond (current : Current) : Response current :=
  if accepted : Ready current then .ready accepted else .blocked accepted

def Response.word {current : Current} : Response current → RawEvent Party Good Port Technology Unit
  | .ready _ => candidate current
  | .blocked _ => []

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

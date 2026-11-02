import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Carrier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

structure RouteLeg where
  item : Entry input endpoint
  destination : Party × Good

def Follows (origin : Party × Good) (lower : Nat) :
    List (RouteLeg input endpoint) → Party × Good → Nat → Prop
  | [], destination, upper => origin = destination ∧ lower ≤ upper
  | leg :: rest, destination, upper =>
      lower ≤ leg.item.position input ∧ leg.item.position input < upper ∧
      input.law.Valid (leg.item.raw input).before (leg.item.raw input).request ∧
      0 < flowAt (input.law.actualDebit (leg.item.raw input).before (leg.item.raw input).request)
        origin.1 origin.2 ∧
      0 < flowAt (input.law.actualCredit (leg.item.raw input).before (leg.item.raw input).request)
        leg.destination.1 leg.destination.2 ∧
      Follows leg.destination (leg.item.position input + 1) rest destination upper

instance (origin : Party × Good) (lower : Nat) (route : List (RouteLeg input endpoint))
    (destination : Party × Good) (upper : Nat) : Decidable (Follows input endpoint origin lower route destination upper) := by
  induction route generalizing origin lower with
  | nil => unfold Follows; infer_instance
  | cons leg rest ih => unfold Follows; infer_instance

abbrev Routes := List ((Party × Good) × List (RouteLeg input endpoint))

def findRoute (routes : Routes input endpoint) (destination : Party × Good) : Option (List (RouteLeg input endpoint)) :=
  (routes.find? (fun prior => decide (prior.1 = destination))).map Prod.snd

def insertRoute (routes : Routes input endpoint) (destination : Party × Good) (route : List (RouteLeg input endpoint)) :
    Routes input endpoint :=
  if routes.any (fun prior => decide (prior.1 = destination)) then routes else routes ++ [(destination, route)]

def extend (item : Entry input endpoint) (routes : Routes input endpoint) : Routes input endpoint :=
  routes.foldl (fun found prior =>
    if 0 < flowAt (input.law.actualDebit (item.raw input).before (item.raw input).request) prior.1.1 prior.1.2 then
      (input.law.actualCredit (item.raw input).before (item.raw input).request).foldl (fun result lot =>
        if 0 < lot.2 then insertRoute input endpoint result lot.1 (prior.2 ++ [⟨item, lot.1⟩]) else result) found
    else found) routes

def routeBetween (origin destination : Party × Good) (lower upper : Nat) :
    Option (List (RouteLeg input endpoint)) :=
  findRoute input endpoint
    ((entries input endpoint).foldl (fun routes item =>
      if lower ≤ item.position input ∧ item.position input < upper then extend input endpoint item routes else routes)
      [(origin, [])]) destination

def materialCells : List (Party × Good) :=
  (((entries input endpoint).flatMap (fun item =>
    input.law.actualDebit (item.raw input).before (item.raw input).request ++
      input.law.actualCredit (item.raw input).before (item.raw input).request)).map Prod.fst).dedup

def materialGoods : List Good := ((materialCells input endpoint).map Prod.snd).dedup

def privateControl (current : RawCurrent Party Good Technology Instrument) (port : Port) : Prop :=
  input.law.allowed current.technology port (input.law.controller current.technology port) = true ∧
    ∃ person ∈ parties input endpoint, input.law.allowed current.technology port person = false

instance (current : RawCurrent Party Good Technology Instrument) (port : Port) :
    Decidable (privateControl input endpoint current port) := by unfold privateControl; infer_instance

omit [DecidableEq Port] in
/-- The original source cohort witnesses exclusion.  It is independent of
which previous recipient now holds the same asset. -/
theorem privateControl_allows_holder_change
    (current : RawCurrent Party Good Technology Instrument) (port : Port)
    (ownerAllowed : input.law.allowed current.technology port (input.law.controller current.technology port) = true)
    (person : Party) (original : person ∈ parties input endpoint)
    (excluded : input.law.allowed current.technology port person = false) :
    privateControl input endpoint current port := ⟨ownerAllowed, person, original, excluded⟩

#print axioms privateControl_allows_holder_change

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

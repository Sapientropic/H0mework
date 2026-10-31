import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

/-! A finite chronological route search over the original inventory.  One
earliest route per material cell suffices for later positive-flow edges;
the constitutive compiler independently checks the resulting route. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

abbrev Routes := List ((Party × Good) × List (RouteLeg law current word))

def findRoute (routes : Routes law current word) (target : Party × Good) :
    Option (List (RouteLeg law current word)) :=
  ((routes.find? (fun route => decide (route.1 = target))).map Prod.snd)

def insertRoute (routes : Routes law current word) (target : Party × Good)
    (route : List (RouteLeg law current word)) : Routes law current word :=
  if routes.any (fun old => decide (old.1 = target)) then routes else routes ++ [(target, route)]

def extend (item : OriginalItem law current word) (routes : Routes law current word) :
    Routes law current word :=
  routes.foldl (fun found prior =>
    if 0 < flowAt (law.actualDebit item.val.before item.val.request) prior.1.1 prior.1.2 then
      (law.actualCredit item.val.before item.val.request).foldl (fun result lot =>
        if 0 < lot.2 then insertRoute law current word result lot.1
          (prior.2 ++ [⟨item, lot.1⟩]) else result) found
    else found) routes

def routeBetween (origin target : Party × Good) (lower upper : Nat) :
    Option (List (RouteLeg law current word)) :=
  findRoute law current word
    ((law.rawItems current word).attach.foldl (fun routes item =>
      if lower ≤ item.val.index ∧ item.val.index < upper then
        extend law current word item routes else routes) [(origin, [])]) target

def materialCells : List (Party × Good) :=
  (((law.rawItems current word).flatMap (fun item =>
    law.actualDebit item.before item.request ++ law.actualCredit item.before item.request)).map Prod.fst).dedup

def materialGoods : List Good := (materialCells law current word).map Prod.snd |>.dedup

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery

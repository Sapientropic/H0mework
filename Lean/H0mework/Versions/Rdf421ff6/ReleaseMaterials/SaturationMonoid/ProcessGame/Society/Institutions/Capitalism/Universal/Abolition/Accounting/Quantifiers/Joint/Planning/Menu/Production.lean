import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Bills
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def technologies (current : Current seed claim) : List Technology :=
  (current.raw.technology :: (Control.responseExecution mechanism past nature response).items.filterMap
    (fun item => match item.request.operation with | .revise _ technology => some technology | _ => none)).dedup

def required (current : Current seed claim) (good : Good) : ℚ :=
  ((Responsibility.Family.positiveScope mechanism past nature response).map
    (fun key => if key.2 = good then current.productive key else 0)).sum +
  ((Entitlement.Duty.scope (window seed)).map (fun key => if key.2.2 = good then current.gross key else 0)).sum +
  (seed.current.members.dedup.map (fun actor => amount Good (bills seed claim current actor) good)).sum +
  ((settlements seed).map (fun request =>
    (actualLaw seed).debit current.raw request |>.map (fun entry => if entry.1.2 = good then entry.2 else 0) |>.sum)).sum

def recipeNet (operator : Party) (technology : Technology) (good : Good) : ℚ :=
  amount Good ((actualLaw seed).technique technology operator).outputs good -
    amount Good (((actualLaw seed).technique technology operator).inputs ++
      ((actualLaw seed).technique technology operator).maintenance) good

def relevantGoods (current : Current seed claim) (operator : Party) (technology : Technology) : List Good :=
  ((Responsibility.Family.positiveScope mechanism past nature response).map Prod.snd ++
    (Entitlement.Duty.scope (window seed)).map (fun key => key.2.2) ++
    seed.current.members.flatMap (fun actor => (bills seed claim current actor).map Prod.fst) ++
    (settlements seed).flatMap (fun request => ((actualLaw seed).debit current.raw request).map (fun entry => entry.1.2)) ++
    ((actualLaw seed).revisionCost current.raw.technology technology).map Prod.fst ++
    (((actualLaw seed).technique technology operator).inputs ++ ((actualLaw seed).technique technology operator).maintenance ++
      ((actualLaw seed).technique technology operator).outputs).map Prod.fst).dedup

def dose (current : Current seed claim) (operator : Party) (technology : Technology) : Nat :=
  max 1 (((relevantGoods seed claim current operator technology).map fun good =>
    if 0 < recipeNet seed operator technology good then
      ⌈(required seed claim current good +
        amount Good ((actualLaw seed).revisionCost current.raw.technology technology) good) / recipeNet seed operator technology good⌉₊
    else 0).foldl max 0)

def productionPrefix (current : Current seed claim) (operator : Party) (technology : Technology) :
    RawEvent Party Good Port Technology Instrument :=
  if Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current then [] else
    (if technology = current.raw.technology then [] else
      [command seed (mechanism.code.siteParty mechanism.observer) (.revise operator technology)]) ++
    List.replicate (dose seed claim current operator technology)
      (command seed (mechanism.code.siteParty mechanism.observer) (.produce operator))

theorem a_paid_original_pair_does_not_authorize_another_plant_run
    (current : Current seed claim) (paid : Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current)
    (operator : Party) (technology : Technology) : productionPrefix seed claim current operator technology = [] :=
  if_pos paid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

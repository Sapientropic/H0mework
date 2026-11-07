import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Primitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Settlement.Word

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def command (_scope : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
    (signer : Party) (operation : Operation Party Good Technology Instrument) : Request Party Good Port Technology Instrument :=
  ⟨signer,[],mechanism.investmentPort,[],operation⟩

def needsWord (current : Current seed claim) : RawEvent Party Good Port Technology Instrument :=
  seed.current.members.dedup.flatMap fun actor =>
    (if (actualLaw seed).necessities current.raw actor = [] then [] else
      [command seed actor (.use actor ((actualLaw seed).necessities current.raw actor) .necessity)]) ++
    (if (actualLaw seed).mandatoryMaintenance current.raw actor = [] then [] else
      [command seed actor (.use actor ((actualLaw seed).mandatoryMaintenance current.raw actor) .maintenance)])

def bills (current : Current seed claim) (actor : Party) : Bundle Good :=
  (actualLaw seed).necessities current.raw actor ++ (actualLaw seed).mandatoryMaintenance current.raw actor

def needCells (current : Current seed claim) : List (Party × Good) :=
  seed.current.members.dedup.flatMap fun actor => ((bills seed claim current actor).map Prod.fst).dedup.map (actor,·)

def fundNeedsFrom (current : Current seed claim) (operator : Party) :
    RawEvent Party Good Port Technology Instrument → List (Party × Good) → RawEvent Party Good Port Technology Instrument
  | front, [] => front
  | front, key :: rest =>
      let stock := (Primitive.execute (actualLaw seed) current.raw 0 front).final.stock key.1 key.2
      let due := max 0 (amount Good (bills seed claim current key.1) key.2 - stock)
      let next := if operator ≠ key.1 ∧ 0 < due then
        front ++ [command seed key.1 (.transfer operator key.1 [(key.2,due)])] else front
      fundNeedsFrom current operator next rest

def fundedNeeds (current : Current seed claim) (operator : Party)
    (front : RawEvent Party Good Port Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  fundNeedsFrom seed claim current operator front (needCells seed claim current) ++ needsWord seed claim current

def settlements : RawEvent Party Good Port Technology Instrument := Evolution.Ingress.Joint.Settlement.word seed

theorem the_old_financial_tail_is_the_original_source_account :
    settlements seed = Evolution.Ingress.Joint.Settlement.word seed := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu

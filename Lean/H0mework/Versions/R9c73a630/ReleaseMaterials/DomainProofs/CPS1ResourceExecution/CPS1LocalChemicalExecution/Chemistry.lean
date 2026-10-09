import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace CPS1LocalChemicalExecution.Chemistry

inductive Atom | C | H | N | O | P | K | Mg deriving DecidableEq,Repr

/-- Ionic convention: ATP4-, ADP3-, HCO3-, carboxyphosphate2-, carbamate-,
carbamoyl phosphate2-, HPO4(2-), NAG2-, K+, Mg2+. NH3 and NH4+ stay distinct.
Rhea18029/ChEBI specify the stable ions; the mixed anhydride loses two protons
from the neutral PubChem195870 formula. This is not a patient pH measurement. -/
inductive Molecule
  | nag | potassium | magnesium | ammonia | ammonium | bicarbonate
  | atp | adp | carboxyphosphate | carbamate | carbamoylPhosphate
  | phosphate | water | proton
  deriving DecidableEq,Repr

def formula (c h n o p k mg : Nat) : Atom → Nat
  | .C => c | .H => h | .N => n | .O => o | .P => p | .K => k | .Mg => mg

def Molecule.atoms : Molecule → Atom → Nat
  | .nag => formula 7 9 1 5 0 0 0
  | .potassium => formula 0 0 0 0 0 1 0
  | .magnesium => formula 0 0 0 0 0 0 1
  | .ammonia => formula 0 3 1 0 0 0 0
  | .ammonium => formula 0 4 1 0 0 0 0
  | .bicarbonate => formula 1 1 0 3 0 0 0
  | .atp => formula 10 12 5 13 3 0 0
  | .adp => formula 10 12 5 10 2 0 0
  | .carboxyphosphate => formula 1 1 0 6 1 0 0
  | .carbamate => formula 1 2 1 2 0 0 0
  | .carbamoylPhosphate => formula 1 2 1 5 1 0 0
  | .phosphate => formula 0 1 0 4 1 0 0
  | .water => formula 0 2 0 1 0 0 0
  | .proton => formula 0 1 0 0 0 0 0

def Molecule.charge : Molecule → Int
  | .nag | .carboxyphosphate | .carbamoylPhosphate | .phosphate => -2
  | .potassium | .ammonium | .proton => 1
  | .magnesium => 2
  | .bicarbonate | .carbamate => -1
  | .atp => -4
  | .adp => -3
  | .ammonia | .water => 0

def Molecule.adenylate : Molecule → Nat | .atp | .adp => 1 | _ => 0
def Molecule.phosphateGroups (molecule : Molecule) : Nat := molecule.atoms .P

def atoms (stock : List Molecule) (atom : Atom) : Nat :=
  (stock.map (fun molecule => molecule.atoms atom)).sum
def charge (stock : List Molecule) : Int := (stock.map Molecule.charge).sum
def adenylate (stock : List Molecule) : Nat := (stock.map Molecule.adenylate).sum

inductive Step
  | deprotonateAmmonium | phosphorylateBicarbonate | formCarbamate | phosphorylateCarbamate
  deriving DecidableEq,Repr

def Step.reactants : Step → List Molecule
  | .deprotonateAmmonium => [.ammonium]
  | .phosphorylateBicarbonate => [.atp,.bicarbonate]
  | .formCarbamate => [.ammonia,.carboxyphosphate]
  | .phosphorylateCarbamate => [.atp,.carbamate]

def Step.products : Step → List Molecule
  | .deprotonateAmmonium => [.ammonia,.proton]
  | .phosphorylateBicarbonate => [.adp,.carboxyphosphate]
  | .formCarbamate => [.carbamate,.phosphate,.proton]
  | .phosphorylateCarbamate => [.adp,.carbamoylPhosphate]

theorem atomic_charge_balance (step : Step) (atom : Atom) :
    atoms step.reactants atom = atoms step.products atom ∧
      charge step.reactants = charge step.products ∧
      adenylate step.reactants = adenylate step.products := by
  cases step <;> cases atom <;> exact ⟨rfl,rfl,rfl⟩

def ammoniaInput : List Molecule := [.atp,.atp,.ammonia,.bicarbonate]
def ammoniaProducts : List Molecule := [.adp,.adp,.phosphate,.carbamoylPhosphate,.proton]
def ammoniumInput : List Molecule := [.atp,.atp,.ammonium,.bicarbonate]
def ammoniumProducts : List Molecule := [.adp,.adp,.phosphate,.carbamoylPhosphate,.proton,.proton]

theorem overall_ammonia (atom : Atom) :
    atoms ammoniaInput atom = atoms ammoniaProducts atom ∧
      charge ammoniaInput = charge ammoniaProducts ∧
      adenylate ammoniaInput = adenylate ammoniaProducts ∧
      ammoniaInput.count .atp = 2 ∧ ammoniaProducts.count .adp = 2 := by
  cases atom <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem overall_ammonium (atom : Atom) :
    atoms ammoniumInput atom = atoms ammoniumProducts atom ∧
      charge ammoniumInput = charge ammoniumProducts ∧
      adenylate ammoniumInput = adenylate ammoniumProducts ∧
      ammoniumInput.count .atp = 2 ∧ ammoniumProducts.count .adp = 2 := by
  cases atom <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem same_scaffold (scaffold : Atom → Nat) (scaffoldCharge : Int) (step : Step) (atom : Atom) :
    scaffold atom + atoms step.reactants atom = scaffold atom + atoms step.products atom ∧
      scaffoldCharge + charge step.reactants = scaffoldCharge + charge step.products := by
  have paid := atomic_charge_balance step atom
  exact ⟨congrArg (scaffold atom + ·) paid.1,congrArg (scaffoldCharge + ·) paid.2.1⟩

theorem proton_not_free_water :
    Molecule.proton.atoms .O = 0 ∧ Molecule.water.atoms .O = 1 ∧
      Molecule.proton.charge = 1 ∧ Molecule.water.charge = 0 := ⟨rfl,rfl,rfl,rfl⟩

end CPS1LocalChemicalExecution.Chemistry

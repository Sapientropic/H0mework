/-! # Source-indexed molecular DFT energy rows

All energies use nanohartree. The six terms are the BLYP functional on the
same closed-shell density matrix as the existing density calculation, not
IQA basin energies or thermal work.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Energy.Interface

inductive EnergyComponent where
  | kinetic
  | electronNuclear
  | coulomb
  | b88Exchange
  | lypCorrelation
  | nuclearRepulsion
  deriving DecidableEq, Repr, Inhabited

def energyComponents : List EnergyComponent :=
  [.kinetic, .electronNuclear, .coulomb, .b88Exchange, .lypCorrelation, .nuclearRepulsion]

structure ComponentIntegral where
  independentIntegral : Int
  rowQuantizationResidual : Int
  deriving DecidableEq, Repr, Inhabited

structure EffectiveOperatorReadout where
  expectation : Int
  electronicEnergy : Int
  doubleCountingCorrection : Int
  xcPotentialExpectation : Int
  xcEnergy : Int
  deriving DecidableEq, Repr, Inhabited

/-- Raw source columns retain every operator, overlap and incidence readout.
The block layout changes reduction depth, never row membership. -/
structure MolecularEnergyLedger where
  aoPairBlocks : Array (Array (Array Int))
  nuclearPairs : Array (Array Int)
  xcGridBlocks : Array (Array Int)
  electronNuclearAtoms : Array (Array Int)
  integral : EnergyComponent → ComponentIntegral
  effectiveOperator : EffectiveOperatorReadout
  reportedSCF : Int
  overlapTrace : Int
  overlapRoundingResidual : Int
  componentRoundingResidual : Int
  scfRecomputationResidual : Int
  deriving Inhabited

private def sumInts : List Int → Int
  | [] => 0
  | first :: rest => first + sumInts rest

def sumColumn (rows : Array (Array Int)) (column : Nat) : Int :=
  sumInts (rows.toList.map fun row => row[column]!)

def sumBlockedColumn (blocks : Array (Array (Array Int))) (column : Nat) : Int :=
  sumInts (blocks.toList.map fun rows => sumColumn rows column)

namespace MolecularEnergyLedger

def rowSum (ledger : MolecularEnergyLedger) : EnergyComponent → Int
  | .kinetic => sumBlockedColumn ledger.aoPairBlocks 10
  | .electronNuclear => sumBlockedColumn ledger.aoPairBlocks 11
  | .coulomb => sumBlockedColumn ledger.aoPairBlocks 12
  | .b88Exchange => sumColumn ledger.xcGridBlocks 3
  | .lypCorrelation => sumColumn ledger.xcGridBlocks 4
  | .nuclearRepulsion => sumColumn ledger.nuclearPairs 4

def integralSum (ledger : MolecularEnergyLedger) : Int :=
  sumInts (energyComponents.map fun component => (ledger.integral component).independentIntegral)

def grandRowSum (ledger : MolecularEnergyLedger) : Int :=
  sumInts (energyComponents.map ledger.rowSum)

def rowResidualSum (ledger : MolecularEnergyLedger) : Int :=
  sumInts (energyComponents.map fun component => (ledger.integral component).rowQuantizationResidual)

def rowToIntegralExact (ledger : MolecularEnergyLedger) : Prop :=
  ∀ component, ledger.rowSum component +
    (ledger.integral component).rowQuantizationResidual =
      (ledger.integral component).independentIntegral

end MolecularEnergyLedger

end LAlanine40K2025.Energy.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

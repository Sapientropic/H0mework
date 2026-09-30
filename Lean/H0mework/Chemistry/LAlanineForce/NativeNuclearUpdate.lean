import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.OfFn
import H0mework.Chemistry.LAlanineEnergy.NativeEnergyLedger

/-! # Source-native integer nuclear update

The force calculation supplies 13 × 3 picohartree/bohr gradient coordinates.
The update itself is computed in picobohr, with an integer normalizer and
toward-zero division. It accepts no target coordinate or future state.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Force.Interface

abbrev Atom := Fin 13
abbrev Axis := Fin 3
abbrev NuclearCoordinates := Atom → Axis → Int

def rowSquaredNorm (values : NuclearCoordinates) (atom : Atom) : Nat :=
  (List.ofFn fun axis : Axis => (values atom axis).natAbs ^ 2).sum

def maximumSquaredNorm (values : NuclearCoordinates) : Nat :=
  (List.ofFn (rowSquaredNorm values)).foldl max 0

def ceilingSqrt (value : Nat) : Nat :=
  let floor := Nat.sqrt value
  if floor * floor < value then floor + 1 else floor

def normalizer (gradient : NuclearCoordinates) : Nat :=
  ceilingSqrt (maximumSquaredNorm gradient)

def stepBudgetPicobohr : Nat := 5000000000

def stepCoordinate (normalizer : Nat) (gradient : Int) : Int :=
  let amount : Int := (stepBudgetPicobohr * gradient.natAbs / normalizer : Nat)
  if gradient < 0 then amount else -amount

def generatedDisplacement (gradient : NuclearCoordinates) : NuclearCoordinates :=
  fun atom axis => stepCoordinate (normalizer gradient) (gradient atom axis)

def generatedTarget (source gradient : NuclearCoordinates) : NuclearCoordinates :=
  fun atom axis => source atom axis + generatedDisplacement gradient atom axis

inductive Configuration where
  | current
  | generatedNext
  deriving DecidableEq, Repr

structure NuclearUpdateReadout where
  sourcePositions : NuclearCoordinates
  gradient : NuclearCoordinates
  gradientComponents : Array (Array (Array Int))
  gradientRoundingResidual : NuclearCoordinates
  recordedTargetPositions : NuclearCoordinates
  currentEnergyNanohartree : Int
  targetEnergyNanohartree : Int
  currentHeavyGraph : Array (List String × Nat)
  targetHeavyGraph : Array (List String × Nat)
  sourceNuclei : Array (String × Nat)
  targetNuclei : Array (String × Nat)
  targetEnergyLedger : Energy.Interface.MolecularEnergyLedger

end LAlanine40K2025.Force.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

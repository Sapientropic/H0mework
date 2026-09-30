import H0mework.Chemistry.LAlanineAtomicMass.SourcePreparation
import H0mework.Chemistry.LAlanineReentry.SourceSourceBoundReentry
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# Mass-number decoding on the original M3 preparation

The decoder reads the original dynamical masses and their original unit conversion.
Its integer output is checked against the retained isotope table. The fractional mass
and decimal-to-binary conversion residuals remain exact, distinct coordinates.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Source

open Force.Interface Inertia.SourceParsing
noncomputable section

/-- M3 retains the masses of the initial declared isotope preparation. -/
def actualMass : Inertia.Mechanics.Masses := Reentry.Source.stepReadout.nuclear.masses

def relativeMass (atom : Atom) : ℚ := actualMass atom / preparation.conversion

/-- Integer extraction uses no element label or default-isotope answer. -/
def massNumber (atom : Atom) : Int := round (relativeMass atom)

/-- Fractional relative atomic mass, not a nuclear binding-energy claim. -/
def massNumberResidual (atom : Atom) : ℚ := relativeMass atom - massNumber atom

/-- Original binary mass minus the exact product of the source's printed decimals. -/
def conversionResidual (atom : Atom) : ℚ :=
  actualMass atom - preparation.massAmu atom * preparation.conversion

theorem conversion_pos : 0 < preparation.conversion := by
  rw [preparation_conversion]
  norm_num

theorem actualMass_original : actualMass = Inertia.Source.stepReadout.masses := rfl

theorem source_integer_margin (atom : Atom) :
    |relativeMass atom - preparation.defaultMassNumber atom| < (1 : ℚ) / 100 := by
  change |massRead _ atom / rationalRead _ - integerRead _ atom| < (1 : ℚ) / 100
  fin_cases atom <;> norm_num [massRead, rationalRead, integerRead]

theorem massNumber_eq_recorded (atom : Atom) :
    massNumber atom = preparation.defaultMassNumber atom := by
  apply round_eq_iff.mpr
  have close := abs_lt.mp (source_integer_margin atom)
  constructor <;> linarith [close.1, close.2]

theorem massNumber_positive (atom : Atom) : 0 < massNumber atom := by
  rw [massNumber_eq_recorded]
  change 0 < integerRead _ atom
  fin_cases atom <;> decide +kernel

theorem massNumberResidual_bound (atom : Atom) :
    |massNumberResidual atom| < (1 : ℚ) / 100 := by
  unfold massNumberResidual
  rw [massNumber_eq_recorded]
  exact source_integer_margin atom

theorem conversionResidual_bound (atom : Atom) :
    |conversionResidual atom| < (2 : ℚ) / 10 ^ 12 := by
  change |massRead _ atom - massRead _ atom * rationalRead _| < (2 : ℚ) / 10 ^ 12
  fin_cases atom <;> norm_num [massRead, rationalRead]

/-- Reconstructed mass remains in the original electron-mass units. -/
def reconstructedMass (atom : Atom) : ℚ :=
  preparation.conversion * (massNumber atom + massNumberResidual atom)

theorem reconstructedMass_eq_actual : reconstructedMass = actualMass := by
  funext atom
  unfold reconstructedMass massNumberResidual relativeMass
  have nonzero := ne_of_gt conversion_pos
  field_simp
  ring

theorem preparedMass_reconstruction (atom : Atom) :
    actualMass atom = preparation.massAmu atom * preparation.conversion +
      conversionResidual atom := by
  unfold conversionResidual
  ring

theorem nitrogen_massNumber : massNumber 2 = 14 := by
  rw [massNumber_eq_recorded]
  rfl

theorem nitrogen_mass_exceeds_integer :
    14 * preparation.conversion < actualMass 2 := by
  change (14 : ℚ) * rationalRead _ < massRead _ 2
  norm_num [massRead, rationalRead]

theorem oxygen_mass_below_integer :
    actualMass 0 < 16 * preparation.conversion := by
  change massRead _ 0 < (16 : ℚ) * rationalRead _
  norm_num [massRead, rationalRead]

end
end LAlanine40K2025.AtomicMass.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

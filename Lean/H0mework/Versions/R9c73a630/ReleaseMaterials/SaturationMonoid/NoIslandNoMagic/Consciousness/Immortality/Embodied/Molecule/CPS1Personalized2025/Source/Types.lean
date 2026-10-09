import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Kernel.Rna
import Mathlib.Algebra.Order.Field.Rat

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
structure AssayRow where
  site : List Char
  columns : List String
  rawNumbers : List (Option String)
  values : List (Option ℚ)
  original : String
  deriving DecidableEq, Repr, Inhabited
structure Summary where
  median : ℚ
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr, Inhabited
structure ClinicalRegistration where
  patient : String
  dose1Day : Nat
  dose1 : ℚ
  doseInterval : Nat
  dose2 : ℚ
  firstTaper : List ℚ
  secondTaper : List ℚ
  weightDays : List Nat
  weights : List ℚ
  ammonia : List Summary
  orotic : List Summary
  doseUnit : String
  scavengerUnit : String
  ammoniaUnit : String
  oroticUnit : String
  tissueStatement : String
  deriving DecidableEq, Repr, Inhabited
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

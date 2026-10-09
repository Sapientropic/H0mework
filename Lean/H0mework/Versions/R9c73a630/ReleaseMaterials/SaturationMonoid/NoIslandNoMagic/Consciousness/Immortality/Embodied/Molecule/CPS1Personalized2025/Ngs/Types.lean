import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.Consumers
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

structure Allele where
  word : Bases
  reads : Nat
  percentage : Nat
  printedClass : String
  deriving DecidableEq, Repr, Inhabited

def replaceWindow (original : Bases) (start : Nat) (word : Bases) : Bases :=
  original.take start ++ word ++ original.drop (start+word.length)

/-- Rounded hundredths of a percentage point; the original exact software version is unreported. -/
def DisplayCompatible (reads percentage denominator : Nat) : Prop :=
  0 < denominator ∧
  (2*percentage-1)*denominator ≤ 20000*reads ∧
  20000*reads ≤ (2*percentage+1)*denominator
instance (r p n : Nat) : Decidable (DisplayCompatible r p n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

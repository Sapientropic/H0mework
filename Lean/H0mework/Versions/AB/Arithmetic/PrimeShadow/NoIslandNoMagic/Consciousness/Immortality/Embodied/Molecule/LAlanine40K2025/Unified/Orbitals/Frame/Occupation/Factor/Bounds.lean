import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Source
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerCoefficients

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped BigOperators
noncomputable section

def factorScale : Int := 1000000000000
def gammaScale : Int := 1000000000000000

def gramRealError (a b : OccupiedSlot) : Int :=
  (∑ i : Basis, (realNumerator i a * realNumerator i b +
    imagNumerator i a * imagNumerator i b)) -
      (if a=b then factorScale^2 else 0)

def gramImagError (a b : OccupiedSlot) : Int :=
  ∑ i : Basis, (realNumerator i a * imagNumerator i b -
    imagNumerator i a * realNumerator i b)

def gammaRealError (i j : Basis) : Int :=
  Reentry.Source.targetRealNumerator i j * factorScale^2 -
    2 * gammaScale * (∑ a : OccupiedSlot,
      (realNumerator i a * realNumerator j a +
        imagNumerator i a * imagNumerator j a))

def gammaImagError (i j : Basis) : Int :=
  Reentry.Source.targetImagNumerator i j * factorScale^2 -
    2 * gammaScale * (∑ a : OccupiedSlot,
      (imagNumerator i a * realNumerator j a -
        realNumerator i a * imagNumerator j a))

def gramEntryBound : Int := 1764690738892
def gammaEntryBound : Int := 3149444791880000000000000000

theorem gammaRealError_swap (i j : Basis) : gammaRealError i j = gammaRealError j i := by
  have sums : (∑ a : OccupiedSlot,
      (realNumerator i a * realNumerator j a + imagNumerator i a * imagNumerator j a)) =
      ∑ a : OccupiedSlot,
        (realNumerator j a * realNumerator i a + imagNumerator j a * imagNumerator i a) := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold gammaRealError
  rw [Reentry.Producer.targetReal_swap i j,sums]

theorem gammaImagError_swap (i j : Basis) : gammaImagError i j = -gammaImagError j i := by
  have sums : (∑ a : OccupiedSlot,
      (imagNumerator i a * realNumerator j a - realNumerator i a * imagNumerator j a)) =
      -(∑ a : OccupiedSlot,
        (imagNumerator j a * realNumerator i a - realNumerator j a * imagNumerator i a)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold gammaImagError
  rw [Reentry.Producer.targetImag_swap i j,sums]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

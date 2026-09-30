import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphKernelCompatibility
import H0mework.Versions.Y.Arithmetic.SonineCoupling.ModifiedWeakFEPoleTrace

/-!
# Nonzero source energy of the modified WeakFE pole

The pole seed has Mellin read one.  Source-level kernel compatibility therefore
forces its quarter-energy coordinate to be nonzero, and the generated energy
translations preserve that fact.  These are source-test facts; they do not
assert nonzero energy for the Riesz dual representative.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram

noncomputable section

theorem selectedModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation)
        (selectedModifiedWeakFEPoleTraceTest observation nontrivial) ≠ 0 := by
  intro energyZero
  have functionalZero :=
    quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
      (selectedCoPoissonMuntzParameter observation)
      (selectedModifiedWeakFEPoleTraceTest observation nontrivial)
      energyZero
  rw [selectedModifiedWeakFEPoleTraceTest_functional_one] at functionalZero
  norm_num at functionalZero

theorem reversalModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation)
        (reversalModifiedWeakFEPoleTraceTest observation nontrivial) ≠ 0 := by
  intro energyZero
  have functionalZero :=
    quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
      (reversalCoPoissonMuntzParameter observation)
      (reversalModifiedWeakFEPoleTraceTest observation nontrivial)
      energyZero
  rw [reversalModifiedWeakFEPoleTraceTest_functional_one] at functionalZero
  norm_num at functionalZero

theorem selectedModifiedWeakFEPole_sourceEnergy_translation_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) :
    positiveMellinQuarterEnergyTranslationIsometry shift
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation)
          (selectedModifiedWeakFEPoleTraceTest observation nontrivial)) ≠ 0 := by
  intro translatedZero
  apply selectedModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
    observation nontrivial
  apply (positiveMellinQuarterEnergyTranslationIsometry shift).injective
  calc
    positiveMellinQuarterEnergyTranslationIsometry shift
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation)
          (selectedModifiedWeakFEPoleTraceTest observation nontrivial)) = 0 :=
      translatedZero
    _ = positiveMellinQuarterEnergyTranslationIsometry shift 0 := by
      symm
      exact map_zero (positiveMellinQuarterEnergyTranslationIsometry shift)

theorem reversalModifiedWeakFEPole_sourceEnergy_translation_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) :
    positiveMellinQuarterEnergyTranslationIsometry shift
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation)
          (reversalModifiedWeakFEPoleTraceTest observation nontrivial)) ≠ 0 := by
  intro translatedZero
  apply reversalModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
    observation nontrivial
  apply (positiveMellinQuarterEnergyTranslationIsometry shift).injective
  calc
    positiveMellinQuarterEnergyTranslationIsometry shift
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation)
          (reversalModifiedWeakFEPoleTraceTest observation nontrivial)) = 0 :=
      translatedZero
    _ = positiveMellinQuarterEnergyTranslationIsometry shift 0 := by
      symm
      exact map_zero (positiveMellinQuarterEnergyTranslationIsometry shift)

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

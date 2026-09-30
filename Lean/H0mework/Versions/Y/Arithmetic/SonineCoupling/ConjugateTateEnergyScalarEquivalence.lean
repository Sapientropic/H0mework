import H0mework.Versions.Y.Arithmetic.SonineCoupling.ConjugateTateGraphSourceMorphism

/-!
# Conjugate--Tate equivalence on energy and scalar coordinates

The inverse Hilbert map is conjugation after reflection. The two inverse laws
use the already generated reflection involution and the actual `Lp`
pointwise-conjugation involution.  Isometry is derived from the forward map,
not accepted as inverse or quotient data.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex MeasureTheory
open scoped ENNReal

noncomputable section

theorem positiveMellinQuarterEnergyConjugation_involutive
    (value : PositiveMellinQuarterEnergy) :
    positiveMellinQuarterEnergyConjugation
        (positiveMellinQuarterEnergyConjugation value) = value := by
  apply Lp.ext
  filter_upwards [
    complexScalarConjugation.coeFn_compLpL value,
    complexScalarConjugation.coeFn_compLpL
      (positiveMellinQuarterEnergyConjugation value)] with x hfirst hsecond
  change ((complexScalarConjugation.compLpL
      (2 : ℝ≥0∞) (volume : Measure ℝ))
      (positiveMellinQuarterEnergyConjugation value)) x = value x
  rw [hsecond]
  change complexScalarConjugation
      (((complexScalarConjugation.compLpL
        (2 : ℝ≥0∞) (volume : Measure ℝ)) value) x) = value x
  rw [hfirst]
  simp [complexScalarConjugation]

/-- Explicit inverse Hilbert map: conjugation after reflection. -/
def positiveMellinQuarterEnergyConjugateTateInverse :
    PositiveMellinQuarterEnergy →L⋆[ℂ] PositiveMellinQuarterEnergy :=
  positiveMellinQuarterEnergyConjugation.comp
    positiveMellinQuarterEnergyReflectionIsometry.toLinearIsometry.toContinuousLinearMap

theorem positiveMellinQuarterEnergyConjugateTate_leftInverse :
    Function.LeftInverse positiveMellinQuarterEnergyConjugateTateInverse
      positiveMellinQuarterEnergyConjugateTate := by
  intro value
  change positiveMellinQuarterEnergyConjugation
      (positiveMellinQuarterEnergyReflection
        (positiveMellinQuarterEnergyReflection
          (positiveMellinQuarterEnergyConjugation value))) = value
  rw [positiveMellinQuarterEnergyReflection_involutive,
    positiveMellinQuarterEnergyConjugation_involutive]

theorem positiveMellinQuarterEnergyConjugateTate_rightInverse :
    Function.RightInverse positiveMellinQuarterEnergyConjugateTateInverse
      positiveMellinQuarterEnergyConjugateTate := by
  intro value
  change positiveMellinQuarterEnergyReflection
      (positiveMellinQuarterEnergyConjugation
        (positiveMellinQuarterEnergyConjugation
          (positiveMellinQuarterEnergyReflection value))) = value
  rw [positiveMellinQuarterEnergyConjugation_involutive,
    positiveMellinQuarterEnergyReflection_involutive]

def positiveMellinQuarterEnergyConjugateTateLinearEquiv :
    PositiveMellinQuarterEnergy ≃ₛₗ[starRingEnd ℂ]
      PositiveMellinQuarterEnergy where
  toFun := positiveMellinQuarterEnergyConjugateTate
  invFun := positiveMellinQuarterEnergyConjugateTateInverse
  left_inv := positiveMellinQuarterEnergyConjugateTate_leftInverse
  right_inv := positiveMellinQuarterEnergyConjugateTate_rightInverse
  map_add' := positiveMellinQuarterEnergyConjugateTate.map_add
  map_smul' := positiveMellinQuarterEnergyConjugateTate.map_smulₛₗ

def positiveMellinQuarterEnergyConjugateTateIsometricEquiv :
    PositiveMellinQuarterEnergy ≃ₛₗᵢ[starRingEnd ℂ]
      PositiveMellinQuarterEnergy :=
  ⟨positiveMellinQuarterEnergyConjugateTateLinearEquiv,
    fun value => by
      change ‖positiveMellinQuarterEnergyConjugateTate value‖ = ‖value‖
      change ‖positiveMellinQuarterEnergyReflection
          (positiveMellinQuarterEnergyConjugation value)‖ = ‖value‖
      rw [positiveMellinQuarterEnergyReflection_norm,
        positiveMellinQuarterEnergyConjugation_norm]⟩

def complexScalarConjugationIsometricEquiv :
    ℂ ≃ₛₗᵢ[starRingEnd ℂ] ℂ :=
  ⟨starLinearEquiv ℂ, norm_star⟩

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

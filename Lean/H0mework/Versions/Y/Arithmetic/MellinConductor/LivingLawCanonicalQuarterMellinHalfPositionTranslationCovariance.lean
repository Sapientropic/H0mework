import H0mework.Versions.Y.Arithmetic.MellinConductor.HalfPositionDomain

/-!
# Translation covariance of the maximal half-position operator

The existing Quarter-Mellin energy translation preserves the maximal
`x/2` domain.  On that domain its commutator with half-position is exactly
`h/2` times the same translated state.  This is a closed-operator identity,
not a bounded extension or a vanishing claim.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionDomain

open Filter MeasureTheory

open scoped ENNReal

noncomputable section

theorem positiveMellinQuarterEnergyTranslation_coeFn
    (shift : ℝ) (value : PositiveMellinQuarterEnergy) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      positiveMellinQuarterEnergyTranslation shift value x =
        value (shift + x) := by
  exact Lp.coeFn_compMeasurePreserving value
    (measurePreserving_add_left (volume : Measure ℝ) shift)

def translatedHalfPositionOutput
    (shift : ℝ) (value : HalfPositionOperator.domain) :
    PositiveMellinQuarterEnergy :=
  positiveMellinQuarterEnergyTranslation shift
      (HalfPositionOperator value) -
    ((shift / 2 : ℝ) : ℂ) •
      positiveMellinQuarterEnergyTranslation shift value.1

theorem translatedHalfPositionOutput_ae
    (shift : ℝ) (value : HalfPositionOperator.domain) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      translatedHalfPositionOutput shift value x =
        ((x / 2 : ℝ) : ℂ) *
          positiveMellinQuarterEnergyTranslation shift value.1 x := by
  have shiftedPositionAE :=
    (measurePreserving_add_left (volume : Measure ℝ) shift
      ).quasiMeasurePreserving.ae (halfPositionOperator_apply_ae value)
  filter_upwards [
      positiveMellinQuarterEnergyTranslation_coeFn
        shift (HalfPositionOperator value),
      positiveMellinQuarterEnergyTranslation_coeFn shift value.1,
      shiftedPositionAE,
      Lp.coeFn_sub
        (positiveMellinQuarterEnergyTranslation shift
          (HalfPositionOperator value))
        (((shift / 2 : ℝ) : ℂ) •
          positiveMellinQuarterEnergyTranslation shift value.1),
      Lp.coeFn_smul ((shift / 2 : ℝ) : ℂ)
        (positiveMellinQuarterEnergyTranslation shift value.1)]
    with x outputTranslateAt inputTranslateAt positionAt subAt smulAt
  unfold translatedHalfPositionOutput
  rw [subAt, Pi.sub_apply, outputTranslateAt, smulAt, Pi.smul_apply,
    inputTranslateAt, positionAt]
  push_cast
  ring

theorem translation_mem_halfPositionOperator_domain
    (shift : ℝ) (value : HalfPositionOperator.domain) :
    positiveMellinQuarterEnergyTranslation shift value.1 ∈
      HalfPositionOperator.domain := by
  rw [mem_halfPositionOperator_domain_iff]
  exact (memLp_congr_ae
    (translatedHalfPositionOutput_ae shift value)).mp
      (Lp.memLp (translatedHalfPositionOutput shift value))

def halfPositionDomainTranslation (shift : ℝ) :
    HalfPositionOperator.domain →ₗ[ℂ] HalfPositionOperator.domain where
  toFun value :=
    ⟨positiveMellinQuarterEnergyTranslation shift value.1,
      translation_mem_halfPositionOperator_domain shift value⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add (positiveMellinQuarterEnergyTranslation shift)
      left.1 right.1
  map_smul' coefficient value := by
    apply Subtype.ext
    exact map_smul (positiveMellinQuarterEnergyTranslation shift)
      coefficient value.1

theorem halfPositionOperator_translation_eq
    (shift : ℝ) (value : HalfPositionOperator.domain) :
    HalfPositionOperator (halfPositionDomainTranslation shift value) =
      translatedHalfPositionOutput shift value := by
  apply Lp.ext
  filter_upwards [
      halfPositionOperator_apply_ae
        (halfPositionDomainTranslation shift value),
      translatedHalfPositionOutput_ae shift value]
    with x operatorAt outputAt
  exact operatorAt.trans outputAt.symm

/-- Exact graph-level commutator.  In the integer chart `shift=2 log n`,
the generated coefficient is `log n`. -/
theorem halfPosition_translation_commutator
    (shift : ℝ) (value : HalfPositionOperator.domain) :
    positiveMellinQuarterEnergyTranslation shift
          (HalfPositionOperator value) -
        HalfPositionOperator (halfPositionDomainTranslation shift value) =
      ((shift / 2 : ℝ) : ℂ) •
        positiveMellinQuarterEnergyTranslation shift value.1 := by
  rw [halfPositionOperator_translation_eq]
  unfold translatedHalfPositionOutput
  abel

end
end HalfPositionDomain
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

import H0mework.Realization.Graph.CokernelNaturality
import H0mework.Arithmetic.MuntzAction.CoPoissonMuntzDilationRelationSquare

/-!
# Descended dilation action on the Müntz graph cokernel

Dividing the source, energy and relation actions by the generated nonzero
Mellin character makes the graph functional square strict.  Generic relation
graph naturality then descends the full dilation square to a continuous
endomorphism of the graph cokernel.  The Riesz trace is stationary under this
character-normalized action; no norm isometry or current vanishing is claimed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedFunctionalGraphPerfectification
open scoped SchwartzMap InnerProductSpace

noncomputable section

def quarterDilationCharacter (z : ℂ) (scale : ℝ) : ℂ :=
  (scale : ℂ) ^ ((1 / 4 : ℂ) - z)

theorem quarterDilationCharacter_ne_zero
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    quarterDilationCharacter z scale ≠ 0 := by
  unfold quarterDilationCharacter
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr positive.ne'))

/-- Character-normalized source dilation.  It fixes the Mellin functional
but is not asserted to preserve the graph norm. -/
def normalizedQuarterDilationTestAction
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    QuarterMellinL2Test z →ₗ[ℂ] QuarterMellinL2Test z :=
  (quarterDilationCharacter z scale)⁻¹ •
    quarterDilationTestAction z scale positive

def normalizedQuarterDilationEnergyAction
    (z : ℂ) (scale : ℝ) :
    PositiveMellinQuarterEnergy →L[ℂ] PositiveMellinQuarterEnergy :=
  (quarterDilationCharacter z scale)⁻¹ •
    (positiveMellinQuarterEnergyTranslationIsometry
      (Real.log scale)).toContinuousLinearEquiv.toContinuousLinearMap

def normalizedQuarterMuntzSchwartzDilationAction
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (quarterDilationCharacter z scale)⁻¹ •
    quarterMuntzSchwartzDilationAction scale positive

theorem normalizedQuarterDilation_feature_square
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    (normalizedQuarterDilationEnergyAction z scale).toLinearMap.comp
        (quarterMellinL2Feature z) =
      (quarterMellinL2Feature z).comp
        (normalizedQuarterDilationTestAction z scale positive) := by
  apply LinearMap.ext
  intro value
  change (quarterDilationCharacter z scale)⁻¹ •
      positiveMellinQuarterEnergyTranslation (Real.log scale)
        (quarterMellinL2Feature z value) =
    quarterMellinL2Feature z
      ((quarterDilationCharacter z scale)⁻¹ •
        quarterDilationTestAction z scale positive value)
  rw [map_smul]
  congr 1
  exact LinearMap.congr_fun
    (quarterDilationFeature_covariance z scale positive) value

theorem normalizedQuarterDilation_functional_fixed
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    (quarterMellinL2Functional z).comp
        (normalizedQuarterDilationTestAction z scale positive) =
      quarterMellinL2Functional z := by
  apply LinearMap.ext
  intro value
  change quarterMellinL2Functional z
      ((quarterDilationCharacter z scale)⁻¹ •
        quarterDilationTestAction z scale positive value) = _
  rw [map_smul]
  have eigen := LinearMap.congr_fun
    (quarterDilationFunctional_eigenlaw z scale positive) value
  change quarterMellinL2Functional z
      (quarterDilationTestAction z scale positive value) =
    quarterDilationCharacter z scale •
      quarterMellinL2Functional z value at eigen
  rw [eigen, smul_smul]
  rw [inv_mul_cancel₀
    (quarterDilationCharacter_ne_zero z scale positive), one_smul]

def normalizedQuarterDilationGraphMorphism
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    GraphSourceMorphism
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (quarterMellinL2Feature z) (quarterMellinL2Functional z) where
  sourceMap := normalizedQuarterDilationTestAction z scale positive
  hilbertMap := normalizedQuarterDilationEnergyAction z scale
  feature_commutes := normalizedQuarterDilation_feature_square z scale positive
  functional_commutes :=
    normalizedQuarterDilation_functional_fixed z scale positive

theorem normalizedQuarterDilation_muntzRelation_square
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    (normalizedQuarterDilationTestAction z scale positive).comp
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) =
      (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf).comp
        (normalizedQuarterMuntzSchwartzDilationAction
          z scale positive) := by
  apply LinearMap.ext
  intro test
  change (quarterDilationCharacter z scale)⁻¹ •
      quarterDilationTestAction z scale positive
        (coPoissonQuarterMellinConvergentMap
          z positiveZ belowHalf test) =
    coPoissonQuarterMellinConvergentMap z positiveZ belowHalf
      ((quarterDilationCharacter z scale)⁻¹ •
        quarterMuntzSchwartzDilationAction scale positive test)
  rw [map_smul]
  congr 1
  exact LinearMap.congr_fun
    (quarterDilation_muntzRelation_square
      z positiveZ belowHalf scale positive) test

def normalizedQuarterDilationRelationMorphism
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    RelationGraphSourceMorphism
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf)
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) where
  graphMorphism := normalizedQuarterDilationGraphMorphism z scale positive
  relationMap :=
    normalizedQuarterMuntzSchwartzDilationAction z scale positive
  relation_commutes :=
    normalizedQuarterDilation_muntzRelation_square
      z positiveZ belowHalf scale positive

/-- Continuous source-generated dilation action on the complete relation
quotient. -/
def coPoissonMuntzGraphCokernelDilationAction
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    CoPoissonMuntzGraphCokernel z positiveZ belowHalf →L[ℂ]
      CoPoissonMuntzGraphCokernel z positiveZ belowHalf :=
  (normalizedQuarterDilationRelationMorphism
    z positiveZ belowHalf scale positive).quotientMap

@[simp] theorem coPoissonMuntzGraphCokernelDilationAction_source
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale)
    (value : QuarterMellinL2Test z) :
    coPoissonMuntzGraphCokernelDilationAction
        z positiveZ belowHalf scale positive
        (coPoissonMuntzGraphSourceMap z positiveZ belowHalf value) =
      coPoissonMuntzGraphSourceMap z positiveZ belowHalf
        (normalizedQuarterDilationTestAction z scale positive value) := by
  exact RelationGraphSourceMorphism.quotientMap_source_readback
    (normalizedQuarterDilationRelationMorphism
      z positiveZ belowHalf scale positive) value

/-- The canonical Riesz trace is stationary under the descended,
character-normalized dilation. -/
theorem coPoissonMuntzRieszTrace_dilation_stationary
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0)
    (scale : ℝ) (positive : 0 < scale)
    (value : QuarterMellinL2Test z) :
    inner ℂ (coPoissonMuntzRieszVector z positiveZ belowHalf zero)
        (coPoissonMuntzGraphCokernelDilationAction
          z positiveZ belowHalf scale positive
          (coPoissonMuntzGraphSourceMap z positiveZ belowHalf value)) =
      inner ℂ (coPoissonMuntzRieszVector z positiveZ belowHalf zero)
        (coPoissonMuntzGraphSourceMap z positiveZ belowHalf value) := by
  rw [coPoissonMuntzGraphCokernelDilationAction_source,
    coPoissonMuntzRieszVector_source_readback,
    coPoissonMuntzRieszVector_source_readback]
  exact LinearMap.congr_fun
    (normalizedQuarterDilation_functional_fixed z scale positive) value

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

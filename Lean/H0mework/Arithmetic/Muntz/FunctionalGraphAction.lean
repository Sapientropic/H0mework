import H0mework.Realization.Graph.Action
import H0mework.Arithmetic.Muntz.FunctionalGraphPerfectification

/-!
# Actual scale-three action on the A1c functional graph

The normalized positive dilation preserves the lawful quarter-`L²` Mellin
test carrier.  Its literal `L²` translation covariance and Mellin character
law generate the diagonal action on the source-owned functional graph and on
its completion.  No isometry, endpoint equality, or annihilation is assumed.
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
open SourceGeneratedFunctionalGraphPerfectification

noncomputable section

def quarterScaleThreeTestAction (z : ℂ) :
    QuarterMellinL2Test z →ₗ[ℂ] QuarterMellinL2Test z where
  toFun value := ⟨
    positiveMellinQuarterNormalizedDilation
      positiveMellinQuarterNoGoScale
      positiveMellinQuarterNoGoScale_pos value.1,
    ⟨positiveQuarterNormalizedDilation_mem_quarterL2
        positiveMellinQuarterNoGoScale
        positiveMellinQuarterNoGoScale_pos value.1 value.2.1,
      by
        have raw := (positiveMellinDilation z
          positiveMellinQuarterNoGoScale
          positiveMellinQuarterNoGoScale_pos
          ⟨value.1, value.2.2⟩).2
        change MellinConvergent
          (positiveMellinExtension
            (positiveMellinQuarterNormalizedDilation
              positiveMellinQuarterNoGoScale
              positiveMellinQuarterNoGoScale_pos value.1)) z
        rw [positiveMellinQuarterNormalizedDilation,
          LinearMap.smul_apply, map_smul]
        exact raw.const_smul
          (positiveMellinQuarterDilationWeight
            positiveMellinQuarterNoGoScale)⟩⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add (positiveMellinQuarterNormalizedDilation
      positiveMellinQuarterNoGoScale
      positiveMellinQuarterNoGoScale_pos) left.1 right.1
  map_smul' coefficient value := by
    apply Subtype.ext
    exact map_smul (positiveMellinQuarterNormalizedDilation
      positiveMellinQuarterNoGoScale
      positiveMellinQuarterNoGoScale_pos) coefficient value.1

theorem quarterScaleThreeFeature_covariance (z : ℂ) :
    quarterScaleThreeEnergyAction.toLinearMap.comp
        (quarterMellinL2Feature z) =
      (quarterMellinL2Feature z).comp
        (quarterScaleThreeTestAction z) := by
  apply LinearMap.ext
  intro value
  let raw : PositiveMellinQuarterL2 := ⟨value.1, value.2.1⟩
  have source := positiveMellinQuarterLpValue_normalizedDilation
    positiveMellinQuarterNoGoScale
    positiveMellinQuarterNoGoScale_pos raw
  change positiveMellinQuarterEnergyTranslation
      (Real.log positiveMellinQuarterNoGoScale)
        (positiveMellinQuarterLpValue raw) =
    quarterMellinL2Feature z (quarterScaleThreeTestAction z value)
  calc
    _ = positiveMellinQuarterLpValue
        (positiveMellinQuarterL2NormalizedDilation
          positiveMellinQuarterNoGoScale
          positiveMellinQuarterNoGoScale_pos raw) := source.symm
    _ = _ := by
      exact MemLp.toLp_congr
        (positiveMellinQuarterL2_memLp
          (positiveMellinQuarterL2NormalizedDilation
            positiveMellinQuarterNoGoScale
            positiveMellinQuarterNoGoScale_pos raw))
        ((quarterScaleThreeTestAction z value).2.1)
        (ae_of_all (volume : Measure ℝ) fun _ => rfl)

theorem quarterScaleThreeWeight_eq_cpow_quarter :
    positiveMellinQuarterDilationWeight
        positiveMellinQuarterNoGoScale =
      (positiveMellinQuarterNoGoScale : ℂ) ^ (1 / 4 : ℂ) := by
  calc
    positiveMellinQuarterDilationWeight
        positiveMellinQuarterNoGoScale =
        ((positiveMellinQuarterNoGoScale ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
      unfold positiveMellinQuarterDilationWeight
      rw [Real.rpow_def_of_pos positiveMellinQuarterNoGoScale_pos]
      congr 3
      ring
    _ = (positiveMellinQuarterNoGoScale : ℂ) ^ (1 / 4 : ℂ) := by
      convert Complex.ofReal_cpow
        positiveMellinQuarterNoGoScale_pos.le (1 / 4 : ℝ) using 1
      norm_num

theorem quarterScaleThreeCharacter_factor (z : ℂ) :
    positiveMellinQuarterDilationWeight positiveMellinQuarterNoGoScale *
        (positiveMellinQuarterNoGoScale : ℂ) ^ (-z) =
      (positiveMellinQuarterNoGoScale : ℂ) ^ ((1 / 4 : ℂ) - z) := by
  rw [quarterScaleThreeWeight_eq_cpow_quarter,
    ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr positiveMellinQuarterNoGoScale_pos.ne')]
  congr 2

theorem quarterScaleThreeFunctional_eigenlaw (z : ℂ) :
    (quarterMellinL2Functional z).comp
        (quarterScaleThreeTestAction z) =
      ((positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - z)) • quarterMellinL2Functional z := by
  apply LinearMap.ext
  intro value
  let convergent : positiveMellinConvergentSubmodule z :=
    ⟨value.1, value.2.2⟩
  let dilated := positiveMellinDilation z
    positiveMellinQuarterNoGoScale
    positiveMellinQuarterNoGoScale_pos convergent
  have raw := positiveMellinFunctional_dilation z
    positiveMellinQuarterNoGoScale
    positiveMellinQuarterNoGoScale_pos convergent
  change positiveMellinFunctional z
      ⟨(quarterScaleThreeTestAction z value).1,
        (quarterScaleThreeTestAction z value).2.2⟩ = _
  calc
    _ = positiveMellinFunctional z
        ((positiveMellinQuarterDilationWeight
          positiveMellinQuarterNoGoScale) • dilated) := by rfl
    _ = (positiveMellinQuarterDilationWeight
          positiveMellinQuarterNoGoScale) •
        positiveMellinFunctional z dilated := by rw [map_smul]
    _ = (positiveMellinQuarterDilationWeight
          positiveMellinQuarterNoGoScale) •
        ((positiveMellinQuarterNoGoScale : ℂ) ^ (-z) •
          positiveMellinFunctional z convergent) := by rw [raw]
    _ = ((positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - z)) •
        positiveMellinFunctional z convergent := by
      simp only [smul_eq_mul]
      rw [← mul_assoc, quarterScaleThreeCharacter_factor]

def quarterFunctionalGraphCovarianceAtCoordinate (coordinate : ℂ) :
    GraphCovariance
      (quarterMellinL2Feature (coordinate / 2))
      (quarterMellinL2Functional (coordinate / 2)) where
  sourceAction := quarterScaleThreeTestAction (coordinate / 2)
  hilbertAction := quarterScaleThreeEnergyAction
  character := (positiveMellinQuarterNoGoScale : ℂ) ^
    ((1 / 4 : ℂ) - coordinate / 2)
  feature_covariance := quarterScaleThreeFeature_covariance (coordinate / 2)
  functional_eigenlaw :=
    quarterScaleThreeFunctional_eigenlaw (coordinate / 2)

def zeroOwnedQuarterGraphCovariance
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    GraphCovariance
      (quarterMellinL2Feature (observation.coordinate / 2))
      (quarterMellinL2Functional (observation.coordinate / 2)) :=
  quarterFunctionalGraphCovarianceAtCoordinate observation.coordinate

def zeroOwnedQuarterGraphActionDisposition
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :=
  settleGraphAction (zeroOwnedQuarterGraphCovariance observation)

theorem zeroOwnedQuarterGraphFunctional_eigenlaw
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (value : ZeroOwnedQuarterFunctionalGraphAmbient observation) :
    zeroOwnedQuarterFunctionalGraphCoordinate observation
        (graphHilbertAction
          (zeroOwnedQuarterGraphCovariance observation) value) =
      (positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - observation.coordinate / 2) *
        zeroOwnedQuarterFunctionalGraphCoordinate observation value :=
  graphHilbertFunctional_eigenlaw
    (zeroOwnedQuarterGraphCovariance observation) value

theorem zeroOwnedQuarterFunctionalGraphEquivariantResidual_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    SourceGeneratedTestHilbertGeneralizedDual.canonicalEquivariantExtensionResidual
        (zeroOwnedQuarterFunctionalGraphFeature observation)
        (graphHilbertAction
          (zeroOwnedQuarterGraphCovariance observation))
        ((positiveMellinQuarterNoGoScale : ℂ) ^
          ((1 / 4 : ℂ) - observation.coordinate / 2))
        (quarterMellinL2Functional (observation.coordinate / 2)) = 0 :=
  graphEquivariantExtensionResidual_zero
    (zeroOwnedQuarterGraphCovariance observation)

end
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

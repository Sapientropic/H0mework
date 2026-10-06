import H0mework.Arithmetic.SonineSource.CanonicalSourceIntegralOrbitAction

/-!
# Source-seeded integral graph-orbit action

The integral dilation history acts on every actual quarter-`L2` source test,
not only on the previously chosen normalized detector shell.  This file
exposes that already present action once and proves its source/graph
naturality on the whole integral carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction

open Character.GlobalCoPoissonCurrent
open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

def seededIntegralDilationTestOrbit
    (z : ℂ) (seed : QuarterMellinL2Test z) :
    IntegralScaleCarrier →ₗ[ℤ] QuarterMellinL2Test z :=
  canonicalBasis.constr ℤ fun scale =>
    quarterDilationTestAction z
      (scaleSquare scale) (scaleSquare_pos scale) seed

@[simp] theorem seededIntegralDilationTestOrbit_delta
    (z : ℂ) (seed : QuarterMellinL2Test z)
    (scale : Units NNReal) :
    seededIntegralDilationTestOrbit z seed (delta scale) =
      quarterDilationTestAction z
        (scaleSquare scale) (scaleSquare_pos scale) seed := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

def seededIntegralGraphOrbit
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (seed : QuarterMellinL2Test z) :
    IntegralScaleCarrier →ₗ[ℤ]
      CoPoissonMuntzGraphCokernel z positive belowHalf :=
  (coPoissonMuntzGraphSourceMap z positive belowHalf
    |>.restrictScalars ℤ).comp
      (seededIntegralDilationTestOrbit z seed)

@[simp] theorem seededIntegralGraphOrbit_delta
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (seed : QuarterMellinL2Test z) (scale : Units NNReal) :
    seededIntegralGraphOrbit z positive belowHalf seed (delta scale) =
      coPoissonMuntzGraphSourceMap z positive belowHalf
        (quarterDilationTestAction z
          (scaleSquare scale) (scaleSquare_pos scale) seed) := by
  simp [seededIntegralGraphOrbit]

theorem seededIntegralGraphOrbit_add
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (left right : QuarterMellinL2Test z) :
    seededIntegralGraphOrbit z positive belowHalf (left + right) =
      seededIntegralGraphOrbit z positive belowHalf left +
        seededIntegralGraphOrbit z positive belowHalf right := by
  apply canonicalBasis.ext
  intro scale
  rw [canonicalBasis_apply]
  simp only [seededIntegralGraphOrbit_delta, LinearMap.add_apply, map_add]

theorem seededIntegralGraphOrbit_smul
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (coefficient : ℂ) (seed : QuarterMellinL2Test z) :
    seededIntegralGraphOrbit z positive belowHalf (coefficient • seed) =
      coefficient • seededIntegralGraphOrbit z positive belowHalf seed := by
  apply canonicalBasis.ext
  intro scale
  rw [canonicalBasis_apply]
  simp only [seededIntegralGraphOrbit_delta, LinearMap.smul_apply, map_smul]

/-- The same integral left translation and quotient dilation are sibling
faces of one source-seeded action. -/
theorem seededIntegralGraphOrbit_action_square
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (seed : QuarterMellinL2Test z) (scale : Units NNReal) :
    (rawCoPoissonMuntzGraphCokernelDilationAction
        z positive belowHalf
        (scaleSquare scale) (scaleSquare_pos scale)
      |>.toLinearMap.restrictScalars ℤ).comp
        (seededIntegralGraphOrbit z positive belowHalf seed) =
      (seededIntegralGraphOrbit z positive belowHalf seed).comp
        (leftTranslation scale).toLinearMap := by
  apply canonicalBasis.ext
  intro right
  have translated :
      (leftTranslation scale).toLinearMap (delta right) =
        delta (scale * right) :=
    leftTranslation_delta scale right
  rw [canonicalBasis_apply]
  change
    rawCoPoissonMuntzGraphCokernelDilationAction
        z positive belowHalf
        (scaleSquare scale) (scaleSquare_pos scale)
        (coPoissonMuntzGraphSourceMap z positive belowHalf
          (seededIntegralDilationTestOrbit z seed (delta right))) =
      coPoissonMuntzGraphSourceMap z positive belowHalf
        (seededIntegralDilationTestOrbit z seed
          ((leftTranslation scale).toLinearMap (delta right)))
  rw [seededIntegralDilationTestOrbit_delta, translated,
    seededIntegralDilationTestOrbit_delta,
    rawCoPoissonMuntzGraphCokernelDilationAction_source]
  apply congrArg (coPoissonMuntzGraphSourceMap z positive belowHalf)
  have composition := LinearMap.congr_fun
    (quarterDilationTestAction_comp z
      (scaleSquare scale) (scaleSquare right)
      (scaleSquare_pos scale) (scaleSquare_pos right)) seed
  simpa only [LinearMap.comp_apply, scaleSquare_mul] using composition

/-- If the seed is an actual relation class, its entire source-generated
integral dilation orbit vanishes in the same quotient. -/
theorem seededIntegralGraphOrbit_eq_zero_of_source_eq_zero
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (seed : QuarterMellinL2Test z)
    (sourceZero :
      coPoissonMuntzGraphSourceMap z positive belowHalf seed = 0) :
    seededIntegralGraphOrbit z positive belowHalf seed = 0 := by
  apply canonicalBasis.ext
  intro scale
  rw [canonicalBasis_apply, seededIntegralGraphOrbit_delta]
  rw [← rawCoPoissonMuntzGraphCokernelDilationAction_source,
    sourceZero, map_zero]
  rfl

theorem seededIntegralGraphOrbit_delta_sub_delta
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (seed : QuarterMellinL2Test z) (scale : Units NNReal) :
    seededIntegralGraphOrbit z positive belowHalf seed
        (delta 1 - delta scale) =
      coPoissonMuntzGraphSourceMap z positive belowHalf seed -
        rawCoPoissonMuntzGraphCokernelDilationAction
          z positive belowHalf
          (scaleSquare scale) (scaleSquare_pos scale)
          (coPoissonMuntzGraphSourceMap z positive belowHalf seed) := by
  rw [map_sub, seededIntegralGraphOrbit_delta,
    seededIntegralGraphOrbit_delta]
  have oneScale : scaleSquare (1 : Units NNReal) = 1 := by
    simp [scaleSquare, scaleValue]
  have oneAction :
      quarterDilationTestAction z
          (scaleSquare (1 : Units NNReal)) (scaleSquare_pos 1) seed = seed := by
    simpa only [oneScale, LinearMap.id_apply] using LinearMap.congr_fun
      (quarterDilationTestAction_one z) seed
  rw [oneAction, rawCoPoissonMuntzGraphCokernelDilationAction_source]

end
end IntegralGraphJointAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

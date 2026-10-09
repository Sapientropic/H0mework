import H0mework.Versions.V2.Arithmetic.BurnolMellin.GenericPhysicalMellinRead
import H0mework.Arithmetic.MellinProjection.CompletedEvaluator

/-!
# Fixed quarter-radius ambient completed-Mellin projection

The historical ambient interface is now a direct `r = 1/4` specialization
of the radius-parametrized evaluator, kernel, and projection theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open scoped InnerProductSpace

noncomputable section

private theorem burnolAmbientCommonGapRadius_positive :
    0 < burnolUnscaledCommonGapRadius := by
  norm_num [burnolUnscaledCommonGapRadius]

def burnolAmbientCompletedMellinEvaluator
    (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  burnolRadiusAmbientCompletedMellinEvaluator burnolUnscaledCommonGapRadius
    burnolAmbientCommonGapRadius_positive coordinate

theorem burnolAmbientCompletedMellinEvaluator_restrict
    (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolAmbientCompletedMellinEvaluator coordinate).comp
        (Submodule.subtypeL
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule) =
      burnolCompletedMellinEvaluator coordinate := by
  exact burnolRadiusAmbientCompletedMellinEvaluator_restrict
    burnolUnscaledCommonGapRadius burnolAmbientCommonGapRadius_positive
      coordinate

def burnolAmbientCompletedMellinRieszVector
    (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolRadiusAmbientCompletedMellinRieszVector burnolUnscaledCommonGapRadius
    burnolAmbientCommonGapRadius_positive coordinate

def burnolAmbientCompletedMellinKernelFormula
    (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolRadiusAmbientCompletedMellinKernelFormula burnolUnscaledCommonGapRadius
    burnolAmbientCommonGapRadius_positive coordinate

theorem burnolAmbientCompletedMellinRieszVector_readback
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (burnolAmbientCompletedMellinRieszVector coordinate) value =
      burnolAmbientCompletedMellinEvaluator coordinate value := by
  exact burnolRadiusAmbientCompletedMellinRieszVector_readback
    burnolUnscaledCommonGapRadius burnolAmbientCommonGapRadius_positive
      coordinate value

theorem burnolAmbientCompletedMellinRieszVector_eq_kernelFormula
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolAmbientCompletedMellinRieszVector coordinate =
      burnolAmbientCompletedMellinKernelFormula coordinate := by
  exact burnolRadiusAmbientCompletedMellinRieszVector_eq_kernelFormula
    burnolUnscaledCommonGapRadius burnolAmbientCommonGapRadius_positive
      coordinate

theorem burnolCompletedMellinRieszVector_eq_ambientProjection
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinRieszVector coordinate =
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius
        ).toSubmodule.orthogonalProjectionOnto
          (burnolAmbientCompletedMellinRieszVector coordinate) := by
  exact burnolRadiusCompletedMellinRieszVector_eq_ambientProjection
    burnolUnscaledCommonGapRadius burnolAmbientCommonGapRadius_positive
      coordinate

theorem burnolCompletedMellinEvaluator_riesz_eq_norm_sq
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinEvaluator coordinate
        (burnolCompletedMellinRieszVector coordinate) =
      (‖burnolCompletedMellinRieszVector coordinate‖ : ℂ) ^ 2 := by
  exact burnolRadiusCompletedMellinEvaluator_riesz_eq_norm_sq
    burnolUnscaledCommonGapRadius burnolAmbientCommonGapRadius_positive
      coordinate

theorem burnolCompletedMellinEvaluator_ne_zero_iff_ambientProjection_ne_zero
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinEvaluator coordinate ≠ 0 ↔
      ((evenBurnolClosedFace burnolUnscaledCommonGapRadius
        ).toSubmodule.orthogonalProjectionOnto
          (burnolAmbientCompletedMellinKernelFormula coordinate)) ≠ 0 := by
  exact
    burnolRadiusCompletedMellinEvaluator_ne_zero_iff_ambientProjection_ne_zero
      burnolUnscaledCommonGapRadius burnolAmbientCommonGapRadius_positive
        coordinate

theorem burnolAmbientCompletedMellinEvaluator_eq_radiusSpecialization
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolAmbientCompletedMellinEvaluator coordinate =
      burnolRadiusAmbientCompletedMellinEvaluator (1 / 4 : ℝ)
        (by norm_num) coordinate := by
  rfl

theorem burnolAmbientCompletedMellinKernelFormula_eq_radiusSpecialization
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolAmbientCompletedMellinKernelFormula coordinate =
      burnolRadiusAmbientCompletedMellinKernelFormula (1 / 4 : ℝ)
        (by norm_num) coordinate := by
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

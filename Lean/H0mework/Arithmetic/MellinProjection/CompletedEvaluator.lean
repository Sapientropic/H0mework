import H0mework.Arithmetic.MellinProjection.TailKernel

/-!
# Radius-parametrized completed-Mellin evaluator and ambient projection

The physical evaluator is the restriction of one explicit ambient functional.
Its Riesz vector is therefore the orthogonal projection of the ambient
gap-plus-tail kernel at the same radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open scoped InnerProductSpace

noncomputable section

local instance radiusCompletedMellinCarrierComplete (radius : ℝ) :
    CompleteSpace (EvenBurnolPhysicalCarrier radius) := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace radius).isClosed.isComplete

def burnolRadiusCompletedMellinEvaluator
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    EvenBurnolPhysicalCarrier radius →L[ℂ] ℂ :=
  burnolRadiusMellinGapMoment radius coordinate.value •
      burnolConstantGapCoefficient radius +
    (burnolRadiusMellinTailEvaluator radius positive
      coordinate.value coordinate.rightHalf).comp
        (Submodule.subtypeL (evenBurnolClosedFace radius).toSubmodule)

def burnolRadiusCompletedMellinRieszVector
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    EvenBurnolPhysicalCarrier radius :=
  (InnerProductSpace.toDual ℂ
    (EvenBurnolPhysicalCarrier radius)).symm
      (burnolRadiusCompletedMellinEvaluator radius positive coordinate)

theorem burnolRadiusCompletedMellinRieszVector_readback
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius) :
    inner ℂ (burnolRadiusCompletedMellinRieszVector
        radius positive coordinate) value =
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value := by
  exact InnerProductSpace.toDual_symm_apply

def burnolAmbientGapCoefficient (radius : ℝ) : BurnolL2 →L[ℂ] ℂ :=
  ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹) •
    ((innerSL ℂ (intervalConstant radius)).comp
      (restrictToInterval radius))

def burnolAmbientGapRieszVector (radius : ℝ) : BurnolL2 :=
  star ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹) •
    (restrictToInterval radius).adjoint (intervalConstant radius)

theorem burnolAmbientGapRieszVector_readback
    (radius : ℝ) (value : BurnolL2) :
    inner ℂ (burnolAmbientGapRieszVector radius) value =
      burnolAmbientGapCoefficient radius value := by
  unfold burnolAmbientGapRieszVector burnolAmbientGapCoefficient
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_star]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem burnolAmbientGapCoefficient_restrict (radius : ℝ) :
    (burnolAmbientGapCoefficient radius).comp
        (Submodule.subtypeL
          (evenBurnolClosedFace radius).toSubmodule) =
      burnolConstantGapCoefficient radius := by
  rfl

def burnolRadiusAmbientCompletedMellinEvaluator
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  burnolRadiusMellinGapMoment radius coordinate.value •
      burnolAmbientGapCoefficient radius +
    burnolRadiusMellinTailEvaluator radius positive
      coordinate.value coordinate.rightHalf

theorem burnolRadiusAmbientCompletedMellinEvaluator_restrict
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolRadiusAmbientCompletedMellinEvaluator
        radius positive coordinate).comp
        (Submodule.subtypeL
          (evenBurnolClosedFace radius).toSubmodule) =
      burnolRadiusCompletedMellinEvaluator radius positive coordinate := by
  unfold burnolRadiusAmbientCompletedMellinEvaluator
    burnolRadiusCompletedMellinEvaluator
  ext value
  simp [burnolAmbientGapCoefficient_restrict]

def burnolRadiusAmbientCompletedMellinRieszVector
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (InnerProductSpace.toDual ℂ BurnolL2).symm
    (burnolRadiusAmbientCompletedMellinEvaluator radius positive coordinate)

def burnolRadiusAmbientCompletedMellinKernelFormula
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  star (burnolRadiusMellinGapMoment radius coordinate.value) •
      burnolAmbientGapRieszVector radius +
    burnolRadiusMellinTailKernelL2 radius positive
      coordinate.value coordinate.rightHalf

theorem burnolRadiusAmbientCompletedMellinRieszVector_readback
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (burnolRadiusAmbientCompletedMellinRieszVector
        radius positive coordinate) value =
      burnolRadiusAmbientCompletedMellinEvaluator
        radius positive coordinate value := by
  exact InnerProductSpace.toDual_symm_apply

theorem burnolRadiusAmbientCompletedMellinRieszVector_eq_kernelFormula
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusAmbientCompletedMellinRieszVector radius positive coordinate =
      burnolRadiusAmbientCompletedMellinKernelFormula
        radius positive coordinate := by
  apply ext_inner_right ℂ
  intro value
  rw [burnolRadiusAmbientCompletedMellinRieszVector_readback]
  unfold burnolRadiusAmbientCompletedMellinEvaluator
    burnolRadiusAmbientCompletedMellinKernelFormula
  simp only [add_apply, smul_apply, smul_eq_mul, inner_add_left,
    inner_smul_left, starRingEnd_apply, star_star]
  rw [burnolAmbientGapRieszVector_readback]
  change _ = _ + burnolRadiusMellinTailEvaluator
    radius positive coordinate.value coordinate.rightHalf value
  rfl

theorem burnolRadiusCompletedMellinRieszVector_eq_ambientProjection
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusCompletedMellinRieszVector radius positive coordinate =
      (evenBurnolClosedFace radius).toSubmodule.orthogonalProjectionOnto
        (burnolRadiusAmbientCompletedMellinRieszVector
          radius positive coordinate) := by
  apply ext_inner_right ℂ
  intro value
  rw [burnolRadiusCompletedMellinRieszVector_readback]
  have restriction := congrArg
    (fun functional : EvenBurnolPhysicalCarrier radius →L[ℂ] ℂ =>
      functional value)
    (burnolRadiusAmbientCompletedMellinEvaluator_restrict
      radius positive coordinate)
  rw [← restriction]
  change burnolRadiusAmbientCompletedMellinEvaluator radius positive coordinate
      (value : BurnolL2) = _
  rw [← burnolRadiusAmbientCompletedMellinRieszVector_readback]
  exact (((evenBurnolClosedFace radius).toSubmodule
    ).inner_orthogonalProjectionOnto_eq_of_mem_right
      value
      (burnolRadiusAmbientCompletedMellinRieszVector
        radius positive coordinate)).symm

theorem burnolRadiusCompletedMellinEvaluator_riesz_eq_norm_sq
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusCompletedMellinEvaluator radius positive coordinate
        (burnolRadiusCompletedMellinRieszVector radius positive coordinate) =
      (‖burnolRadiusCompletedMellinRieszVector
        radius positive coordinate‖ : ℂ) ^ 2 := by
  rw [← burnolRadiusCompletedMellinRieszVector_readback]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
    (burnolRadiusCompletedMellinRieszVector radius positive coordinate)

theorem burnolRadiusCompletedMellinEvaluator_ne_zero_iff_ambientProjection_ne_zero
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusCompletedMellinEvaluator radius positive coordinate ≠ 0 ↔
      ((evenBurnolClosedFace radius).toSubmodule.orthogonalProjectionOnto
        (burnolRadiusAmbientCompletedMellinKernelFormula
          radius positive coordinate)) ≠ 0 := by
  rw [← burnolRadiusAmbientCompletedMellinRieszVector_eq_kernelFormula,
    ← burnolRadiusCompletedMellinRieszVector_eq_ambientProjection]
  constructor
  · intro evaluatorNe projectionZero
    apply evaluatorNe
    apply ContinuousLinearMap.ext
    intro value
    rw [← burnolRadiusCompletedMellinRieszVector_readback, projectionZero]
    simp
  · intro projectionNe evaluatorZero
    apply projectionNe
    apply ext_inner_right ℂ
    intro value
    rw [burnolRadiusCompletedMellinRieszVector_readback, evaluatorZero]
    simp

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

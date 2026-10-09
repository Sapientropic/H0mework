import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter FourierTransform MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

theorem quarter_fourier_pairing_of_reflection (left right : BurnolQuarterIntervalL2)
    (rightEven : reflectRestricted q right = right) :
    inner ℂ (burnolTruncatedFourier left) right =
      inner ℂ left (burnolTruncatedFourier right) := by
  have reflected : reflectL2 (burnolQuarterZeroExtension right) =
      burnolQuarterZeroExtension right := by
    change reflectL2 (burnolRadiusZeroExtension q right) = _
    rw [burnolRadiusZeroExtension_reflect, rightEven]
    rfl
  have unitary := fourierL2.inner_map_map (burnolQuarterZeroExtension left)
    (fourierL2 (burnolQuarterZeroExtension right))
  rw [fourierL2_fourierL2, reflected] at unitary
  calc
    _ = inner ℂ (fourierL2 (burnolQuarterZeroExtension left))
        (burnolQuarterZeroExtension right) := by
      exact (ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction
        (fourierL2 (burnolQuarterZeroExtension left)) right).symm
    _ = inner ℂ (burnolQuarterZeroExtension left)
        (fourierL2 (burnolQuarterZeroExtension right)) := unitary
    _ = _ := ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction
      (fourierL2 (burnolQuarterZeroExtension right)) left

theorem meanZero_fourier_pairing_of_reflection
    (left right : BurnolQuarterMeanZeroCarrier)
    (rightEven : reflectRestricted q (right : BurnolQuarterIntervalL2) = right) :
    inner ℂ (burnolMeanZeroTruncatedFourier left) right =
      inner ℂ left (burnolMeanZeroTruncatedFourier right) := by
  unfold burnolMeanZeroTruncatedFourier
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact quarter_fourier_pairing_of_reflection _ _ rightEven

private theorem phase_inner (frequency : ℝ) (state : BurnolQuarterIntervalL2) :
    inner ℂ (Constructor.compact (Constructor.phase frequency)
      (Constructor.phaseContinuous frequency)) state =
        Constructor.fourierRaw state (-frequency) := by
  rw [L2.inner_def]
  unfold Constructor.fourierRaw VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards [Constructor.compact_read (Constructor.phase frequency)
    (Constructor.phaseContinuous frequency)] with x read
  rw [read]
  simp [Constructor.phase, RCLike.inner_apply, innerₗ_apply_apply,
    Circle.smul_def, mul_comm]

private theorem constant_inner (state : BurnolQuarterIntervalL2) :
    inner ℂ (intervalConstant q) state =
      (1 / 2 : ℂ) * burnolQuarterMeanCoefficient state := by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow, burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num
  ring

theorem eta_source_read (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ Response.eta (burnolRieszSingleFourierSource coordinate) =
      (1 / 2 : ℂ) * burnolRieszReturnRaw coordinate q := by
  let b := burnolRieszSingleFourierSource coordinate
  let mean := burnolQuarterMeanCoefficient (burnolTruncatedFourier (b : BurnolQuarterIntervalL2))
  have plus : Constructor.fourierRaw (b : BurnolQuarterIntervalL2) q =
      burnolRieszReturnRaw coordinate q + mean := by
    change _ = (Constructor.fourierRaw (b : BurnolQuarterIntervalL2) q - mean) + mean
    ring
  have minus : Constructor.fourierRaw (b : BurnolQuarterIntervalL2) (-q) =
      burnolRieszReturnRaw coordinate q + mean := by
    have endpoints := burnolRieszSingleFourierReturnRaw_endpoints coordinate
    change Constructor.fourierRaw (b : BurnolQuarterIntervalL2) (-q) - mean =
      Constructor.fourierRaw (b : BurnolQuarterIntervalL2) q - mean at endpoints
    linear_combination endpoints + plus
  have constant : inner ℂ (burnolTruncatedFourier (intervalConstant q))
      (b : BurnolQuarterIntervalL2) = (1 / 2 : ℂ) * mean := by
    rw [quarter_fourier_pairing_of_reflection _ _
      (burnolRieszSingleFourierSource_reflection_fixed coordinate), constant_inner]
  unfold Response.eta Constructor.endpointColumn
  rw [inner_add_left]
  simp only [Constructor.zeroMean,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    inner_sub_left, inner_smul_left]
  rw [phase_inner, phase_inner, neg_neg, plus, minus, constant]
  norm_num [map_ofNat]
  ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

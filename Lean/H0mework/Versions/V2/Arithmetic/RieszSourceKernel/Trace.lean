import H0mework.Versions.V2.Arithmetic.RieszEuler.Scalar
import H0mework.Versions.V2.Arithmetic.RieszForcing.SourceParity
import H0mework.Versions.V2.Arithmetic.RieszGreen.RawDerivative
import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.BoundaryTracePosition
import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.FourierKernel

/-! The generated source coefficients are the two actual jumps of the original physical Riesz state. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Kernel

open Complex MeasureTheory Set
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def A (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  star coordinate.value * GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate q

def beta (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolRieszSingleFourierSourceRaw coordinate q

theorem position_jump (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszStatePositiveOuterRaw coordinate q - burnolRieszStateQuarterInnerRaw coordinate = -A coordinate := by
  have mean : star (burnolRadiusMellinGapMoment q coordinate.value) *
      star ((‖intervalConstant q‖ ^ 2 : ℂ)⁻¹) = GapEuler.gapMean q coordinate := by
    rw [burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
    norm_num [GapEuler.gapMean]
  rw [burnolRieszState_quarter_outer_sub_inner, mean,
    burnolRieszSingleFourierReturnRaw_endpoints]
  have source := GapEuler.gapMean_primitive q (by norm_num) coordinate
  unfold A burnolRieszReturnRaw
  linear_combination -source

theorem fourier_jump (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszFourierExteriorRaw coordinate q -
      (burnolQuarterMeanCoefficient (burnolQuarterRestriction
          (burnolAmbientEvenPart (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate)))) +
        burnolQuarterMeanCoefficient (burnolTruncatedFourier
          (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2))) =
      beta coordinate := by
  have inside : q ∈ symmetricInterval q := by norm_num [symmetricInterval]
  have negative : -q ∈ symmetricInterval q := by norm_num [symmetricInterval]
  rw [← burnolRieszFourierRaw_gap_read coordinate inside]
  calc
    _ = burnolEvenRaw ((symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate)) q := by
      unfold burnolRieszFourierRaw
      ring
    _ = beta coordinate := by
      unfold burnolEvenRaw beta
      rw [indicator_of_mem inside, indicator_of_mem negative, burnolRieszSingleFourierSourceRaw_endpoints]
      ring

end
end OriginalRieszSource.Kernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

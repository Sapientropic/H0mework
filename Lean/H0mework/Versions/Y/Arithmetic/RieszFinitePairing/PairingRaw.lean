import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Trace

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Classical Complex MeasureTheory Set
open OriginalRieszSource

noncomputable section
local notation "q" => (1 / 4 : ℝ)

def positionMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolRieszStateQuarterInnerRaw coordinate

def fourierMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction
    (burnolAmbientEvenPart (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate)))) +
      burnolQuarterMeanCoefficient (burnolTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2))

def positionTail (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x -
    star (burnolRadiusMellinGapMoment q coordinate.value) *
      star ((‖intervalConstant q‖ ^ 2 : ℂ)⁻¹) -
        burnolEvenRaw (burnolRieszReturnRaw coordinate) x

def fourierTail (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolEvenRaw (burnolRieszSingleFourierSourceRaw coordinate) x

private theorem negative_outside {x : ℝ} (outside : x ∉ symmetricInterval q) :
    -x ∉ symmetricInterval q := by
  intro negative
  apply outside
  simp only [symmetricInterval, mem_Icc] at negative ⊢
  constructor <;> linarith [negative.1, negative.2]

theorem position_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszStateRaw coordinate x = positionMean coordinate +
      if x ∈ symmetricInterval q then 0 else positionTail coordinate x := by
  by_cases inside : x ∈ symmetricInterval q
  · rw [if_pos inside, add_zero]
    exact burnolRieszStateRaw_eq_quarterInner_of_mem coordinate inside
  rw [if_neg inside]
  have negative := negative_outside inside
  unfold burnolRieszStateRaw burnolRieszCorrectionRaw positionTail positionMean
    burnolRieszStateQuarterInnerRaw burnolRieszReturnRaw burnolEvenRaw burnolMeanZeroFourierRaw
  simp only [indicator_of_notMem inside, indicator_of_notMem negative]
  ring

theorem fourier_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszFourierRaw coordinate x = fourierMean coordinate +
      if x ∈ symmetricInterval q then 0 else fourierTail coordinate x := by
  by_cases inside : x ∈ symmetricInterval q
  · rw [if_pos inside, add_zero]
    exact burnolRieszFourierRaw_gap_read coordinate inside
  rw [if_neg inside]
  have negative := negative_outside inside
  unfold burnolRieszFourierRaw burnolRieszFourierExteriorRaw fourierMean fourierTail
    burnolEvenRaw burnolRieszSingleFourierSourceRaw burnolRieszFourierForcingRaw
    burnolPositionMeanZeroRaw burnolMeanZeroRaw burnolMeanZeroFourierRaw
  simp only [burnolEvenRaw, indicator_of_notMem inside, indicator_of_notMem negative, neg_neg]
  ring

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

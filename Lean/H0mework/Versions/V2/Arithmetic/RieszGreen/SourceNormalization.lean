import H0mework.Versions.V2.Arithmetic.RieszGreen.SourcePairing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem secondReturn_endpoints (coordinate : BurnolCompletedMellinCoordinate) :
    Constructor.secondReturnRaw coordinate (-q) = Constructor.secondReturnRaw coordinate q := by
  have actual := burnolRieszSingleFourierSourceRaw_endpoints coordinate
  change burnolRieszFourierForcingRaw coordinate (-q) + Constructor.secondReturnRaw coordinate (-q) =
    burnolRieszFourierForcingRaw coordinate q + Constructor.secondReturnRaw coordinate q at actual
  rw [Translator.ForcingMeanZero.forcingRaw_eq, Translator.ForcingMeanZero.forcingRaw_eq,
    Translator.ForcingWhole.raw_even] at actual
  exact add_left_cancel actual

theorem secondEuler_mean (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (Constructor.secondEulerAmbient coordinate) =
      Constructor.secondReturnRaw coordinate q := by
  have actual := Euler.smoothEuler_mean
    (burnolMeanZeroTruncatedFourier (Constructor.returnState coordinate))
    (Constructor.secondReturnRaw coordinate)
    (Constructor.fourierDerivative (burnolRieszReturnRaw coordinate))
    (Constructor.secondReturnRaw_read coordinate) (Constructor.secondReturnRaw_continuous coordinate)
    (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous coordinate))
    (Constructor.secondReturnRaw_hasDerivAt coordinate)
  change burnolQuarterMeanCoefficient (Constructor.secondEulerAmbient coordinate) =
    (Constructor.secondReturnRaw coordinate q + Constructor.secondReturnRaw coordinate (-q)) / 2 at actual
  rw [secondReturn_endpoints] at actual
  linear_combination actual

/-- The full raw weighted derivative retains the original forcing mean. -/
theorem weightedRaw_eq (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    weightedRaw coordinate x =
      (star coordinate.value - 1 / 2) * Translator.ForcingWhole.raw coordinate x +
        (star coordinate.value * GapEuler.gapMean q coordinate) * Edge.raw q x +
          Constructor.secondEulerRaw coordinate x -
            (1 / 2 : ℂ) * Translator.ForcingMeanZero.mean coordinate := by
  have beta : Kernel.beta coordinate =
      burnolRieszFourierForcingRaw coordinate q + Constructor.secondReturnRaw coordinate q := rfl
  unfold weightedRaw centeredRaw
  rw [secondEuler_mean, beta, Translator.ForcingMeanZero.forcing_mean_boundary,
    Translator.ForcingMeanZero.forcingRaw_eq]
  unfold Translator.ForcingWhole.coefficient
  ring

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

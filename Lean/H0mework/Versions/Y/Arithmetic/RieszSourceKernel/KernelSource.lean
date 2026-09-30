import H0mework.Versions.Y.Arithmetic.RieszForcing.SourceParity
import H0mework.Versions.Y.Arithmetic.RieszEuler.GapEulerFourier

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Kernel

open Complex
noncomputable section

theorem original_kernel_reconstruction (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate) +
      burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2) -
      fourierL2 (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  let source := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let returned := burnolQuarterZeroExtension
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
      BurnolQuarterIntervalL2)
  have sourceFixed : reflectL2 source = source := by
    change reflectL2 (burnolRadiusZeroExtension (1 / 4 : ℝ)
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have returnFixed : reflectL2 returned = returned := by
    change reflectL2 (burnolRadiusZeroExtension (1 / 4 : ℝ)
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
        BurnolQuarterIntervalL2)) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierReturn_reflection_fixed]
    rfl
  have fourierFixed : reflectL2 (fourierL2 source) = fourierL2 source := by
    rw [← fourierL2_reflectL2_commute, sourceFixed]
  have wholeFixed : burnolAmbientEvenPart (returned - fourierL2 source) =
      returned - fourierL2 source := by
    unfold burnolAmbientEvenPart
    rw [map_sub, returnFixed, fourierFixed]
    module
  have native := burnolCompletedMellinRieszVector_eq_singleFourierSource coordinate
  change (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
    burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate) +
      burnolAmbientEvenPart (returned - fourierL2 source) at native
  rw [wholeFixed] at native
  exact native.trans (by change _ = _ + returned - fourierL2 source; module)

end
end OriginalRieszSource.Kernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

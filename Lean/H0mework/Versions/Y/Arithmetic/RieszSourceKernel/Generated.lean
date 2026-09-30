import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.KernelEquation
import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Trace
import H0mework.Versions.Y.Arithmetic.RieszEuler.Solve
import H0mework.Versions.Y.Arithmetic.RieszEuler.Return

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Kernel

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem original_kernel_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      (star coordinate.value - 1 / 2) •
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      A coordinate • Response.Psi + beta coordinate • 𝓕 Response.Psi := by
  let extension : BurnolQuarterMeanZeroCarrier →L[ℂ] TemperedDistribution ℝ ℂ :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).comp
      (burnolQuarterZeroExtension.comp
        (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))
  have sourceValue := congrArg extension (Euler.sourceEuler_eq coordinate)
  simp only [map_add, map_sub, map_smul] at sourceValue
  change extension (Euler.sourceEuler coordinate) =
    (star coordinate.value - 1 / 2) •
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) +
    A coordinate • (Response.wholeU : TemperedDistribution ℝ ℂ) -
      beta coordinate • (Response.wholeV : TemperedDistribution ℝ ℂ) at sourceValue
  have sourceLaw := Euler.source_euler coordinate
  change GapEuler.euler (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) =
    extension (Euler.sourceEuler coordinate) - beta coordinate • GapEuler.edge q at sourceLaw
  rw [sourceValue] at sourceLaw
  have returnValue := congrArg extension (Euler.returnEuler_eq coordinate)
  simp only [map_add, map_sub, map_smul] at returnValue
  change extension (Constructor.returnEuler coordinate) =
    -(star coordinate.value - 1 / 2) •
      (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
    A coordinate • (Response.wholeV : TemperedDistribution ℝ ℂ) +
      beta coordinate • (Response.wholeU : TemperedDistribution ℝ ℂ) at returnValue
  have returnLaw := Euler.return_euler coordinate
  change GapEuler.euler (burnolQuarterZeroExtension
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
        BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) =
    extension (Constructor.returnEuler coordinate) -
      burnolRieszReturnRaw coordinate q • GapEuler.edge q at returnLaw
  rw [returnValue] at returnLaw
  exact euler_from_source_laws coordinate sourceLaw returnLaw

end
end OriginalRieszSource.Kernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.KernelSource
import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.ResponseProfile
import H0mework.Versions.V2.Arithmetic.RieszEuler.Forcing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Kernel

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
noncomputable section

local notation "q" => (1 / 4 : ℝ)

/- This assembly consumes local generated Euler laws; it is not their producer. -/
theorem euler_from_source_laws (coordinate : BurnolCompletedMellinCoordinate)
    (sourceLaw :
      GapEuler.euler (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) =
      (star coordinate.value - 1 / 2) • (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) +
      (star coordinate.value * GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate q) •
        (Response.wholeU : TemperedDistribution ℝ ℂ) -
      burnolRieszSingleFourierSourceRaw coordinate q • (Response.wholeV : TemperedDistribution ℝ ℂ) -
      burnolRieszSingleFourierSourceRaw coordinate q • GapEuler.edge q)
    (returnLaw :
      GapEuler.euler (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) =
      -(star coordinate.value - 1 / 2) • (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
      (star coordinate.value * GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate q) •
        (Response.wholeV : TemperedDistribution ℝ ℂ) +
      burnolRieszSingleFourierSourceRaw coordinate q • (Response.wholeU : TemperedDistribution ℝ ℂ) -
      burnolRieszReturnRaw coordinate q • GapEuler.edge q) :
    GapEuler.euler (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      (star coordinate.value - 1 / 2) •
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
    (star coordinate.value * GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate q) •
      Response.Psi + burnolRieszSingleFourierSourceRaw coordinate q • 𝓕 Response.Psi := by
  let original := burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)
  let source := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let returned := burnolQuarterZeroExtension
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2)
  have read : (burnolCompletedMellinRieszVector coordinate : BurnolL2) = original + returned - fourierL2 source :=
    original_kernel_reconstruction coordinate
  have material := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) read
  rw [map_sub, map_add] at material
  change (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
    (original : TemperedDistribution ℝ ℂ) + (returned : TemperedDistribution ℝ ℂ) -
      (fourierL2 source : TemperedDistribution ℝ ℂ) at material
  have transformed : 𝓕 (source : TemperedDistribution ℝ ℂ) =
      (fourierL2 source : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq source
  rw [← transformed] at material
  have originalLaw := GapEuler.even_gapTail_euler q (by norm_num) coordinate
  change GapEuler.euler (original : TemperedDistribution ℝ ℂ) +
    (star coordinate.value - 1 / 2) • (original : TemperedDistribution ℝ ℂ) =
      (-star coordinate.value * GapEuler.gapMean q coordinate) • GapEuler.edge q at originalLaw
  change GapEuler.euler (source : TemperedDistribution ℝ ℂ) = _ at sourceLaw
  change GapEuler.euler (returned : TemperedDistribution ℝ ℂ) = _ at returnLaw
  rw [material, map_sub, map_add, GapEuler.euler_fourier, sourceLaw, returnLaw,
    Response.Psi_fourier]
  rw [show GapEuler.euler (original : TemperedDistribution ℝ ℂ) =
    (-star coordinate.value * GapEuler.gapMean q coordinate) • GapEuler.edge q -
      (star coordinate.value - 1 / 2) • (original : TemperedDistribution ℝ ℂ)
      from eq_sub_of_add_eq originalLaw]
  unfold Response.Psi
  simp only [sub_eq_add_neg, FourierTransform.fourier_neg,
    FourierAdd.fourier_add, FourierSMul.fourier_smul]
  dsimp only [source, returned]
  module

end
end OriginalRieszSource.Kernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

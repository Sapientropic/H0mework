import H0mework.Versions.V2.Arithmetic.RieszGreen.KernelGram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex
open OriginalRieszSource
noncomputable section

def kernelSelfSource (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  (star (Kernel.A coordinate) * Kernel.A coordinate -
    star (Kernel.beta coordinate) * Kernel.beta coordinate) /
      (2 * (coordinate.value + star coordinate.value - 1))

/-- The original evaluator consumes the already generated whole-K Gram in its native scalar field. -/
theorem original_kernel_self_source (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) = kernelSelfSource coordinate := by
  have nonzero : (2 : ℂ) * (coordinate.value + star coordinate.value - 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (OriginalRieszSourceGreen.source_cross_parameter_ne_zero coordinate coordinate)
  unfold kernelSelfSource
  apply (eq_div_iff nonzero).mpr
  linear_combination 2 * OriginalRieszSourceGreen.original_kernel_gram coordinate coordinate

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.RieszGreen.Assemble
import H0mework.Versions.V2.Arithmetic.RieszGreen.ReturnGreen
import H0mework.Versions.V2.Arithmetic.RieszGreen.SourceIntegral

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex
open OriginalRieszSource

noncomputable section

/-- Both actual interval equations generate the complete original source Green form. -/
theorem original_source_green (left right : BurnolCompletedMellinCoordinate) :
    (left.value + star right.value - 1) *
        (inner ℂ (burnolRieszSingleFourierSource left) (burnolRieszSingleFourierSource right) -
          inner ℂ (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource left))
            (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource right))) =
      (1 / 2 : ℂ) *
        (star (Kernel.beta left) * Kernel.beta right - star (Kernel.A left) * Kernel.A right +
          star (star left.value * GapEuler.gapMean (1 / 4) left) *
            (star right.value * GapEuler.gapMean (1 / 4) right)) :=
  source_green_from_green left right (source_interval_green left right) (return_green left right)

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.RieszForcing.ForcingCutoffPairing
import H0mework.Versions.V2.Arithmetic.RieszForcing.Interval

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.ForcingCutoff

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology InnerProductSpace
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

theorem original_forcing_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler
        (burnolQuarterZeroExtension
          (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) :
            BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) =
      (star coordinate.value - 1 / 2) •
        (burnolQuarterZeroExtension
          (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) :
            BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      ForcingWhole.coefficient coordinate •
        (burnolQuarterZeroExtension (ForcingMeanZero.eta : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) -
      burnolRieszFourierForcingRaw coordinate q • GapEuler.edge q := by
  ext test
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  rw [euler_zeroExtension_pairing _ _ (burnolRieszFourierForcing_ae_raw coordinate),
    zeroExtension_pairing _ _ (burnolRieszFourierForcing_ae_raw coordinate),
    zeroExtension_pairing _ _ ForcingMeanZero.eta_read, edge_pairing]
  have source := forcing_scalar_equation coordinate test
  linear_combination -source

end
end OriginalRieszSource.Translator.ForcingCutoff
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

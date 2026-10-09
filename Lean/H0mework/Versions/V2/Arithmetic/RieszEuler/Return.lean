import H0mework.Versions.V2.Arithmetic.SonineProjection.Return
import H0mework.Versions.V2.Arithmetic.RieszEuler.Extension
import H0mework.Versions.V2.Arithmetic.RieszForcing.SourceParity

/-! The actual smooth returns generate their zero-extension Euler distributions. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler

open Complex Filter MeasureTheory Set Constructor
open scoped ENNReal SchwartzMap Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

private theorem raw_endpoints (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw) (continuous : Continuous raw)
    (fixed : reflectRestricted q state = state) : raw (-q) = raw q := by
  let reflection := negMeasurePreserving_restrict q
  have reflected : (fun x : ℝ => raw (-x)) =ᵐ[μq] raw := by
    filter_upwards [Lp.coeFn_compMeasurePreserving state reflection,
      reflection.quasiMeasurePreserving.ae read, read] with x negative negativeRead direct
    change reflectRestricted q state x = state (-x) at negative
    rw [fixed] at negative
    exact negativeRead.symm.trans (negative.symm.trans direct)
  exact Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
    (by norm_num : -q ≠ q) reflected
    (continuous.comp continuous_neg).continuousOn continuous.continuousOn (by norm_num)

theorem return_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler
      (burnolQuarterZeroExtension (returnState coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (returnEuler coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) - burnolRieszReturnRaw coordinate q • GapEuler.edge q := by
  exact even_extension_euler (returnState coordinate : BurnolQuarterIntervalL2)
    (burnolRieszReturnRaw coordinate) (burnolRieszReturnRawDerivative coordinate)
    (returnState_read coordinate) (burnolRieszReturnRaw_continuous coordinate)
    (burnolRieszReturnRawDerivative_continuous coordinate) (burnolRieszReturnRaw_hasDerivAt coordinate)
    (returnEulerAmbient_mean coordinate) (burnolRieszSingleFourierReturnRaw_endpoints coordinate)

theorem secondReturn_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler
      (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (returnState coordinate) : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (secondEuler coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) - secondReturnRaw coordinate q • GapEuler.edge q := by
  have firstFixed : sourceMeanZeroReflection (returnState coordinate) = returnState coordinate := by
    apply Subtype.ext
    exact burnolRieszSingleFourierReturn_reflection_fixed coordinate
  have reflected := sourceMeanZeroFourier_reflect (returnState coordinate)
  rw [firstFixed] at reflected
  have fixed := congrArg (fun state : BurnolQuarterMeanZeroCarrier =>
    (state : BurnolQuarterIntervalL2)) reflected.symm
  have endpoints := raw_endpoints _ (secondReturnRaw coordinate)
    (secondReturnRaw_read coordinate) (secondReturnRaw_continuous coordinate) fixed
  have derivativeContinuous := fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous coordinate)
  exact even_extension_euler _ (secondReturnRaw coordinate)
    (fourierDerivative (burnolRieszReturnRaw coordinate)) (secondReturnRaw_read coordinate)
    (secondReturnRaw_continuous coordinate) derivativeContinuous (secondReturnRaw_hasDerivAt coordinate)
    (smoothEuler_mean _ _ _ (secondReturnRaw_read coordinate) (secondReturnRaw_continuous coordinate)
      derivativeContinuous (secondReturnRaw_hasDerivAt coordinate)) endpoints

end
end OriginalRieszSource.Euler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

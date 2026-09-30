import H0mework.Versions.Y.Arithmetic.RieszEuler.Return
import H0mework.Versions.Y.Arithmetic.RieszForcing.ForcingCutoff
import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Core
import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Trace

/-! The original source equation generates its whole Euler value and the actual endpoint mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler

open Complex Filter MeasureTheory Constructor
open scoped ENNReal Topology
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

def sourceEuler (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  (star coordinate.value - 1 / 2) •
      burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) +
    (star coordinate.value * GapEuler.gapMean q coordinate) • Response.eta + secondEuler coordinate

theorem sourceEuler_def (coordinate : BurnolCompletedMellinCoordinate) :
    sourceEuler coordinate =
      (star coordinate.value - 1 / 2) •
          burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) +
        (star coordinate.value * GapEuler.gapMean q coordinate) • Response.eta + secondEuler coordinate := rfl

theorem source_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (sourceEuler coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) - Kernel.beta coordinate • GapEuler.edge q := by
  have equation := burnolRieszSingleFourierSource_equation coordinate
  change burnolRieszSingleFourierSource coordinate -
    burnolMeanZeroTruncatedFourier (returnState coordinate) =
      burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) at equation
  have split := congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : BurnolQuarterIntervalL2))
    (sub_eq_iff_eq_add.mp equation)
  have whole :
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension
        (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) :
          BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier (returnState coordinate) : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) := by
    rw [split]
    change Lp.toTemperedDistributionCLM ℂ volume 2 (burnolQuarterZeroExtension (_ + _)) = _
    rw [map_add, map_add]
    rfl
  have combination :
      (burnolQuarterZeroExtension (sourceEuler coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) =
      (star coordinate.value - 1 / 2) •
        (burnolQuarterZeroExtension
          (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) :
            BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      (star coordinate.value * GapEuler.gapMean q coordinate) •
        (burnolQuarterZeroExtension (Response.eta : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      (burnolQuarterZeroExtension (secondEuler coordinate : BurnolQuarterIntervalL2) :
        TemperedDistribution ℝ ℂ) := by
    change Lp.toTemperedDistributionCLM ℂ volume 2
      (burnolQuarterZeroExtension ((_ • _ + _ • _) + _)) = _
    simp only [map_add, map_smul]
    rfl
  have endpoint : Kernel.beta coordinate =
      burnolRieszFourierForcingRaw coordinate q + secondReturnRaw coordinate q := rfl
  rw [whole, map_add, Translator.ForcingCutoff.original_forcing_euler, secondReturn_euler,
    combination, endpoint]
  change (_ + (star coordinate.value * GapEuler.gapMean q coordinate) •
      (burnolQuarterZeroExtension (Response.eta : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) - _) + _ = _
  module

theorem sourceEuler_read (coordinate : BurnolCompletedMellinCoordinate) :
    ((sourceEuler coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq]
      fun x : ℝ =>
        (star coordinate.value - 1 / 2) * burnolRieszFourierForcingRaw coordinate x +
        (star coordinate.value * GapEuler.gapMean q coordinate) *
          (Edge.raw q x - Translator.ForcingMeanZero.edgeMean) +
        (secondEulerRaw coordinate x - burnolQuarterMeanCoefficient (secondEulerAmbient coordinate)) := by
  let forcing : BurnolQuarterIntervalL2 :=
    burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)
  let left : BurnolQuarterIntervalL2 := (star coordinate.value - 1 / 2) • forcing
  let column : BurnolQuarterIntervalL2 :=
    (star coordinate.value * GapEuler.gapMean q coordinate) • (Response.eta : BurnolQuarterIntervalL2)
  have secondRead := burnolMeanZeroProjection_ae_raw (secondEulerAmbient coordinate)
    (secondEulerRaw coordinate) (compact_read _ (secondEulerRaw_continuous coordinate))
  change ((secondEuler coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq]
    (fun x : ℝ => secondEulerRaw coordinate x -
      burnolQuarterMeanCoefficient (secondEulerAmbient coordinate)) at secondRead
  have actual : (sourceEuler coordinate : BurnolQuarterIntervalL2) =
      (left + column) + (secondEuler coordinate : BurnolQuarterIntervalL2) := rfl
  rw [actual]
  filter_upwards [Lp.coeFn_add (left + column) (secondEuler coordinate : BurnolQuarterIntervalL2),
    Lp.coeFn_add left column,
    Lp.coeFn_smul (star coordinate.value - 1 / 2) forcing,
    Lp.coeFn_smul (star coordinate.value * GapEuler.gapMean q coordinate)
      (Response.eta : BurnolQuarterIntervalL2),
    burnolRieszFourierForcing_ae_raw coordinate, Translator.ForcingMeanZero.eta_read, secondRead]
    with x total sum forcingScale columnScale forcingRead columnRead returned
  change left x = _ at forcingScale
  change column x = _ at columnScale
  change forcing x = _ at forcingRead
  change (Response.eta : BurnolQuarterIntervalL2) x = _ at columnRead
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at total sum forcingScale columnScale
  rw [total, sum, forcingScale, columnScale, forcingRead, columnRead, returned]

end
end OriginalRieszSource.Euler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

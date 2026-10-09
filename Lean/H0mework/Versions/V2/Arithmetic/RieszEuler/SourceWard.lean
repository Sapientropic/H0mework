import H0mework.Versions.V2.Arithmetic.RieszEuler.SourceKernel
import H0mework.Versions.V2.Arithmetic.RieszEuler.EulerSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler

open Complex Filter MeasureTheory
open Constructor
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem source_meanZero_ward (coordinate : BurnolCompletedMellinCoordinate)
    (db : BurnolQuarterMeanZeroCarrier)
    (weakSource : GapEuler.euler (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (db : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
        Kernel.beta coordinate • GapEuler.edge q) :
    returnEuler coordinate + burnolMeanZeroTruncatedFourier db = Kernel.beta coordinate • Response.eta := by
  let nativeFourier := burnolRadiusTruncatedFourierRaw q (db : BurnolQuarterIntervalL2)
  let mean := burnolQuarterMeanCoefficient (burnolTruncatedFourier
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) / 2
  let lhs : ℝ → ℂ := returnEulerRaw coordinate + nativeFourier
  let rhs : ℝ → ℂ := Kernel.beta coordinate • Edge.raw q - mean • (fun _ : ℝ => (1 : ℂ))
  have lhsContinuous : Continuous lhs :=
    (returnEulerRaw_continuous coordinate).add (burnolRadiusTruncatedFourierRaw_continuous _)
  have rhsContinuous : Continuous rhs :=
    ((Edge.raw_continuous q).const_smul (Kernel.beta coordinate)).sub (continuous_const.const_smul mean)
  have same : lhs = rhs := by
    funext x
    have generated := source_kernel_ward coordinate db weakSource x
    dsimp only [lhs, rhs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
      returnEulerRaw, nativeFourier, mean]
    unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw
    linear_combination generated
  have states : compact lhs lhsContinuous = compact rhs rhsContinuous :=
    ((continuous_memLp lhs lhsContinuous).toLp_eq_toLp_iff
      (continuous_memLp rhs rhsContinuous)).mpr (Filter.EventuallyEq.of_eq same)
  rw [compact_add (returnEulerRaw coordinate) nativeFourier (returnEulerRaw_continuous coordinate)
    (burnolRadiusTruncatedFourierRaw_continuous _)] at states
  have native : compact nativeFourier (burnolRadiusTruncatedFourierRaw_continuous
      (db : BurnolQuarterIntervalL2)) = burnolTruncatedFourier (db : BurnolQuarterIntervalL2) :=
    Edge.compact_truncatedFourier _
  rw [native] at states
  rw [compact_sub (Kernel.beta coordinate • Edge.raw q) (mean • (fun _ : ℝ => (1 : ℂ)))
    ((Edge.raw_continuous q).const_smul (Kernel.beta coordinate)) (continuous_const.const_smul mean),
    compact_smul (Kernel.beta coordinate) (Edge.raw q) (Edge.raw_continuous q),
    compact_smul mean (fun _ : ℝ => (1 : ℂ)) continuous_const, compact_one] at states
  have normalized := congrArg zeroMean states
  simp only [map_add, map_sub, map_smul, zeroMean_constant, smul_zero, sub_zero] at normalized
  rw [Edge.zeroMean_raw_eq_endpointColumns] at normalized
  exact normalized

theorem original_source_meanZero_ward (coordinate : BurnolCompletedMellinCoordinate) :
    returnEuler coordinate + burnolMeanZeroTruncatedFourier (sourceEuler coordinate) =
      Kernel.beta coordinate • Response.eta :=
  source_meanZero_ward coordinate (sourceEuler coordinate) (source_euler coordinate)

end
end OriginalRieszSource.Euler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

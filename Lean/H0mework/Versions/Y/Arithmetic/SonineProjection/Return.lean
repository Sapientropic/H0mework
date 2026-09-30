import H0mework.Versions.Y.Arithmetic.SonineProjection.ConstructorCompact

/-! The original smooth return generates its own compact mean-zero Euler value. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Constructor

open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

def returnState (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)

theorem returnState_read (coordinate : BurnolCompletedMellinCoordinate) :
    ((returnState coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq]
      burnolRieszReturnRaw coordinate :=
  burnolMeanZeroFourier_ae_raw (burnolRieszSingleFourierSource coordinate)

theorem return_integral_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in (-q)..q, burnolRieszReturnRaw coordinate x) = 0 := by
  have generated := mean_zero (returnState coordinate)
  rw [mean_integral] at generated
  have raw := integral_congr_ae (returnState_read coordinate)
  rw [raw] at generated
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  exact (mul_eq_zero.mp generated).resolve_left (by norm_num)

def returnEulerRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ) * burnolRieszReturnRawDerivative coordinate x + (1 / 2 : ℂ) * burnolRieszReturnRaw coordinate x

theorem returnEulerRaw_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (returnEulerRaw coordinate) := by
  have actual := burnolRieszReturnRaw_continuous coordinate
  have derivative := burnolRieszReturnRawDerivative_continuous coordinate
  unfold returnEulerRaw
  fun_prop

def returnEulerAmbient (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  compact (returnEulerRaw coordinate) (returnEulerRaw_continuous coordinate)

def returnEuler (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  zeroMean (returnEulerAmbient coordinate)

theorem returnEulerAmbient_mean (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (returnEulerAmbient coordinate) =
      (burnolRieszReturnRaw coordinate q + burnolRieszReturnRaw coordinate (-q)) / 2 := by
  rw [returnEulerAmbient, mean_compact]
  have source := return_kernel_ward coordinate 0
  simp only [phase, zero_mul, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, Complex.ofReal_zero,
    mul_zero, sub_zero] at source
  have split : returnEulerRaw coordinate = fun x : ℝ =>
      (burnolRieszReturnRaw coordinate x + (x : ℂ) * burnolRieszReturnRawDerivative coordinate x) -
        (1 / 2 : ℂ) * burnolRieszReturnRaw coordinate x := by
    funext x
    unfold returnEulerRaw
    ring
  have bulkContinuous : Continuous (fun x : ℝ =>
      burnolRieszReturnRaw coordinate x + (x : ℂ) * burnolRieszReturnRawDerivative coordinate x) := by
    have actual := burnolRieszReturnRaw_continuous coordinate
    have derivative := burnolRieszReturnRawDerivative_continuous coordinate
    fun_prop
  rw [split, intervalIntegral.integral_sub (bulkContinuous.intervalIntegrable (-q) q)
    (((burnolRieszReturnRaw_continuous coordinate).const_mul (1 / 2 : ℂ)).intervalIntegrable (-q) q),
    intervalIntegral.integral_const_mul, return_integral_zero, mul_zero, sub_zero, source]
  norm_num
  ring

def secondReturnRaw (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolMeanZeroFourierRaw (returnState coordinate)

theorem secondReturnRaw_eq_fourier (coordinate : BurnolCompletedMellinCoordinate) :
    secondReturnRaw coordinate = fun x =>
      fourierRaw (burnolRieszReturnRaw coordinate) x -
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (returnState coordinate : BurnolQuarterIntervalL2)) := by
  have source := fourierRaw_congr _ _ (returnState_read coordinate)
  rw [fourierRaw_state] at source
  funext x
  unfold secondReturnRaw burnolMeanZeroFourierRaw
  rw [congrFun source x]

theorem secondReturnRaw_read (coordinate : BurnolCompletedMellinCoordinate) :
    ((burnolMeanZeroTruncatedFourier (returnState coordinate) : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq]
      secondReturnRaw coordinate := burnolMeanZeroFourier_ae_raw _

theorem secondReturnRaw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    HasDerivAt (secondReturnRaw coordinate)
      (fourierDerivative (burnolRieszReturnRaw coordinate) x) x := by
  rw [secondReturnRaw_eq_fourier]
  exact (fourierRaw_hasDerivAt _ (burnolRieszReturnRaw_continuous coordinate) x).sub_const _

theorem secondReturnRaw_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (secondReturnRaw coordinate) :=
  continuous_iff_continuousAt.mpr fun x => (secondReturnRaw_hasDerivAt coordinate x).continuousAt

def secondEulerRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ) * fourierDerivative (burnolRieszReturnRaw coordinate) x + (1 / 2 : ℂ) * secondReturnRaw coordinate x

theorem secondEulerRaw_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (secondEulerRaw coordinate) := by
  have derivative := fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous coordinate)
  have returned := secondReturnRaw_continuous coordinate
  unfold secondEulerRaw
  fun_prop

def secondEulerAmbient (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  compact (secondEulerRaw coordinate) (secondEulerRaw_continuous coordinate)

def secondEuler (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  zeroMean (secondEulerAmbient coordinate)

end
end OriginalRieszSource.Constructor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.SonineProjection.Return

/-! The actual `S b` and `S(S b)` consume the complete mean-zero endpoint Ward law. -/

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

def endpointColumn (endpoint : ℝ) : BurnolQuarterMeanZeroCarrier :=
  zeroMean ((q : ℂ) • compact (phase endpoint) (phaseContinuous endpoint) -
    (1 / 2 : ℂ) • burnolTruncatedFourier (intervalConstant q))

private theorem return_ward_fourier (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    (frequency : ℂ) * fourierDerivative (burnolRieszReturnRaw coordinate) frequency +
      (1 / 2 : ℂ) * fourierRaw (burnolRieszReturnRaw coordinate) frequency +
        fourierRaw (returnEulerRaw coordinate) frequency =
      (q : ℂ) * (phase frequency q * burnolRieszReturnRaw coordinate q +
        phase frequency (-q) * burnolRieszReturnRaw coordinate (-q)) := by
  let moment := fun x : ℝ => phase frequency x *
    (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * burnolRieszReturnRaw coordinate x)
  let returned := fun x : ℝ => phase frequency x * burnolRieszReturnRaw coordinate x
  let euler := fun x : ℝ => phase frequency x * returnEulerRaw coordinate x
  have momentContinuous : Continuous moment := by
    have kernel := phaseContinuous frequency
    have source := burnolRieszReturnRaw_continuous coordinate
    dsimp only [moment]
    fun_prop
  have returnedContinuous : Continuous returned :=
    (phaseContinuous frequency).mul (burnolRieszReturnRaw_continuous coordinate)
  have eulerContinuous : Continuous euler :=
    (phaseContinuous frequency).mul (returnEulerRaw_continuous coordinate)
  rw [fourierDerivative_integral _ (burnolRieszReturnRaw_continuous coordinate),
    fourierRaw_integral, fourierRaw_integral]
  change (frequency : ℂ) * (∫ x : ℝ in (-q)..q, moment x) +
    (1 / 2 : ℂ) * (∫ x : ℝ in (-q)..q, returned x) +
      (∫ x : ℝ in (-q)..q, euler x) = _
  calc
    _ = ∫ x : ℝ in (-q)..q,
        ((frequency : ℂ) * moment x + (1 / 2 : ℂ) * returned x) + euler x := by
      rw [intervalIntegral.integral_add
        (f := fun x => (frequency : ℂ) * moment x + (1 / 2 : ℂ) * returned x) (g := euler)
        (((momentContinuous.const_mul (frequency : ℂ)).add
          (returnedContinuous.const_mul (1 / 2 : ℂ))).intervalIntegrable (-q) q)
        (eulerContinuous.intervalIntegrable (-q) q),
        intervalIntegral.integral_add (f := fun x => (frequency : ℂ) * moment x)
          (g := fun x => (1 / 2 : ℂ) * returned x) ((momentContinuous.const_mul (frequency : ℂ)).intervalIntegrable (-q) q)
          ((returnedContinuous.const_mul (1 / 2 : ℂ)).intervalIntegrable (-q) q),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = ∫ x : ℝ in (-q)..q,
        phase frequency x *
          ((1 - 2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ) * (x : ℂ)) *
              burnolRieszReturnRaw coordinate x +
            (x : ℂ) * burnolRieszReturnRawDerivative coordinate x) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [moment, returned, euler, returnEulerRaw]
      ring
    _ = _ := return_kernel_ward coordinate frequency

/-- The actual full-frequency Ward value before quarter restriction and mean-zero projection. -/
theorem return_ward_fourier_source (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    (frequency : ℂ) * fourierDerivative (burnolRieszReturnRaw coordinate) frequency +
      (1 / 2 : ℂ) * fourierRaw (burnolRieszReturnRaw coordinate) frequency +
        fourierRaw (returnEulerRaw coordinate) frequency =
      (q : ℂ) * (phase frequency q * burnolRieszReturnRaw coordinate q +
        phase frequency (-q) * burnolRieszReturnRaw coordinate (-q)) :=
  return_ward_fourier coordinate frequency

private theorem return_ward_ambient (coordinate : BurnolCompletedMellinCoordinate) :
    secondEulerAmbient coordinate + burnolTruncatedFourier (returnEulerAmbient coordinate) =
      (burnolRieszReturnRaw coordinate q * (q : ℂ)) • compact (phase q) (phaseContinuous q) +
        (burnolRieszReturnRaw coordinate (-q) * (q : ℂ)) • compact (phase (-q)) (phaseContinuous (-q)) -
          (burnolQuarterMeanCoefficient (burnolTruncatedFourier
            (returnState coordinate : BurnolQuarterIntervalL2)) / 2) • intervalConstant q := by
  let mean := burnolQuarterMeanCoefficient
    (burnolTruncatedFourier (returnState coordinate : BurnolQuarterIntervalL2))
  let rhs := (burnolRieszReturnRaw coordinate q * (q : ℂ)) • phase q +
    (burnolRieszReturnRaw coordinate (-q) * (q : ℂ)) • phase (-q) -
      (mean / 2) • (fun _ : ℝ => (1 : ℂ))
  have rhsContinuous : Continuous rhs := by
    have plus := phaseContinuous q
    have minus := phaseContinuous (-q)
    dsimp only [rhs]
    fun_prop
  have actual : secondEulerRaw coordinate + fourierRaw (returnEulerRaw coordinate) = rhs := by
    funext x
    have ward := return_ward_fourier coordinate x
    have second := congrFun (secondReturnRaw_eq_fourier coordinate) x
    dsimp only [Pi.add_apply, secondEulerRaw, rhs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [second, phase_symm q x, phase_symm (-q) x]
    dsimp only [mean]
    linear_combination ward
  have same := (continuous_memLp _
      ((secondEulerRaw_continuous coordinate).add
        (fourierRaw_continuous _ (returnEulerRaw_continuous coordinate)))).toLp_eq_toLp_iff
      (continuous_memLp rhs rhsContinuous)
  have equalStates : compact _ ((secondEulerRaw_continuous coordinate).add
        (fourierRaw_continuous _ (returnEulerRaw_continuous coordinate))) = compact rhs rhsContinuous :=
    same.mpr (Filter.EventuallyEq.of_eq actual)
  have fourierState : compact (fourierRaw (returnEulerRaw coordinate))
      (fourierRaw_continuous _ (returnEulerRaw_continuous coordinate)) =
        burnolTruncatedFourier (returnEulerAmbient coordinate) := by
    have source := fourierRaw_congr _ _ (compact_read _ (returnEulerRaw_continuous coordinate))
    apply Lp.ext
    filter_upwards [compact_read (fourierRaw (returnEulerRaw coordinate))
      (fourierRaw_continuous _ (returnEulerRaw_continuous coordinate)),
      truncatedFourier_read (returnEulerAmbient coordinate)] with x left right
    rw [left, right]
    exact (congrFun source x).symm
  rw [compact_add (secondEulerRaw coordinate) (fourierRaw (returnEulerRaw coordinate))
    (secondEulerRaw_continuous coordinate) (fourierRaw_continuous _ (returnEulerRaw_continuous coordinate)),
    fourierState] at equalStates
  refine equalStates.trans ?_
  let plus := compact (phase q) (phaseContinuous q)
  let minus := compact (phase (-q)) (phaseContinuous (-q))
  let a := burnolRieszReturnRaw coordinate q * (q : ℂ)
  let b := burnolRieszReturnRaw coordinate (-q) * (q : ℂ)
  let d := mean / 2
  change compact rhs rhsContinuous = a • plus + b • minus - d • intervalConstant q
  apply Lp.ext
  filter_upwards [compact_read rhs rhsContinuous,
    Lp.coeFn_sub (a • plus + b • minus) (d • intervalConstant q),
    Lp.coeFn_add (a • plus) (b • minus),
    Lp.coeFn_smul a plus, Lp.coeFn_smul b minus, Lp.coeFn_smul d (intervalConstant q),
    compact_read (phase q) (phaseContinuous q), compact_read (phase (-q)) (phaseContinuous (-q)),
    intervalConstant_coeFn q] with x whole subRead addRead plusRead minusRead constantRead plusRaw minusRaw constant
  rw [whole, subRead]
  change rhs x = (a • plus + b • minus : BurnolQuarterIntervalL2) x - (d • intervalConstant q : BurnolQuarterIntervalL2) x
  rw [addRead]
  change rhs x = (a • plus : BurnolQuarterIntervalL2) x + (b • minus : BurnolQuarterIntervalL2) x - _
  rw [plusRead, minusRead, constantRead]
  change rhs x = a * plus x + b * minus x - d * intervalConstant q x
  rw [plusRaw, minusRaw, constant, mul_one]
  simp only [rhs, a, b, d, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]

theorem return_meanZero_ward (coordinate : BurnolCompletedMellinCoordinate) :
    secondEuler coordinate + burnolMeanZeroTruncatedFourier (returnEuler coordinate) =
      burnolRieszReturnRaw coordinate q • endpointColumn q +
        burnolRieszReturnRaw coordinate (-q) • endpointColumn (-q) := by
  have full := congrArg zeroMean (return_ward_ambient coordinate)
  simp only [map_add, map_sub, map_smul, zeroMean_constant, smul_zero, sub_zero] at full
  have returned : burnolMeanZeroTruncatedFourier (returnEuler coordinate) =
      zeroMean (burnolTruncatedFourier (returnEulerAmbient coordinate)) -
        burnolQuarterMeanCoefficient (returnEulerAmbient coordinate) •
          zeroMean (burnolTruncatedFourier (intervalConstant q)) := by
    change zeroMean (burnolTruncatedFourier (returnEuler coordinate : BurnolQuarterIntervalL2)) = _
    rw [show (returnEuler coordinate : BurnolQuarterIntervalL2) =
      returnEulerAmbient coordinate - burnolQuarterMeanCoefficient (returnEulerAmbient coordinate) • intervalConstant q
      from zeroMean_read _, map_sub, map_smul, map_sub, map_smul]
  rw [returned, returnEulerAmbient_mean]
  change secondEuler coordinate + _ = _ at full
  unfold endpointColumn
  simp only [map_sub, map_smul]
  rw [show secondEuler coordinate =
      (burnolRieszReturnRaw coordinate q * (q : ℂ)) • zeroMean (compact (phase q) (phaseContinuous q)) +
      (burnolRieszReturnRaw coordinate (-q) * (q : ℂ)) • zeroMean (compact (phase (-q)) (phaseContinuous (-q))) -
      zeroMean (burnolTruncatedFourier (returnEulerAmbient coordinate)) from eq_sub_of_add_eq full]
  module

end
end OriginalRieszSource.Constructor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

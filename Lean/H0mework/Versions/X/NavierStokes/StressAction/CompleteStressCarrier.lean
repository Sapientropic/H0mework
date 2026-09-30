import H0mework.Versions.X.NavierStokes.MomentumAction.NegativeFourMomentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeCompleteStressCarrier

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientNativeFluidMedium ThreeDimensionalIntegerLatticeCriticalKernel
open NativeFullOrderStress NativeTimeJetCarrier

noncomputable section

abbrev Tensor := EuclideanSpace ℂ (Coordinate × Coordinate)
abbrev Space := lp (fun _ : IntegerWavevector => Tensor) 2

/-- The zero mode is retained; it carries the original stress trace. -/
def weight (wave : IntegerWavevector) : ℝ := if wave = 0 then 1 else (integerWaveNormSq wave)⁻¹

theorem weight_pos (wave : IntegerWavevector) : 0 < weight wave := by
  by_cases zero : wave = 0
  · simp [weight, zero]
  · simpa [weight, zero] using inv_pos.mpr (integerWaveNormSq_pos zero)

theorem weight_sq (wave : IntegerWavevector) :
    weight wave ^ 2 = (if wave = 0 then 1 else 0) + integerWaveCriticalKernel wave := by
  by_cases zero : wave = 0
  · simp [weight, zero, integerWaveCriticalKernel, integerWaveNormSq]
  · simp [weight, zero, integerWaveCriticalKernel]

theorem weight_summable : Summable (fun wave => weight wave ^ 2) := by
  simp_rw [weight_sq]
  exact (hasSum_ite_eq 0 1).summable.add summable_integerWaveCriticalKernel

def tensor (value : NativeFluidStressCoefficient) : Tensor := WithLp.toLp 2 (fun pair => value pair.1 pair.2)

def untensor (value : Tensor) : NativeFluidStressCoefficient := fun output input => value (output, input)

theorem tensor_norm_sq (value : NativeFluidStressCoefficient) :
    ‖tensor value‖ ^ 2 = ∑ output : Coordinate, ∑ input : Coordinate, ‖value output input‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_prod_type _

private theorem tensor_bound {value : NativeFluidStressCoefficient} {budget : ℝ}
    (bounded : ∀ output input, ‖value output input‖ ≤ budget) :
    ‖tensor value‖ ^ 2 ≤ 9 * budget ^ 2 := by
  rw [tensor_norm_sq]
  have sumBound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
      pow_le_pow_left₀ (norm_nonneg _) (bounded output input) 2
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, ← mul_assoc, show (3 : ℝ) * 3 = 9 by norm_num] using sumBound

private theorem weighted_bound {stress : NativeFluidStressFourierState} {budget : ℝ}
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) (wave : IntegerWavevector) :
    ‖weight wave • tensor (stress wave)‖ ^ 2 ≤ 9 * budget ^ 2 * weight wave ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul_of_nonneg_left (tensor_bound (bounded wave)) (sq_nonneg _)).trans_eq (by ring)

/-- Complete tensor coefficients of the given source stress, including frequency zero. -/
def ofBound (stress : NativeFluidStressFourierState) (budget : ℝ)
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) : Space :=
  ⟨fun wave => weight wave • tensor (stress wave), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact (weight_summable.mul_left (9 * budget ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) (weighted_bound bounded)⟩

theorem ofBound_norm_sq (stress : NativeFluidStressFourierState) (budget : ℝ)
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) :
    ‖ofBound stress budget bounded‖ ^ 2 ≤ 9 * budget ^ 2 * ∑' wave, weight wave ^ 2 := by
  have actual := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (ofBound stress budget bounded)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at actual
  rw [actual, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (weighted_bound bounded)
    ((weight_summable.mul_left _).of_nonneg_of_le (fun _ => sq_nonneg _) (weighted_bound bounded))
    (weight_summable.mul_left _)

def read (value : Space) : NativeFluidStressFourierState :=
  fun wave output input => (weight wave)⁻¹ • value wave (output, input)

theorem read_ofBound (stress : NativeFluidStressFourierState) (budget : ℝ)
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) :
    read (ofBound stress budget bounded) = stress := by
  funext wave output input
  change (weight wave)⁻¹ • (weight wave • stress wave output input) = _
  rw [inv_smul_smul₀ (weight_pos wave).ne']

theorem read_injective : Function.Injective read := by
  intro first last same
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro pair
  have actual := congrFun (congrFun (congrFun same wave) pair.1) pair.2
  have scaled := congrArg (fun value : ℂ => weight wave • value) actual
  simpa only [read, smul_inv_smul₀ (weight_pos wave).ne'] using scaled

def readCLM (wave : IntegerWavevector) (output input : Coordinate) : Space →L[ℝ] ℂ :=
  (weight wave)⁻¹ •
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate × Coordinate => ℂ)).toContinuousLinearMap
      |>.comp (lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave)
      |> (ContinuousLinearMap.proj (output, input)).comp)

theorem readCLM_apply (value : Space) (wave : IntegerWavevector) (output input : Coordinate) :
    readCLM wave output input value = read value wave output input := rfl

end
end SaturationMonoid.NavierStokes.NativeCompleteStressCarrier

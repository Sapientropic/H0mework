import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Carrier
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Source

set_option autoImplicit false
open scoped BigOperators ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticPositive
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeEndpointVelocityCarrier
open NativeUnheatedHalfNonlinear NativeUnheatedQuarticEnvelope NativeUnheatedPairNegativeKernel
noncomputable section

theorem row_square_bound (value : wholePhysical) (wave : IntegerWavevector) :
    (quarter wave*NativeUnheatedQuarticEnvelope.row value wave)^2 ≤
      (9*(2*Real.pi))*(Real.sqrt (1+integerWaveNormSq wave)*NativeUnheatedQuarticEnvelope.row value wave^2) := by
  rw [mul_pow, quarter_sq]
  have paid := mul_le_mul_of_nonneg_right (root_bound wave) (sq_nonneg (NativeUnheatedQuarticEnvelope.row value wave))
  have positive : 0 ≤ (2*Real.pi)*Real.sqrt (1+integerWaveNormSq wave)*NativeUnheatedQuarticEnvelope.row value wave^2 := by positivity
  nlinarith

theorem square_summable (value : wholePhysical) (regular : H1 value) :
    Summable (fun wave => (quarter wave*NativeUnheatedQuarticEnvelope.row value wave)^2) :=
  ((NativeUnheatedQuarticHalfEnvelope.square_summable value regular).mul_left (9*(2*Real.pi))).of_nonneg_of_le
    (fun _ => sq_nonneg _) (row_square_bound value)

def envelope (value : wholePhysical) (regular : H1 value) : NativeFullOrderAction.ScalarL2 :=
  ⟨fun wave => quarter wave*NativeUnheatedQuarticEnvelope.row value wave, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using square_summable value regular)⟩

theorem envelope_apply (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    envelope value regular wave = quarter wave*NativeUnheatedQuarticEnvelope.row value wave := rfl

theorem envelope_nonnegative (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    0 ≤ envelope value regular wave := mul_nonneg (quarter_nonnegative wave) (row_nonnegative value wave)

theorem envelope_bound (value : wholePhysical) (regular : H1 value) :
    ‖envelope value regular‖ ≤ coefficient*gradientMass value := by
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg coefficient_nonnegative mass0)).mp
  have identity := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (envelope value regular)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at identity
  rw [identity]
  have paid := Summable.tsum_le_tsum (row_square_bound value) (square_summable value regular)
    ((NativeUnheatedQuarticHalfEnvelope.square_summable value regular).mul_left (9*(2*Real.pi)))
  rw [tsum_mul_left] at paid
  apply paid.trans
  have full := mul_le_mul_of_nonneg_left (NativeUnheatedQuarticHalfEnvelope.mass_bound value regular)
    (by positivity : (0 : ℝ) ≤ 9*(2*Real.pi))
  unfold coefficient
  rw [mul_pow, Real.sq_sqrt (by positivity [NativeUnheatedRieszKernel.constant_nonnegative])]
  exact full.trans_eq (by ring)

def input (value : wholePhysical) (regular : H1 value) (leaf position : Fin 4) : NativeUnheatedTriadSum.E :=
  if position=leaf then NativeUnheatedQuarticSource.scalarLift (envelope value regular) else wholeVelocity value.1

theorem input_product (value : wholePhysical) (regular : H1 value) (leaf : Fin 4) :
    ‖input value regular leaf 0‖*‖input value regular leaf 1‖*‖input value regular leaf 2‖*‖input value regular leaf 3‖ ≤
      coefficient*gradientMass value*‖wholeVelocity value.1‖^3 := by
  have paid := mul_le_mul_of_nonneg_right (envelope_bound value regular) (pow_nonneg (norm_nonneg (wholeVelocity value.1)) 3)
  fin_cases leaf <;> simpa [input, Fin.ext_iff, NativeUnheatedQuarticSource.scalarLift_norm,
    pow_succ, mul_assoc, mul_comm, mul_left_comm] using paid

theorem pressure_bound (kernel : ℂ) (wave : IntegerWavevector) (i j response : Coordinate) :
    ‖kernel*NativeUnheatedTriadChannels.pressure wave i j response‖ ≤
      ‖kernel*(quarter wave : ℂ)‖*quarter wave := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (quarter_nonnegative wave)]
  calc
    _ ≤ ‖kernel‖*root wave := mul_le_mul_of_nonneg_left (NativeUnheatedTriadChannels.pressure_bound wave i j response) (norm_nonneg _)
    _ = _ := by rw [← quarter_sq]; ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticPositive

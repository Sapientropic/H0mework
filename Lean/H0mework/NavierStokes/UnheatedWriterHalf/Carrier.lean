import H0mework.NavierStokes.UnheatedWriterQuartic.HalfEnvelope
import H0mework.NavierStokes.UnheatedWriterTriad.CubicRows

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedHalfNonlinear
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeResolventCompactness NativeWholeResolvent NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing
open NativeUnheatedPairNegativeKernel NativeUnheatedQuarticEnvelope NativeHigherTimeJets NativeTimeJetCarrier
noncomputable section

def quarter (wave : IntegerWavevector) : ℝ := Real.sqrt (root wave)
theorem quarter_nonnegative (wave : IntegerWavevector) : 0 ≤ quarter wave := Real.sqrt_nonneg _
theorem quarter_sq (wave : IntegerWavevector) : quarter wave^2 = root wave := Real.sq_sqrt (root_nonnegative wave)

theorem flux_row_bound (value : wholePhysical) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖mixedFlux (wholeVelocity value.1) (wholeVelocity value.1) wave output input‖ ≤ NativeUnheatedQuarticEnvelope.row value wave := by
  rw [mixedFlux, norm_neg]
  have pairs := mixed_pair_summable (wholeVelocity value.1) (wholeVelocity value.1) wave output input
  apply (norm_tsum_le_tsum_norm pairs.norm).trans
  apply pairs.norm.tsum_le_tsum _ (pair_summable value wave)
  intro first
  rw [norm_mul]
  have a := NativeUnheatedPairInverseFlux.coordinate_bound (wholeVelocity value.1) first input
  have b := NativeUnheatedPairInverseFlux.coordinate_bound (wholeVelocity value.1) (wave-first) output
  rw [← amplitude_original] at a b
  exact mul_le_mul a b (norm_nonneg _) (by exact norm_nonneg _)

theorem action_row_square (value : wholePhysical) (wave : Wave) :
    ‖euclideanCoordinateRow (NativeWholeH1Mixed.row value value wave.1)‖^2 ≤
      9*integerWaveViscousMultiplier wave.1*NativeUnheatedQuarticEnvelope.row value wave.1^2 := by
  let stress := mixedFlux (wholeVelocity value.1) (wholeVelocity value.1)
  have tensorBound : (∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (stress wave.1 output input)) ≤
      9*NativeUnheatedQuarticEnvelope.row value wave.1^2 := by
    have entries := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
        pow_le_pow_left₀ (norm_nonneg _) (flux_row_bound value wave.1 output input) 2
    simpa only [Complex.normSq_eq_norm_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, show (3 : ℝ)*3 = 9 by norm_num] using entries
  have divergence := NativeFullOrderStress.divergence_amplitude_le stress wave.1
  have projected := transverseProjection_amplitudeSq_le wave.1 wave.2 (nativeFluidStressDivergenceCoefficient stress wave.1)
  rw [euclideanCoordinateRow_norm_sq]
  exact (projected.trans divergence).trans ((mul_le_mul_of_nonneg_left tensorBound (multiplier_positive wave).le).trans_eq (by ring))

theorem root_bound (wave : IntegerWavevector) : root wave ≤ (2*Real.pi)*Real.sqrt (1+integerWaveNormSq wave) := by
  rw [root, integerWaveViscousMultiplier, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity)

theorem row_square_bound (value : wholePhysical) (regular : H1 value) (wave : Wave) :
    ‖quarter wave.1 • negativeAction value value regular regular wave‖^2 ≤
      (9*(2*Real.pi))*(Real.sqrt (1+integerWaveNormSq wave.1)*NativeUnheatedQuarticEnvelope.row value wave.1^2) := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, quarter_sq]
  change root wave.1*‖negativeRow value value wave‖^2 ≤ _
  rw [negative_row_sq, negativeDensity]
  have paid := mul_le_mul_of_nonneg_left (action_row_square value wave)
    (mul_nonneg (root_nonnegative wave.1) (inv_nonneg.mpr (multiplier_positive wave).le))
  have cancelled : root wave.1*((integerWaveViscousMultiplier wave.1)⁻¹*
      ‖euclideanCoordinateRow (NativeWholeH1Mixed.row value value wave.1)‖^2) ≤
        9*root wave.1*NativeUnheatedQuarticEnvelope.row value wave.1^2 := by
    convert! paid using 1
    · ring
    · field_simp [(multiplier_positive wave).ne']
  exact cancelled.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (root_bound wave.1) (by norm_num : (0 : ℝ) ≤ 9))
    (sq_nonneg _)).trans_eq (by ring))

theorem row_square_summable (value : wholePhysical) (regular : H1 value) :
    Summable (fun wave : Wave => ‖quarter wave.1 • negativeAction value value regular regular wave‖^2) := by
  have paid := (NativeUnheatedQuarticHalfEnvelope.square_summable value regular).subtype (fun wave => wave ≠ 0)
  exact (paid.mul_left (9*(2*Real.pi))).of_nonneg_of_le (fun _ => sq_nonneg _) (row_square_bound value regular)

def ofPhysical (value : wholePhysical) (regular : H1 value) : State :=
  ⟨fun wave => quarter wave.1 • negativeAction value value regular regular wave, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using row_square_summable value regular)⟩

def coefficient : ℝ := Real.sqrt (9*(2*Real.pi)*NativeUnheatedRieszKernel.constant)
theorem coefficient_nonnegative : 0 ≤ coefficient := Real.sqrt_nonneg _

theorem ofPhysical_bound (value : wholePhysical) (regular : H1 value) :
    ‖ofPhysical value regular‖ ≤ coefficient*gradientMass value := by
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg coefficient_nonnegative mass0)).mp
  rw [NativeResolventCompactness.norm_sq_sum]
  have major := (NativeUnheatedQuarticHalfEnvelope.square_summable value regular).subtype (fun wave => wave ≠ 0)
  have paid := Summable.tsum_le_tsum (row_square_bound value regular) (row_square_summable value regular) (major.mul_left (9*(2*Real.pi)))
  rw [tsum_mul_left] at paid
  have complete := Summable.tsum_subtype_le
    (fun wave => Real.sqrt (1+integerWaveNormSq wave)*NativeUnheatedQuarticEnvelope.row value wave^2) (fun wave => wave ≠ 0)
    (fun _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (NativeUnheatedQuarticHalfEnvelope.square_summable value regular)
  have total := paid.trans (mul_le_mul_of_nonneg_left (complete.trans (NativeUnheatedQuarticHalfEnvelope.mass_bound value regular))
    (by positivity : (0 : ℝ) ≤ 9*(2*Real.pi)))
  unfold coefficient
  rw [mul_pow, Real.sq_sqrt (by positivity [NativeUnheatedRieszKernel.constant_nonnegative])]
  exact total.trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedHalfNonlinear

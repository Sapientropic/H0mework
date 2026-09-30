import H0mework.NavierStokes.UnheatedWriterPair.WindowTail


set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairWindowTail

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeUnheatedPairInverseKernel NativeUnheatedPairInverseFlux NativeForwardWindowJets NativeHigherTimeJets

noncomputable section
variable {nu : Viscosity}

theorem moment_bound (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    (weight wave)⁻¹ ^ spatialOrder * ‖tail seed timeOrder (spatialOrder + 2) time wave output input‖ ≤
      budget seed timeOrder (spatialOrder + 2) * weight wave ^ 2 := by
  have paid := mul_le_mul_of_nonneg_left (tail_bound seed timeOrder (spatialOrder + 2) time wave output input)
    (pow_nonneg (inv_nonneg.mpr (weight_pos wave).le) spatialOrder)
  apply paid.trans_eq
  rw [pow_add]
  have cancel : (weight wave)⁻¹ ^ spatialOrder * weight wave ^ spatialOrder = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (weight_pos wave).ne', one_pow]
  calc
    _ = ((weight wave)⁻¹ ^ spatialOrder * weight wave ^ spatialOrder) *
        (budget seed timeOrder (spatialOrder + 2) * weight wave ^ 2) := by ring
    _ = _ := by rw [cancel, one_mul]

theorem moment_summable (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) (output input : Coordinate) :
    Summable (fun wave => (weight wave)⁻¹ ^ spatialOrder *
      ‖tail seed timeOrder (spatialOrder + 2) time wave output input‖) :=
  (weight_summable.mul_left (budget seed timeOrder (spatialOrder + 2))).of_nonneg_of_le
    (fun wave => mul_nonneg (pow_nonneg (inv_nonneg.mpr (weight_pos wave).le) spatialOrder) (norm_nonneg _))
    (fun wave => moment_bound seed timeOrder spatialOrder time wave output input)

def wholeMomentRow (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate,
    (weight wave)⁻¹ ^ spatialOrder * ‖tail seed timeOrder (spatialOrder + 2) time wave output input‖

theorem wholeMomentRow_nonnegative (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) : 0 ≤ wholeMomentRow seed timeOrder spatialOrder time wave := by
  unfold wholeMomentRow
  positivity [weight_pos wave]

theorem wholeMomentRow_bound (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) :
    wholeMomentRow seed timeOrder spatialOrder time wave ≤
      9 * budget seed timeOrder (spatialOrder + 2) * weight wave ^ 2 := by
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun output _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun input _ =>
      moment_bound seed timeOrder spatialOrder time wave output input))
  simpa only [wholeMomentRow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, ← mul_assoc, show (3 : ℝ) * 3 = 9 by norm_num] using paid

theorem whole_moment_summable (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) : Summable (wholeMomentRow seed timeOrder spatialOrder time) :=
  (weight_summable.mul_left (9 * budget seed timeOrder (spatialOrder + 2))).of_nonneg_of_le
    (wholeMomentRow_nonnegative seed timeOrder spatialOrder time)
    (wholeMomentRow_bound seed timeOrder spatialOrder time)

theorem whole_moment_bound (seed : GeneratedWholeRestartCurrent nu) (timeOrder spatialOrder : ℕ)
    (time : ℝ) :
    (∑' wave, wholeMomentRow seed timeOrder spatialOrder time wave) ≤
      9 * budget seed timeOrder (spatialOrder + 2) * ∑' wave, weight wave ^ 2 := by
  rw [← tsum_mul_left]
  exact (whole_moment_summable seed timeOrder spatialOrder time).tsum_le_tsum
    (wholeMomentRow_bound seed timeOrder spatialOrder time)
    (weight_summable.mul_left (9 * budget seed timeOrder (spatialOrder + 2)))

theorem weight_le_one (wave : IntegerWavevector) : weight wave ≤ 1 := by
  by_cases zero : wave = 0
  · simp only [weight, if_pos zero, le_rfl]
  · simpa only [weight, if_neg zero] using inv_le_one_of_one_le₀ (one_le_integerWaveNormSq wave zero)

theorem uniform_bound (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖tail seed timeOrder inverseOrder time wave output input‖ ≤ budget seed timeOrder inverseOrder :=
  (tail_bound seed timeOrder inverseOrder time wave output input).trans
    (mul_le_of_le_one_right (budget_nonnegative seed timeOrder inverseOrder)
      (pow_le_one₀ (weight_pos wave).le (weight_le_one wave)))

def carrier (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ) (time : ℝ) : Space :=
  ofBound (tail seed timeOrder inverseOrder time) (budget seed timeOrder inverseOrder)
    (uniform_bound seed timeOrder inverseOrder time)

theorem carrier_read (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ) (time : ℝ) :
    read (carrier seed timeOrder inverseOrder time) = tail seed timeOrder inverseOrder time :=
  read_ofBound _ _ _

theorem tail_zero (seed : GeneratedWholeRestartCurrent nu) (timeOrder : ℕ) (time : ℝ) :
    tail seed timeOrder 0 time = read (jet seed timeOrder time).snd := by
  funext wave output input
  let view : FullSpace →L[ℝ] ℂ := (readCLM wave output input).comp
    (WithLp.sndL 2 ℝ _ Space)
  have integrable : Integrable (fun shift : ℝ => kernelJet timeOrder shift •
      NativeUnifiedCompleteSource.source seed (time - shift)) :=
    (kernelJet_compact timeOrder).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernelJet_smooth timeOrder).continuous (NativeForwardWindowSource.original_locallyIntegrable seed) time
  change (∫ shift : ℝ, kernelJet timeOrder shift • raw seed 0 wave output input (time - shift)) =
    view (∫ shift : ℝ, kernelJet timeOrder shift • NativeUnifiedCompleteSource.source seed (time - shift))
  rw [← view.integral_comp_comm integrable]
  apply integral_congr_ae
  have original := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    (NativeUnifiedGlobalStressSource.stress_ae seed)
  filter_upwards [original] with shift same
  rw [map_smul]
  congr 1
  change coefficient nu 0 (velocity seed (time - shift)) (velocity seed (time - shift)) wave output input =
    read (NativeUnifiedCompleteSource.source seed (time - shift)).snd wave output input
  rw [coefficient_zero, velocity, NativeUnifiedCompleteSource.velocity_read, mixedFlux_diagonal,
    NativeUnifiedCompleteSource.stress_read, same]

theorem carrier_zero (seed : GeneratedWholeRestartCurrent nu) (timeOrder : ℕ) (time : ℝ) :
    carrier seed timeOrder 0 time = (jet seed timeOrder time).snd := by
  apply read_injective
  rw [carrier_read, tail_zero]

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairWindowTail

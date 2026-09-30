import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.CubicIdentity
import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.GlobalIntegral

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedCubicCarrier
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing
open NativeUnheatedSourceGradient NativeUnheatedPairGlobalEvolution NativeUnheatedCubicIdentity
open NativeUnheatedPairNegativeKernel NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity}

def coefficient (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  2*bound nu*NativeUnifiedCompleteSource.budget seed^2*(2*Real.pi)

theorem coefficient_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ coefficient seed := by
  unfold coefficient bound NativeUnheatedCubicKernel.cap
  positivity [nu.coeff_pos]

theorem row_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖sourceTriple seed 0 time wave output input‖ ≤ coefficient seed*Real.sqrt (mass seed time) := by
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · have actual := action_bound nu (physical seed time nonnegative) regular wave output input
      have velocity : ‖wholeVelocity (physical seed time nonnegative).1‖ ≤ NativeUnifiedCompleteSource.budget seed :=
        (wholeVelocity_norm_le _).trans ((WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound seed time))
      have gradient : ‖gradientValue (physical seed time nonnegative) regular‖ ≤ (2*Real.pi)*Real.sqrt (mass seed time) := by
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        rw [gradientValue_norm_sq, physical_mass]
        simp only [mul_pow, Real.sq_sqrt (mass_nonnegative seed time), le_refl]
      rw [sourceTriple, dif_pos nonnegative, dif_pos regular]
      apply actual.trans
      have square := pow_le_pow_left₀ (norm_nonneg _) velocity 2
      have factor0 : 0 ≤ 2*bound nu := by unfold bound NativeUnheatedCubicKernel.cap; positivity [nu.coeff_pos]
      have scaled := mul_le_mul (mul_le_mul_of_nonneg_left square factor0) gradient (norm_nonneg _)
        (mul_nonneg factor0 (sq_nonneg _))
      exact scaled.trans_eq (by unfold coefficient; ring)
    · simp only [sourceTriple, dif_pos nonnegative, dif_neg regular, norm_zero]
      exact mul_nonneg (coefficient_nonnegative seed) (Real.sqrt_nonneg _)
  · simp only [sourceTriple, dif_neg nonnegative, norm_zero]
    exact mul_nonneg (coefficient_nonnegative seed) (Real.sqrt_nonneg _)

def value (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Space :=
  ofBound (sourceTriple seed 0 time) (coefficient seed*Real.sqrt (mass seed time)) (row_bound seed time)

theorem read_value (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    read (value seed time) = sourceTriple seed 0 time := read_ofBound _ _ _

def squareCoefficient (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  9*coefficient seed^2*(∑' wave, weight wave^2)

theorem squareCoefficient_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ squareCoefficient seed := by
  unfold squareCoefficient
  positivity

theorem norm_sq_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖value seed time‖^2 ≤ squareCoefficient seed*mass seed time := by
  have actual := ofBound_norm_sq (sourceTriple seed 0 time) (coefficient seed*Real.sqrt (mass seed time)) (row_bound seed time)
  rw [mul_pow, Real.sq_sqrt (mass_nonnegative seed time)] at actual
  exact actual.trans_eq (by unfold squareCoefficient; ring)

theorem measurable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    AEStronglyMeasurable (value seed) (volume.restrict (Icc 0 horizon)) := by
  have rows (wave : IntegerWavevector) : AEStronglyMeasurable (fun time => value seed time wave) (volume.restrict (Icc 0 horizon)) := by
    have scalar (pair : Coordinate × Coordinate) : AEStronglyMeasurable (fun time => sourceTriple seed 0 time wave pair.1 pair.2)
        (volume.restrict (Icc 0 horizon)) := (sourceTriple_integrable seed 0 horizon nonnegative wave pair.1 pair.2).aestronglyMeasurable
    have finite : AEStronglyMeasurable (fun time (pair : Coordinate × Coordinate) => sourceTriple seed 0 time wave pair.1 pair.2)
        (volume.restrict (Icc 0 horizon)) := by
      have measured : AEMeasurable (fun time (pair : Coordinate × Coordinate) => sourceTriple seed 0 time wave pair.1 pair.2)
          (volume.restrict (Icc 0 horizon)) := aemeasurable_pi_iff.mpr (fun pair => (scalar pair).aemeasurable)
      exact measured.aestronglyMeasurable
    exact (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate × Coordinate => ℂ)).symm.continuous).comp_aestronglyMeasurable finite).const_smul (weight wave)
  let part (observed : Finset IntegerWavevector) (time : ℝ) : Space :=
    ∑ wave ∈ observed, lp.single 2 wave (value seed time wave)
  have finite (observed : Finset IntegerWavevector) : AEStronglyMeasurable (part observed) (volume.restrict (Icc 0 horizon)) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => Tensor) 2 wave).continuous.comp_aestronglyMeasurable (rows wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset IntegerWavevector)) finite
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (value seed time)

theorem norm_sq_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (fun time => ‖value seed time‖^2) (volume.restrict (Icc 0 horizon)) := by
  apply ((mass_integrable seed horizon nonnegative).const_mul (squareCoefficient seed)).mono'
    ((measurable seed horizon nonnegative).norm.pow 2)
  exact Eventually.of_forall fun time => by simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using! norm_sq_bound seed time

theorem memLp_two (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    MemLp (value seed) 2 (volume.restrict (Icc 0 horizon)) :=
  (memLp_two_iff_integrable_sq_norm (measurable seed horizon nonnegative)).mpr (norm_sq_integrable seed horizon nonnegative)

theorem integral_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, ‖value seed time‖^2) ≤
      squareCoefficient seed*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  have integral := integral_mono (norm_sq_integrable seed horizon nonnegative)
    ((mass_integrable seed horizon nonnegative).const_mul (squareCoefficient seed)) (norm_sq_bound seed)
  rw [integral_const_mul] at integral
  exact integral.trans (mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) (squareCoefficient_nonnegative seed))

theorem value_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    value seed (response.2.clockAdvance+time) = value response.1 time := by
  have later : 0 ≤ response.2.clockAdvance+time := add_nonneg response.2.clockAdvance_pos.le nonnegative
  have same : physical seed (response.2.clockAdvance+time) later = physical response.1 time nonnegative := by
    apply Subtype.ext
    simp only [physical, NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]
  apply read_injective
  rw [read_value, read_value]
  funext wave output input
  by_cases regular : H1 (physical response.1 time nonnegative)
  · have original : H1 (physical seed (response.2.clockAdvance+time) later) := same.symm ▸ regular
    simp only [sourceTriple, dif_pos later, dif_pos nonnegative, dif_pos original, dif_pos regular, same,
      NativeUnheatedGlobalNegativeOne.state_next seed response generated time nonnegative]
  · have original : ¬ H1 (physical seed (response.2.clockAdvance+time) later) := fun h => regular (same ▸ h)
    simp only [sourceTriple, dif_pos later, dif_pos nonnegative, dif_neg original, dif_neg regular]

end
end SaturationMonoid.NavierStokes.NativeUnheatedCubicCarrier

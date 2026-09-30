import H0mework.NavierStokes.UnheatedWriterTriad.PrimitiveKernel
import H0mework.NavierStokes.UnheatedWriterTriad.SourceReadout

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadPrimitiveSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeEndpointVelocityCarrier NativeUnheatedTriadKernel NativeUnheatedStressPairEvolution
open NativeUnheatedTriadPrimitiveKernel
noncomputable section
variable {nu : Viscosity}

def mean (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : NativeUnheatedTriadSum.E :=
  wholeVelocityCLM (NativeUnifiedCompleteSource.source seed time).fst

theorem mean_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (mean seed) (volume : Measure ℝ) :=
  wholeVelocityCLM.continuous.comp_aestronglyMeasurable (NativeUnheatedSourceWeightedTail.velocity_measurable seed)

theorem mean_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖mean seed time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time)

def row (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (i j output spectator : Coordinate)
    (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) : ℂ :=
  NativeUnheatedTriadSum.term (kernel nu i j output) wave i j spectator
    (mean seed time) (mean seed time) (mean seed time) indices

def coefficient (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) : ℂ :=
  NativeUnheatedTriadSum.value (kernel nu i j output) wave i j spectator
    (mean seed time) (mean seed time) (mean seed time)

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  (3 * cap nu * ‖NativeUnheatedTriadSum.weights‖) * (NativeUnifiedCompleteSource.budget seed)^3

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed := by
  have positive : 0 ≤ NativeUnifiedCompleteSource.budget seed := (norm_nonneg _).trans (mean_bound seed 0)
  unfold bound cap
  positivity [nu.coeff_pos]

theorem row_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    Summable (fun indices => ‖row seed wave i j output spectator indices time‖) :=
  NativeUnheatedTriadSum.absolute_summable (kernel nu i j output) (cap nu) (kernel_bound nu i j output)
    wave i j spectator (mean seed time) (mean seed time) (mean seed time)

theorem row_sum_bound (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    (∑' indices, ‖row seed wave i j output spectator indices time‖) ≤ bound seed := by
  have generated := NativeUnheatedTriadSum.absolute_bound (kernel nu i j output) (cap nu)
    (kernel_bound nu i j output) wave i j spectator (mean seed time) (mean seed time) (mean seed time)
  have powered := pow_le_pow_left₀ (norm_nonneg _) (mean_bound seed time) 3
  have factor0 : 0 ≤ 3 * cap nu * ‖NativeUnheatedTriadSum.weights‖ := by unfold cap; positivity [nu.coeff_pos]
  exact generated.trans (by simpa only [bound, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_left powered factor0)

theorem coefficient_eq_tsum (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    coefficient seed wave i j output spectator time = ∑' indices, row seed wave i j output spectator indices time :=
  NativeUnheatedTriadSum.value_eq_tsum (kernel nu i j output) (cap nu) (kernel_bound nu i j output)
    wave i j spectator (mean seed time) (mean seed time) (mean seed time)

theorem coefficient_bound (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    ‖coefficient seed wave i j output spectator time‖ ≤ bound seed := by
  rw [coefficient_eq_tsum]
  exact (norm_tsum_le_tsum_norm (row_summable seed wave i j output spectator time)).trans
    (row_sum_bound seed wave i j output spectator time)

theorem row_original (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    row seed wave i j output spectator indices time =
      ((decay nu (indices.2 + (wave-indices.1-indices.2)) indices.1)⁻¹ *
        (triadDecay nu indices.2 (wave-indices.1-indices.2) indices.1)⁻¹) •
      (NativeUnheatedTriadChannels.pressure (indices.2 + (wave-indices.1-indices.2)) i j output *
        NativeUnheatedTriadTime.product seed (indices.2,i) (wave-indices.1-indices.2,j) (indices.1,spectator) time) := by
  simp only [row, NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm, kernel, mean,
    NativeUnheatedTriadTime.product, NativeUnheatedTriadRows.velocity_original, wholeVelocityCLM_apply,
    Complex.real_smul, Complex.ofReal_mul]
  ring

theorem coefficient_measurable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) :
    AEStronglyMeasurable (coefficient seed wave i j output spectator) (volume : Measure ℝ) :=
  NativeUnheatedTriadSum.aestronglyMeasurable (kernel nu i j output) (cap nu) (kernel_bound nu i j output)
    wave i j spectator (mean_measurable seed) (mean_measurable seed) (mean_measurable seed)

theorem coefficient_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (start finish : ℝ) :
    Integrable (coefficient seed wave i j output spectator) (volume.restrict (Icc start finish)) :=
  (integrable_const (bound seed)).mono' (coefficient_measurable seed wave i j output spectator).restrict
    (Eventually.of_forall (coefficient_bound seed wave i j output spectator))

theorem row_measurable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) :
    AEStronglyMeasurable (row seed wave i j output spectator indices) (volume : Measure ℝ) := by
  have read (k : IntegerWavevector) (coordinate : Coordinate) :
      AEStronglyMeasurable (fun time => mean seed time k coordinate) (volume : Measure ℝ) := by
    let evaluation := (ContinuousLinearMap.proj coordinate : (Coordinate → ℂ) →L[ℝ] ℂ).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => Coordinate → ℂ) 2 k)
    exact evaluation.continuous.comp_aestronglyMeasurable (mean_measurable seed)
  exact (((read indices.2 i).mul (read (wave-indices.1-indices.2) j)).const_mul
    (kernel nu i j output indices.2 (wave-indices.1-indices.2) indices.1)).mul (read indices.1 spectator)

theorem row_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (start finish : ℝ) :
    Integrable (row seed wave i j output spectator indices) (volume.restrict (Icc start finish)) := by
  apply (integrable_const (bound seed)).mono' (row_measurable seed wave i j output spectator indices).restrict
  apply Eventually.of_forall
  intro time
  exact ((row_summable seed wave i j output spectator time).le_tsum indices (fun _ _ => norm_nonneg _)).trans
    (row_sum_bound seed wave i j output spectator time)

theorem row_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (start finish : ℝ) :
    Summable (fun indices => ∫ time in Icc start finish, ‖row seed wave i j output spectator indices time‖) := by
  apply summable_of_sum_le (c := ∫ _time in Icc start finish, bound seed)
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro indices
  rw [← integral_finsetSum _ (fun index _ => (row_integrable seed wave i j output spectator index start finish).norm)]
  apply integral_mono (integrable_finsetSum _ (fun index _ =>
    (row_integrable seed wave i j output spectator index start finish).norm)) (integrable_const (bound seed))
  intro time
  exact ((row_summable seed wave i j output spectator time).sum_le_tsum indices (fun _ _ => norm_nonneg _)).trans
    (row_sum_bound seed wave i j output spectator time)

theorem integral_eq_row_sum (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (start finish : ℝ) :
    (∫ time in Icc start finish, coefficient seed wave i j output spectator time) =
      ∑' indices, ∫ time in Icc start finish, row seed wave i j output spectator indices time := by
  rw [integral_tsum_of_summable_integral_norm
    (fun index => row_integrable seed wave i j output spectator index start finish)
    (row_integrals_summable seed wave i j output spectator start finish)]
  exact integral_congr_ae (Eventually.of_forall (coefficient_eq_tsum seed wave i j output spectator))

def primitive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressCoefficient :=
  fun output spectator => -(∑ i : Coordinate, ∑ j : Coordinate,
    (coefficient seed wave i j spectator output time + coefficient seed wave i j output spectator time))

theorem primitive_row_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector)
    (output spectator : Coordinate) : ‖primitive seed time wave output spectator‖ ≤ 18 * bound seed := by
  rw [primitive, norm_neg]
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Coordinate)) =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Coordinate)) =>
      (norm_add_le _ _).trans (add_le_add (coefficient_bound seed wave i j spectator output time)
        (coefficient_bound seed wave i j output spectator time)))))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at paid
  nlinarith only [paid]

theorem primitive_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    ‖primitive seed time wave‖ ≤ 18 * bound seed := by
  have nonnegative := mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) (bound_nonnegative seed)
  apply (pi_norm_le_iff_of_nonneg nonnegative).mpr
  intro output
  exact (pi_norm_le_iff_of_nonneg nonnegative).mpr (primitive_row_bound seed time wave output)

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed (response.2.clockAdvance+time) = primitive response.1 time := by
  funext wave output spectator
  simp only [primitive, coefficient_eq_tsum, row_original,
    NativeUnheatedTriadTime.product_next seed _ _ _ response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadPrimitiveSource

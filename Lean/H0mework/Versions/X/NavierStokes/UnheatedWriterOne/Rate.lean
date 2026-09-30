import H0mework.Versions.X.NavierStokes.UnheatedWriterGradient.Physical
import H0mework.Versions.X.NavierStokes.StressNegativeOne.Rate

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedGlobalNegativeOne

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing
open NativeNegativeOneInclusion NativeNegativeOneMomentum NativeUnheatedSourceGradient
open NativeCompleteStressAction NativeCompleteStressBilinear NativeEndpointVelocityCarrier

noncomputable section
variable {nu : Viscosity}

def rate (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State := by
  classical
  exact if nonnegative : 0 ≤ time then
    if regular : H1 (physical seed time nonnegative) then
      momentum nu (physical seed time nonnegative) regular else 0
  else 0

theorem rate_original_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, ∀ wave : Wave, rate seed time wave =
      if 0 ≤ time then (lowerWeight wave)⁻¹ •
        (NativeWholeResolventZeroAction.momentumOperator nu
          (NativeUnifiedCompleteSource.source seed time).fst (NativeUnifiedCompleteSource.source seed time).fst wave)
      else 0 := by
  filter_upwards [physical_H1_ae seed] with time generated
  intro wave
  by_cases nonnegative : 0 ≤ time
  · rw [rate, dif_pos nonnegative, dif_pos (generated nonnegative), if_pos nonnegative]
    exact original_row nu _ (generated nonnegative) wave
  · simp only [rate, dif_neg nonnegative, if_neg nonnegative, lp.coeFn_zero, Pi.zero_apply]

theorem rate_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (rate seed) (volume : Measure ℝ) := by
  have velocity := (WithLp.fstL 2 ℝ _ NativeCompleteStressCarrier.Space).continuous.comp_aestronglyMeasurable
    (NativeUnifiedCompleteSource.source_measurable seed)
  have rows (wave : Wave) : AEStronglyMeasurable (fun time => rate seed time wave) (volume : Measure ℝ) := by
    have original := (original_continuous nu).comp_aestronglyMeasurable velocity
    have read := ((lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable original).const_smul
      (lowerWeight wave)⁻¹
    have piece := read.restrict.piecewise (s := Ici (0 : ℝ)) (g := fun _ => (0 : ComplexCoordinateEuclidean))
      measurableSet_Ici aestronglyMeasurable_const
    apply piece.congr
    filter_upwards [rate_original_ae seed] with time same
    exact (same wave).symm
  let part (observed : Finset Wave) (time : ℝ) : State :=
    ∑ wave ∈ observed, lp.single 2 wave (rate seed time wave)
  have measurable (observed : Finset Wave) : AEStronglyMeasurable (part observed) (volume : Measure ℝ) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable (rows wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Wave)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (rate seed time)

theorem rate_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖rate seed time‖ ≤ coefficient nu * (1 + mass seed time) := by
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · rw [rate, dif_pos nonnegative, dif_pos regular]
      simpa only [physical_mass] using momentum_bound nu (physical seed time nonnegative) regular
    · rw [rate, dif_pos nonnegative, dif_neg regular, norm_zero]
      exact mul_nonneg (coefficient_nonnegative nu) (by linarith [mass_nonnegative seed time])
  · rw [rate, dif_neg nonnegative, norm_zero]
    exact mul_nonneg (coefficient_nonnegative nu) (by linarith [mass_nonnegative seed time])

theorem rate_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (rate seed) (volume.restrict (Icc 0 horizon)) :=
  ((integrable_const (1 : ℝ)).add (mass_integrable seed horizon nonnegative)).const_mul (coefficient nu) |>.mono'
    (rate_measurable seed).restrict (Eventually.of_forall (rate_bound seed))

theorem lower_rate_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → lowerCLM (rate seed time) = momentumCLM nu (NativeUnifiedCompleteSource.source seed time) := by
  filter_upwards [physical_H1_ae seed, NativeUnifiedGlobalStressSource.stress_ae seed] with time regular stress
  intro nonnegative
  rw [rate, dif_pos nonnegative, dif_pos (regular nonnegative), NativeNegativeOneMomentum.momentum, lower_momentum]
  have tensor : (NativeUnifiedCompleteSource.source seed time).snd =
      mixed (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
    apply NativeCompleteStressCarrier.read_injective
    rw [NativeUnifiedCompleteSource.stress_read, stress, mixed_read, NativeHigherTimeJets.mixedFlux_diagonal,
      NativeUnifiedCompleteSource.velocity_read]
  change NativeWholeResolventZeroAction.momentumOperator nu
    (NativeUnifiedCompleteSource.source seed time).fst (NativeUnifiedCompleteSource.source seed time).fst = _
  rw [NativeWholeResolventZeroAction.momentumOperator]
  change _ = divergenceCLM (NativeUnifiedCompleteSource.source seed time).snd -
    viscousCLM nu (NativeUnifiedCompleteSource.source seed time).fst
  rw [tensor]
  rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedGlobalNegativeOne

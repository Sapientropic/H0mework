import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Source
import H0mework.Versions.X.NavierStokes.WindowSourcePreparation.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffStress
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeCompleteStressCarrier NativeWindowFiniteStressConvergence NativeEndpointVelocityCarrier NativeHigherTimeJets
noncomputable section
variable {nu : Viscosity}

def lowCLM (F : Finset IntegerWavevector) : Space →L[ℝ] Space :=
  ∑ k ∈ F,(lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => Tensor) 2 k).comp
    (lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 k)

theorem low_row (F : Finset IntegerWavevector) (value : Space) (k : IntegerWavevector) :
    lowCLM F value k=if k∈F then value k else 0 := by
  classical
  simp only [lowCLM,sum_apply,ContinuousLinearMap.comp_apply,lp.coeFn_sum,Finset.sum_apply,
    lp.singleContinuousLinearMap_apply,lp.coeFn_single,Finset.sum_pi_single]
  rfl

theorem low_bound (F : Finset IntegerWavevector) (value : Space) : ‖lowCLM F value‖≤‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  rw [low_row]
  split_ifs <;> simp

theorem low_tendsto (value : Space) : Tendsto (fun radius => lowCLM (integerWaveFrequencyCube radius) value) atTop (nhds value) := by
  have finite : HasSum (fun k => lp.single 2 k (value k)) value := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) value
  have source:=finite.comp integerWaveFrequencyCube_tendsto_atTop
  simpa only [lowCLM,sum_apply,ContinuousLinearMap.comp_apply,lp.singleContinuousLinearMap_apply,Function.comp_def] using! source

def value (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Space :=
  lowCLM F (source seed time)-finiteAt seed F time

def coefficients (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (k : IntegerWavevector) : ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressCoefficient :=
  (if k∈F then read (NativeUnifiedCompleteSource.source seed time).snd k else 0)-
    mixedFlux (NativeUnheatedWindowStress.projection seed F time) (NativeUnheatedWindowStress.projection seed F time) k

theorem value_original_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0 ≤ time →∀ F k,
    value seed F time k=NativeWindowSobolevStress.quarter k • tensor (coefficients seed F time k) := by
  filter_upwards [source_row_ae seed] with time original nonnegative F k
  rw [value,lp.coeFn_sub,Pi.sub_apply,low_row,finiteAt,finite_row]
  rw [original nonnegative k]
  by_cases inside : k∈F <;> ext entry <;> simp [coefficients,inside,tensor,smul_sub,NativeUnheatedWindowStress.projection]

theorem value_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (k : IntegerWavevector) (outside : k∉F∪(F+F)) : value seed F time k=0 := by
  rw [value,lp.coeFn_sub,Pi.sub_apply,low_row,if_neg (fun inside => outside (Finset.mem_union_left _ inside)),
    finiteAt,finite_supported _ F k (fun inside => outside (Finset.mem_union_right _ inside)),sub_self]

theorem value_bound_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0 ≤ time →∀ F,
    ‖value seed F time‖≤(2*cap)*NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [source_bound_ae seed] with time paid nonnegative F
  exact (norm_sub_le _ _).trans ((add_le_add ((low_bound F _).trans (paid nonnegative).1)
    ((paid nonnegative).2 F)).trans_eq (by ring))

theorem value_tendsto_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0 ≤ time →
    Tendsto (fun radius => value seed (integerWaveFrequencyCube radius) time) atTop (nhds 0) := by
  filter_upwards [source_tendsto_ae seed] with time paid nonnegative
  simpa only [value,sub_self] using (low_tendsto (source seed time)).sub (paid nonnegative)

theorem value_measurable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (horizon : ℝ) :
    AEStronglyMeasurable (value seed F) (volume.restrict (Icc 0 horizon)) :=
  ((lowCLM F).continuous.comp_aestronglyMeasurable (source_measurable seed horizon)).sub
    (finiteAt_continuous seed F).aestronglyMeasurable.restrict

theorem value_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) : Integrable (value seed F) (volume.restrict (Icc 0 horizon)) := by
  apply ((NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative).const_mul (2*cap)).mono'
    (value_measurable seed F horizon)
  filter_upwards [ae_restrict_of_ae (value_bound_ae seed),ae_restrict_mem measurableSet_Icc] with time paid inside
  exact paid inside.1 F

theorem integral_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫time in Icc 0 horizon,‖value seed (integerWaveFrequencyCube radius) time‖) atTop (nhds 0) := by
  have paid:=tendsto_integral_of_dominated_convergence
    (fun time => (2*cap)*NativeUnheatedSourceGradient.mass seed time)
    (fun radius => (value_measurable seed (integerWaveFrequencyCube radius) horizon).norm)
    ((NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative).const_mul (2*cap))
    (fun radius => by
      filter_upwards [ae_restrict_of_ae (value_bound_ae seed),ae_restrict_mem measurableSet_Icc] with time bound inside
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using bound inside.1 (integerWaveFrequencyCube radius))
    (by
      filter_upwards [ae_restrict_of_ae (value_tendsto_ae seed),ae_restrict_mem measurableSet_Icc] with time actual inside
      simpa only [norm_zero] using (actual inside.1).norm)
  simpa only [integral_zero] using paid

theorem value_before (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (before : time ≤ 0) :
    value seed F time=value seed F 0 := by
  have same := NativeWindowPreparationSource.complete_nonpositive seed time before
  have velocity : NativeAbsoluteEventualControl.velocity seed time=NativeAbsoluteEventualControl.velocity seed 0 := by
    rw [← NativeUnifiedCompleteSource.velocity_read,← NativeUnifiedCompleteSource.velocity_read]
    exact congrArg WithLp.fst same
  have weighted : source seed time=source seed 0 := by
    unfold source
    rw [show (NativeUnifiedCompleteSource.source seed time).fst=
      (NativeUnifiedCompleteSource.source seed 0).fst from congrArg WithLp.fst same]
  simp only [value,weighted,finiteAt,velocity]

theorem value_integrable_total (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (a b : ℝ) :
    Integrable (value seed F) (volume.restrict (Icc a b)) := by
  let H:=max 0 b
  let difference := fun time => value seed F time-value seed F 0
  have positive : Integrable ((Icc 0 H).indicator difference) (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Icc).2
      ((value_integrable seed F H (le_max_left _ _)).sub (integrable_const _))
  have same : (fun time => value seed F 0+(Icc 0 H).indicator difference time)=ᵐ[volume.restrict (Icc a b)] value seed F := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
    by_cases nonnegative : 0 ≤ time
    · rw [indicator_of_mem (show time∈Icc 0 H from ⟨nonnegative,inside.2.trans (le_max_right _ _)⟩)]
      dsimp only [difference]
      abel
    · rw [indicator_of_notMem (fun member => nonnegative member.1),add_zero,value_before seed F time (le_of_not_ge nonnegative)]
  exact ((integrable_const _).add positive.integrableOn).congr same

theorem value_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    LocallyIntegrable (value seed F) (volume : Measure ℝ) := by
  intro x
  exact ⟨Icc (x-1) (x+1),Icc_mem_nhds (by linarith) (by linarith),value_integrable_total seed F (x-1) (x+1)⟩

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    value seed F (step.2.clockAdvance+time)=value step.1 F time := by
  have same := NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative
  have weighted : source seed (step.2.clockAdvance+time)=source step.1 time := by
    unfold source
    rw [show (NativeUnifiedCompleteSource.source seed (step.2.clockAdvance+time)).fst=
      (NativeUnifiedCompleteSource.source step.1 time).fst from congrArg WithLp.fst same]
  have velocity : NativeAbsoluteEventualControl.velocity seed (step.2.clockAdvance+time)=NativeAbsoluteEventualControl.velocity step.1 time := by
    rw [← NativeUnifiedCompleteSource.velocity_read,← NativeUnifiedCompleteSource.velocity_read]
    exact congrArg WithLp.fst same
  simp only [value,weighted,finiteAt,velocity]

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffStress

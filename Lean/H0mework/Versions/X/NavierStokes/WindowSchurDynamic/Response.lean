import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse temporalBudget)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowHistoryCommonResponse (response)
open NativeWindowHistoryCommonForceBounds (budget)
open NativeWindowHistoryJacobianControl (density density_integrable density_integral density_include form correction jacobian)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) : energy nu M (response seed M order time)≤budget seed horizon order := by
  have point : ∀ᵐ lag ∂averageMeasure,density nu M (response seed M order time lag)≤budget seed horizon order := by
    filter_upwards [NativeWindowHistoryCommonResponse.response_sample seed M order time] with lag actual
    rw [actual,density_include]
    exact NativeWindowHistoryCommonResponse.source_sample_bound seed horizon M order time inside lag
  have source := integral_mono_ae (density_integrable nu M (response seed M order time)) (integrable_const _) point
  simpa only [density_integral,integral_const,probReal_univ,one_smul] using source

theorem response_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    response seed M 0 time=completion seed M time := by
  apply Lp.ext
  filter_upwards [NativeWindowHistoryCommonResponse.response_ae seed M 0 time,
    NativeWindowHistoryInverseWindow.completion_original seed M time] with lag responseRead completionRead
  rw [responseRead,completionRead,NativeWindowHistoryCommonResponse.curve,
    NativeWindowHistoryCommonForceTime.jet_zero,NativeWindowHistoryCommonForceTime.value_original]

private theorem form_abs (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (u v : H) :
    |2*form nu M u v|≤energy nu M u+energy nu M v := by
  have first := NativeWindowHistoryJacobianControl.form_young seed M u v 1
  have last := NativeWindowHistoryJacobianControl.form_young seed M u v (-1)
  apply abs_le.mpr
  constructor <;> nlinarith only [first,last]

private theorem mass_le_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) :
    ‖v‖^2≤energy nu M v := by
  have positive := mul_nonneg nu.coeff_pos.le (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M v)
  unfold energy
  linarith only [positive]

def work (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (temporalResponse seed M time) (jacobian seed M time (response seed M order time))

private theorem form_difference {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (u v : E) (A : E →L[ℝ] E) :
    2*inner ℝ u (L (v-A v))=2*inner ℝ u (L v)-2*inner ℝ u (L (A v)) := by
  rw [map_sub,inner_sub_right,mul_sub]

private theorem abs_difference (a b : ℝ) : |a-b|≤|a|+|b| := by
  simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le a 0 b

private theorem jacobian_pair_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u v : H) :
    |2*form nu M u (jacobian seed M time v)|≤
      2*energy nu M u+energy nu M v+energy nu M (correction seed M time v) := by
  have identity : 2*form nu M u (jacobian seed M time v)=2*form nu M u v-2*form nu M u (correction seed M time v) := by
    simpa only [form,jacobian,sub_apply,ContinuousLinearMap.id_apply] using!
      form_difference (E := H) (NativeWindowHistoryJacobianControl.heat nu M) u v (correction seed M time)
  have triangle := (abs_difference _ _).trans (add_le_add (form_abs seed M u v)
    (form_abs seed M u (correction seed M time v)))
  rw [identity]
  exact triangle.trans_eq (by ring)

theorem source_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ order : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      |work seed M order time|≤C := by
  obtain ⟨low,A,A0,paid⟩ := NativeWindowHistoryJacobianControl.source_correction_bound seed horizon nonnegative 1 (by norm_num)
  refine ⟨low,fun order => ⟨2*temporalBudget seed horizon+(2+A)*budget seed horizon order,?_,?_⟩⟩
  · exact add_nonneg (mul_nonneg (by norm_num) (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon))
      (mul_nonneg (by linarith only [A0]) (NativeWindowHistoryCommonForceBounds.budget_nonnegative seed horizon order))
  · intro M above time inside
    have w := NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
    have y := source_energy seed horizon M order time inside
    have r := paid M above time inside (response seed M order time)
    have mass := mass_le_energy seed M (response seed M order time)
    have triangle := jacobian_pair_bound seed M time (temporalResponse seed M time) (response seed M order time)
    change |work seed M order time|≤_ at triangle
    have scaledMass := mul_le_mul_of_nonneg_left mass A0
    have scaledY := mul_le_mul_of_nonneg_left y A0
    nlinarith only [triangle,w,y,r,scaledMass,scaledY]

def reactionWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (temporalResponse seed M time) (jacobian seed M time (completion seed M time))

theorem reaction_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    reactionWork seed M time=work seed M 0 time :=
  congrArg (fun v : H => 2*form nu M (temporalResponse seed M time) (jacobian seed M time v)) (response_zero seed M time).symm

theorem source_reaction_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,|reactionWork seed M time|≤C := by
  obtain ⟨low,paid⟩ := source_work_bound seed horizon nonnegative
  obtain ⟨C,C0,bound⟩ := paid 0
  exact ⟨low,C,C0,fun M above time inside => (congrArg abs (reaction_original seed M time)).trans_le (bound M above time inside)⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    work seed M order (step.2.clockAdvance+time)=work step.1 M order time := by
  have applied := congrArg₂ (fun (D : H →L[ℝ] H) (v : H) => D v)
    (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0)
    (NativeWindowHistoryCommonResponse.response_next seed M order step generated time time0)
  exact congrArg₂ (fun u v : H => 2*form nu M u v)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0) applied

theorem reaction_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    reactionWork seed M (step.2.clockAdvance+time)=reactionWork step.1 M time := by
  have applied := congrArg₂ (fun (D : H →L[ℝ] H) (v : H) => D v)
    (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0)
    (NativeWindowHistorySchurCompletion.completion_next seed M step generated time time0)
  exact congrArg₂ (fun u v : H => 2*form nu M u v)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0) applied

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicResponse

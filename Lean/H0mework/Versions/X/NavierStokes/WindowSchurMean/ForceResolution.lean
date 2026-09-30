import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl
import H0mework.Versions.X.NavierStokes.WindowSchurMean.ForcingTest
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Momentum

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanForceResolution
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowTraceWholeHistory (finiteHistory projected projection)
open NativeWindowHistoryHeatDual (heat heatEnergy energy)
open NativeWindowHistoryDynamicHistory (kernelAction kernelAction_ae)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def force (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean (forcingHistory seed M time))

theorem force_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    pairing (modes M) v (force seed M time)=
      inner ℝ (embed (includeCLM (modes M) (modes_closed M) v)) (forcingHistory seed M time) := by
  rw [NativeWindowHistoryMeanProjection.embed_pairing,include_inner _ (modes_zero M)]
  rfl

private theorem heat_small (e g d epsilon a : ℝ) (e0 : 0≤e) (g0 : 0≤g)
    (eps0 : 0<epsilon) (source : e≤d*Real.sqrt g) (gradient : a*g≤e) (square : d^2=a*epsilon) : e≤epsilon := by
  have bound:=pow_le_pow_left₀ e0 source 2
  rw [mul_pow,Real.sq_sqrt g0,square] at bound
  have scaled:=mul_le_mul_of_nonneg_left gradient eps0.le
  by_contra failed
  have pos:e>0:=lt_trans eps0 (lt_of_not_ge failed)
  have sign:=mul_pos pos (sub_pos.mpr (lt_of_not_ge failed))
  nlinarith only [bound,scaled,sign]

theorem source_force_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ M≥low,∀ time∈Icc 0 horizon,heatEnergy nu M (force seed M time)≤epsilon := by
  let delta:=Real.sqrt (nu.coeff*epsilon)
  have delta0:0<delta:=Real.sqrt_pos.mpr (mul_pos nu.coeff_pos positive)
  obtain ⟨low,paid⟩:=NativeWindowHistoryMeanForcingTest.source_effect_small seed horizon nonnegative delta delta0
  refine ⟨low,fun M above time inside => ?_⟩
  let f:=force seed M time
  let v:=heat nu M f
  have source:heatEnergy nu M f≤delta*Real.sqrt (curlPair (modes M) v.1 v.1) := by
    have read:heatEnergy nu M f=inner ℝ (embed (includeCLM (modes M) (modes_closed M) v)) (forcingHistory seed M time) :=
      force_pairing seed M time v
    exact (le_abs_self _).trans ((congrArg abs read).trans_le (paid M above time inside v))
  have gradient:nu.coeff*curlPair (modes M) v.1 v.1≤heatEnergy nu M f := by
    have actual:=NativeWindowHistoryHeatDual.heatEnergy_self nu M f
    change heatEnergy nu M f=‖coefficients (modes M) v‖^2+nu.coeff*curlPair (modes M) v.1 v.1 at actual
    linarith only [actual,sq_nonneg ‖coefficients (modes M) v‖]
  exact heat_small _ _ _ _ _ (NativeWindowHistoryHeatDual.heatEnergy_nonnegative nu M f)
    (NativeWindowHistorySchurSampleControl.gradient_nonnegative M v) positive source gradient
    (Real.sq_sqrt (mul_nonneg nu.coeff_pos.le positive.le))

theorem forcing_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    projected M (forcingHistory seed M time)=forcingHistory seed M time := by
  let P:=(projection M).compLpL 2 averageMeasure
  have source:=P.hasFDerivAt.comp_hasDerivAt (E := H) (F := H) time (NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  have original:HasDerivAt (fun t => finiteHistory seed t M) (P (rateHistory seed M time)) time := by
    apply source.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => (NativeWindowHistoryOseenGap.projected_finiteHistory seed t M).symm
  have rate:=HasDerivAt.unique (𝕜 := ℝ) (F := H) original (NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  have forcing:=NativeWindowHistoryOseen.forcingHistory_difference seed M time
  exact (congrArg P forcing).trans ((P.map_sub _ _).trans
    ((congrArg₂ (fun x y : H => x-y) rate (NativeWindowHistoryOseenGap.projected_action seed M time _)).trans forcing.symm))

theorem force_include (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (force seed M time)=mean (forcingHistory seed M time) :=
  (NativeWindowHistoryMeanProjection.mean_comp (projection M) (forcingHistory seed M time)).symm.trans
    (congrArg mean (forcing_projected seed M time))

def error (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  kernelAction seed M time (embed (mean (forcingHistory seed M time)))

def resolved (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  completion seed M time-error seed M time

theorem error_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    error seed M time=ᵐ[averageMeasure] fun lag => includeCLM (modes M) (modes_closed M)
      (NativeWindowHistoryFrozenInverse.physical seed M (time-lag) (force seed M time)) := by
  filter_upwards [kernelAction_ae seed M time (embed (mean (forcingHistory seed M time))),
    NativeWindowTraceWholeHistory.constant_ae (mean (forcingHistory seed M time))] with lag source constant
  change error seed M time lag=_ at source
  rw [source,show embed (mean (forcingHistory seed M time)) lag=mean (forcingHistory seed M time) from constant,
    ← force_include]
  change includeCLM (modes M) (modes_closed M) (NativeWindowHistoryFrozenInverse.physical seed M (time-lag)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (includeCLM (modes M) (modes_closed M) _)))=_
  rw [restrict_include]

theorem source_point_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ M≥low,∀ time∈Icc 0 horizon,∀ sample : ℝ,
      energy nu M (NativeWindowHistoryFrozenInverse.physical seed M sample (force seed M time))≤epsilon := by
  obtain ⟨low,paid⟩:=source_force_small seed horizon nonnegative epsilon positive
  exact ⟨low,fun M above time inside sample =>
    (NativeWindowHistoryHeatDual.source_bound seed M sample _).trans (paid M above time inside)⟩

theorem source_error_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ M≥low,∀ time∈Icc 0 horizon,
      NativeWindowHistorySchurTemporalControl.energy nu M (error seed M time)≤epsilon := by
  obtain ⟨low,paid⟩:=source_point_small seed horizon nonnegative epsilon positive
  refine ⟨low,fun M above time inside => ?_⟩
  have point:∀ᵐ lag ∂averageMeasure,NativeWindowHistoryJacobianControl.density nu M (error seed M time lag)≤epsilon := by
    filter_upwards [error_ae seed M time] with lag read
    rw [read,NativeWindowHistoryJacobianControl.density_include]
    exact paid M above time inside (time-lag)
  have bound:=integral_mono_ae (NativeWindowHistoryJacobianControl.density_integrable nu M (error seed M time)) (integrable_const _) point
  simpa only [NativeWindowHistoryJacobianControl.density_integral,integral_const,probReal_univ,one_smul] using bound

theorem resolved_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (resolved seed M time)=mean (finiteHistory seed time M)-mean (error seed M time) :=
  (mean.map_sub _ _).trans (congrArg (fun x => x-mean (error seed M time))
    (NativeWindowHistorySchurCompletion.completion_mean seed M time))

theorem error_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    error seed M time-action seed M time (error seed M time)=embed (mean (forcingHistory seed M time)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (error seed M time) (action seed M time (error seed M time)),
    NativeWindowHistoryOseen.action_ae seed M time (error seed M time),error_ae seed M time,
    NativeWindowTraceWholeHistory.constant_ae (mean (forcingHistory seed M time))]
    with lag difference acted original constant
  have source:=congrArg (includeCLM (modes M) (modes_closed M))
    (NativeWindowHistoryFrozenInverse.physical_write seed M (time-lag) (force seed M time))
  have write:includeCLM (modes M) (modes_closed M) (NativeWindowHistoryFrozenInverse.physical seed M (time-lag) (force seed M time))-
      NativeWindowHistoryOseen.forwardFiber seed M (time-lag)
        (includeCLM (modes M) (modes_closed M) (NativeWindowHistoryFrozenInverse.physical seed M (time-lag) (force seed M time)))=
      includeCLM (modes M) (modes_closed M) (force seed M time) := by
    simpa only [map_sub,NativeWindowHistoryOseen.forwardFiber,NativeWindowHistoryOseen.lift_included] using! source
  exact difference.trans ((congrArg₂ (fun x y : wholePhysical => x-y) original
    (acted.trans (congrArg (NativeWindowHistoryOseen.forwardFiber seed M (time-lag)) original))).trans
      (write.trans ((force_include seed M time).trans constant.symm)))

def input (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  mean (finiteHistory seed time M)-mean (rateHistory seed M time)+
    mean (NativeWindowHistorySchurMomentum.xMixed seed M time)+mean (NativeWindowHistorySchurMomentum.wSelf seed M time)

theorem input_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    input seed M time=commonForce seed M time-mean (forcingHistory seed M time) := by
  unfold input
  rw [NativeWindowHistorySchurMomentum.source_momentum]
  abel

private theorem subtract_equations {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (x e c f : E) (first : x-A x=c) (last : e-A e=f) :
    (x-e)-A (x-e)=c-f := by
  rw [map_sub,← first,← last]
  abel

theorem resolved_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    resolved seed M time-action seed M time (resolved seed M time)=embed (input seed M time) := by
  have source:=subtract_equations (E := H) (action seed M time) (completion seed M time) (error seed M time)
    (embed (commonForce seed M time)) (embed (mean (forcingHistory seed M time)))
    (NativeWindowHistorySchurCompletion.completion_equation seed M time) (error_equation seed M time)
  exact source.trans ((embed.map_sub _ _).symm.trans (congrArg embed (input_original seed M time).symm))

def resolvedSample (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) : physicalSpace (modes M) :=
  NativeWindowHistorySchurSampleControl.sample seed M time lag-
    NativeWindowHistoryFrozenInverse.physical seed M (time-lag) (force seed M time)

theorem resolved_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    resolved seed M time=ᵐ[averageMeasure] fun lag =>
      includeCLM (modes M) (modes_closed M) (resolvedSample seed M time lag) := by
  filter_upwards [Lp.coeFn_sub (completion seed M time) (error seed M time),error_ae seed M time,
    NativeWindowHistorySchurSampleControl.sample_include seed M time] with lag difference discarded kept
  change resolved seed M time lag=_ at difference
  exact difference.trans ((congrArg₂ (fun x y : wholePhysical => x-y) kept.symm discarded).trans (map_sub _ _ _).symm)

private theorem quadratic_sub {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (positive : ∀ x,0≤B x x) (x y : E) :
    B (x-y) (x-y)≤2*B x x+2*B y y := by
  have source:=positive (x+y)
  simp only [map_add,LinearMap.add_apply] at source
  simp only [map_sub,LinearMap.sub_apply]
  linarith only [source]

theorem finite_sub_bound (nu : Viscosity) (M : ℕ) (x y : physicalSpace (modes M)) :
    energy nu M (x-y)≤2*energy nu M x+2*energy nu M y := by
  simpa only [NativeWindowHistoryHeatDual.form_self] using quadratic_sub (NativeWindowHistoryHeatDual.form nu M)
    (fun v => (NativeWindowHistoryHeatDual.energy_nonnegative nu M v).trans_eq (NativeWindowHistoryHeatDual.form_self nu M v).symm) x y

theorem source_resolved_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ B : ℝ,0≤B ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ∀ᵐ lag ∂averageMeasure,energy nu M (resolvedSample seed M time lag)≤B := by
  obtain ⟨first,C,C0,source⟩:=NativeWindowHistorySchurSampleControl.source_sample_bound seed horizon nonnegative
  obtain ⟨last,small⟩:=source_point_small seed horizon nonnegative 1 (by norm_num)
  refine ⟨max first last,2*C+2,by positivity,fun M above time inside => ?_⟩
  filter_upwards [source M ((le_max_left _ _).trans above) time inside] with lag bounded
  have x:energy nu M (NativeWindowHistorySchurSampleControl.sample seed M time lag)≤C := by
    simpa only [NativeWindowHistorySchurSampleControl.sampleEnergy,energy,pairing,LinearMap.mk₂_apply,real_inner_self_eq_norm_sq] using bounded
  have e:=small M ((le_max_right _ _).trans above) time inside (time-lag)
  have sub:=finite_sub_bound nu M (NativeWindowHistorySchurSampleControl.sample seed M time lag)
    (NativeWindowHistoryFrozenInverse.physical seed M (time-lag) (force seed M time))
  change energy nu M (resolvedSample seed M time lag)≤_ at sub
  linarith only [sub,x,e]

theorem source_resolved_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ B : ℝ,0≤B ∧∀ M≥low,∀ time∈Icc 0 horizon,
      NativeWindowHistorySchurTemporalControl.energy nu M (resolved seed M time)≤B := by
  obtain ⟨low,B,B0,source⟩:=source_resolved_bound seed horizon nonnegative
  refine ⟨low,B,B0,fun M above time inside => ?_⟩
  have point:∀ᵐ lag ∂averageMeasure,NativeWindowHistoryJacobianControl.density nu M (resolved seed M time lag)≤B := by
    filter_upwards [resolved_ae seed M time,source M above time inside] with lag read bound
    rw [read,NativeWindowHistoryJacobianControl.density_include]
    exact bound
  have paid:=integral_mono_ae (NativeWindowHistoryJacobianControl.density_integrable nu M (resolved seed M time)) (integrable_const _) point
  simpa only [NativeWindowHistoryJacobianControl.density_integral,integral_const,probReal_univ,one_smul] using paid

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem error_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    error seed M (step.2.clockAdvance+time)=error step.1 M time :=
  congrArg₂ (fun (K : H →L[ℝ] H) (f : H) => K (embed (mean f)))
    (NativeWindowHistoryDynamicHistory.kernelAction_next seed M step generated time time0)
    (NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0)

theorem resolved_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    resolved seed M (step.2.clockAdvance+time)=resolved step.1 M time :=
  congrArg₂ (fun x e : H => x-e) (NativeWindowHistorySchurCompletion.completion_next seed M step generated time time0)
    (error_next seed M step generated time time0)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanForceResolution

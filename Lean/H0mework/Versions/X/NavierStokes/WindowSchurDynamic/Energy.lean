import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.History
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CommonResponseWork

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H rateHistory action forcingHistory)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeWindowHistorySchurTranspose (transposeAction)
open NativeWindowTraceWholeHistory (projected finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistoryDynamicHistory (kernelAction commonRate residualRate)
open NativeWindowHistoryMeanProjection (embed)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def principal (nu : Viscosity) (M : ℕ) : H →L[ℝ] H :=
  (NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure+nu.coeff • laplacianAction nu M

theorem principal_apply (nu : Viscosity) (M : ℕ) (v : H) :
    principal nu M v=projected M v+nu.coeff • laplacianAction nu M v := rfl

theorem principal_symmetric (nu : Viscosity) (M : ℕ) (u v : H) :
    inner ℝ (principal nu M u) v=inner ℝ u (principal nu M v) :=
  NativeWindowHistoryCommonResponseWork.principal_pairing nu M u v

theorem residual_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    projected M (temporalResponse seed M time)=temporalResponse seed M time := by
  have same : temporalResponse seed M time=finiteHistory seed time M-NativeWindowHistorySchurCompletion.completion seed M time := by
    rw [NativeWindowHistorySchurCompletion.source_split]
    abel
  have distribute := ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure).map_sub
    (finiteHistory seed time M) (NativeWindowHistorySchurCompletion.completion seed M time)
  exact (congrArg (projected M) same).trans (distribute.trans
    ((congrArg₂ (fun x y : H => x-y) (NativeWindowHistoryOseenGap.projected_finiteHistory seed time M)
      (NativeWindowHistorySchurCompletion.completion_projected seed M time)).trans same.symm))

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (temporalResponse seed M time) (principal nu M (temporalResponse seed M time))

private theorem quadratic_read {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v l : E) (a : ℝ) : inner ℝ v (v+a • l)=‖v‖^2+a*inner ℝ v l := by
  rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]

private theorem principal_energy (nu : Viscosity) (M : ℕ) (v : H) (supported : projected M v=v) :
    inner ℝ v (principal nu M v)=NativeWindowHistorySchurTemporalControl.energy nu M v := by
  have actual : principal nu M v=v+nu.coeff • laplacianAction nu M v :=
    (principal_apply nu M v).trans (congrArg (fun x : H => x+nu.coeff • laplacianAction nu M v) supported)
  have point := (congrArg (fun x : H => inner ℝ v x) actual).trans
    (quadratic_read (E := H) v (laplacianAction nu M v) nu.coeff)
  exact point.trans (congrArg (fun r : ℝ => ‖v‖^2+nu.coeff*r)
    (NativeWindowMetricGraphHistory.history_gradient nu M v))

theorem energy_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    energy seed M time=NativeWindowHistorySchurTemporalControl.energy nu M (temporalResponse seed M time) :=
  principal_energy nu M (temporalResponse seed M time) (residual_projected seed M time)

def sourceRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*inner ℝ (principal nu M (temporalResponse seed M time)) (residualRate seed M time)

private theorem paired_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (symmetric : ∀ x y,inner ℝ (T x) y=inner ℝ x (T y))
    {f : ℝ → E} {d : E} {t : ℝ} (derivative : HasDerivAt f d t) :
    HasDerivAt (fun s => inner ℝ (f s) (T (f s))) (2*inner ℝ (T (f t)) d) t := by
  have last := T.hasFDerivAt.comp_hasDerivAt t derivative
  have original := derivative.inner ℝ last
  have same := symmetric (f t) d
  have swap := real_inner_comm (T (f t)) d
  have value : inner ℝ (f t) (T d)+inner ℝ d ((T ∘ f) t)=2*inner ℝ (T (f t)) d := by
    change inner ℝ (f t) (T d)+inner ℝ d (T (f t))=_
    linarith only [same,swap]
  rw [value] at original
  exact original

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (energy seed M) (sourceRate seed M time) time := by
  have source := paired_derivative (E := H) (principal nu M) (principal_symmetric nu M)
    (NativeWindowHistoryDynamicHistory.residual_hasDerivAt seed M time)
  simpa only [energy,sourceRate] using! source

theorem common_response (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    kernelAction seed M time (embed (commonRate seed M time))=NativeWindowHistoryCommonResponse.response seed M 1 time := by
  apply Lp.ext
  filter_upwards [NativeWindowHistoryDynamicHistory.kernelAction_ae seed M time (embed (commonRate seed M time)),
    NativeWindowTraceWholeHistory.constant_ae (commonRate seed M time),
    NativeWindowHistoryCommonResponse.response_ae seed M 1 time] with lag acted constant original
  rw [acted,show embed (commonRate seed M time) lag=commonRate seed M time from constant,original]
  rfl

private def testImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K T : E →L[ℝ] E) (q : E) : E := q-T.adjoint (K.adjoint q)

def test (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) : H :=
  testImage (E := H) (kernelAction seed M time) (transposeAction seed M time) (principal nu M v)

def jointWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*inner ℝ (rateHistory seed M time) (test seed M time (temporalResponse seed M time))

theorem jointWork_source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    jointWork seed M time=2*inner ℝ
      (action seed M time (finiteHistory seed time M)+forcingHistory seed M time)
      (test seed M time (temporalResponse seed M time)) :=
  congrArg (fun v : H => 2*inner ℝ v (test seed M time (temporalResponse seed M time)))
    (NativeWindowHistoryOseen.source_equation seed M time)

private theorem signed_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K T : E →L[ℝ] E) (q a d : E) :
    2*inner ℝ q (a-K (T a+d))=
      2*inner ℝ a (q-T.adjoint (K.adjoint q))-2*inner ℝ q (K d) := by
  rw [map_add,inner_sub_right,inner_add_right,inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm a q,real_inner_comm (K (T a)) q]
  ring

theorem sourceRate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    sourceRate seed M time=jointWork seed M time-NativeWindowHistoryCommonResponseWork.work seed M 1 time := by
  have source := signed_pairing (E := H) (kernelAction seed M time) (transposeAction seed M time)
    (principal nu M (temporalResponse seed M time)) (rateHistory seed M time) (embed (commonRate seed M time))
  change sourceRate seed M time=jointWork seed M time-
    2*inner ℝ (principal nu M (temporalResponse seed M time)) (kernelAction seed M time (embed (commonRate seed M time))) at source
  exact source.trans (congrArg (fun v : H => jointWork seed M time-
    2*inner ℝ (principal nu M (temporalResponse seed M time)) v) (common_response seed M time))

private theorem abs_difference (a b c : ℝ) (same : a=b-c) : |a-b|=|c| := by
  rw [same,sub_sub_cancel_left,abs_neg]

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,
      |sourceRate seed M time-jointWork seed M time| ≤
        epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  obtain ⟨C,C0,paid⟩ := NativeWindowHistoryCommonResponseWork.source_work_bound seed horizon 1 epsilon positive
  refine ⟨C,C0,fun M time inside => ?_⟩
  exact (abs_difference _ _ _ (sourceRate_original seed M time)).trans_le (paid M time inside)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem energy_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    energy seed M (step.2.clockAdvance+time)=energy step.1 M time :=
  congrArg (fun v : H => inner ℝ v (principal nu M v))
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)

theorem sourceRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    sourceRate seed M (step.2.clockAdvance+time)=sourceRate step.1 M time :=
  congrArg₂ (fun v d : H => 2*inner ℝ (principal nu M v) d)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
    (NativeWindowHistoryDynamicHistory.residualRate_next seed M step generated time time0)

theorem jointWork_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    jointWork seed M (step.2.clockAdvance+time)=jointWork step.1 M time := by
  have same := congrArg₂ (fun a b : ℝ => a+b) (sourceRate_next seed M step generated time time0)
    (NativeWindowHistoryCommonResponseWork.work_next seed M 1 step generated time time0)
  simpa only [sourceRate_original,sub_add_cancel] using same

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicEnergy

import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.CenteredMeanWork
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Net

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCenteredNet
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action forcingHistory rateHistory)
open NativeWindowHistoryMeanProjection (mean embed residual)
open NativeWindowHistorySchurTemporalControl (temporalResponse temporalBudget)
open NativeWindowHistoryJacobianControl (form heat jacobian)
open NativeWindowHistoryDynamicEnergy (jointWork sourceRate)
open NativeWindowHistoryJacobianViscous (diagonal commutatorWork retainedWork)
noncomputable section
variable {nu : Viscosity}

def centeredRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  residual (rateHistory seed M time)

theorem centeredRate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    centeredRate seed M time=residual (action seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)+
      forcingHistory seed M time) :=
  congrArg residual (NativeWindowHistoryOseen.source_equation seed M time)

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  2*form nu M (temporalResponse seed M time) (jacobian seed M time (centeredRate seed M time))

private theorem adjoint_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G J : E →L[ℝ] E) (symmetric : ∀ u v,inner ℝ u (G v)=inner ℝ v (G u)) (w q : E) :
    2*inner ℝ w (G (J q))=2*inner ℝ q (J.adjoint (G w)) := by
  rw [ContinuousLinearMap.adjoint_inner_right,symmetric]

theorem work_test (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    work seed M time=2*inner ℝ (centeredRate seed M time)
      (NativeWindowHistoryDynamicEnergy.test seed M time (temporalResponse seed M time)) := by
  have first := adjoint_pair (E := H) (heat nu M) (jacobian seed M time)
    (NativeWindowHistoryJacobianControl.form_symmetric nu M) (temporalResponse seed M time) (centeredRate seed M time)
  exact first.trans (congrArg (fun t : H => 2*inner ℝ (centeredRate seed M time) t)
    (NativeWindowHistoryJacobianControl.source_test seed M time))

theorem work_source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    work seed M time=2*inner ℝ
      (action seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)+forcingHistory seed M time)
      (residual (NativeWindowHistoryDynamicEnergy.test seed M time (temporalResponse seed M time))) :=
  (work_test seed M time).trans ((congrArg (fun q : H => 2*inner ℝ q
    (NativeWindowHistoryDynamicEnergy.test seed M time (temporalResponse seed M time))) (centeredRate_original seed M time)).trans
      (congrArg (2*·) (NativeWindowHistoryMeanProjection.residual_symmetric _ _)))

private theorem pair_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G J : E →L[ℝ] E) (w a b : E) :
    2*inner ℝ w (G (J (a+b)))=2*inner ℝ w (G (J a))+2*inner ℝ w (G (J b)) := by
  rw [map_add,map_add,inner_add_right,mul_add]

theorem joint_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    jointWork seed M time=NativeWindowHistoryAdjointMeanWork.work seed M time+work seed M time := by
  have split : rateHistory seed M time=NativeWindowHistoryAdjointMeanWork.meanRate seed M time+centeredRate seed M time :=
    (NativeWindowHistoryMeanProjection.split (rateHistory seed M time)).symm
  have original := (NativeWindowHistoryJacobianViscous.joint_read seed M time).trans
    (congrArg (fun q : H => 2*form nu M (temporalResponse seed M time) (jacobian seed M time q)) split)
  apply original.trans
  simpa only [form,work,NativeWindowHistoryAdjointMeanWork.work] using!
    pair_sum (E := H) (heat nu M) (jacobian seed M time) (temporalResponse seed M time)
      (NativeWindowHistoryAdjointMeanWork.meanRate seed M time) (centeredRate seed M time)

theorem net_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    diagonal seed M time (temporalResponse seed M time)+commutatorWork seed M time (temporalResponse seed M time)+
      retainedWork seed M time+NativeWindowHistoryDynamicResponse.reactionWork seed M time-work seed M time=
        NativeWindowHistoryAdjointMeanWork.work seed M time := by
  have first := NativeWindowHistoryJacobianViscous.joint_split seed M time
  have reaction := NativeWindowHistoryJacobianViscous.reaction_split seed M time
  have actual := joint_split seed M time
  linarith only [first,reaction,actual]

theorem source_reduction (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time ∈ Icc 0 horizon,
      |sourceRate seed M time-work seed M time| ≤ C := by
  obtain ⟨low,B,B0,meanPaid⟩ := NativeWindowHistoryAdjointMeanWork.source_work_bound seed horizon nonnegative
  refine ⟨low,B+temporalBudget seed horizon+NativeWindowHistoryCommonForceBounds.budget seed horizon 1,
    add_nonneg (add_nonneg B0 (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon))
      (NativeWindowHistoryCommonForceBounds.budget_nonnegative seed horizon 1),?_⟩
  intro M above time inside
  have original := NativeWindowHistoryDynamicEnergy.sourceRate_original seed M time
  have split := joint_split seed M time
  have same : sourceRate seed M time-work seed M time=NativeWindowHistoryAdjointMeanWork.work seed M time-
      NativeWindowHistoryCommonResponseWork.work seed M 1 time := by linarith only [original,split]
  rw [same]
  exact (abs_sub _ _).trans ((add_le_add (meanPaid M above time inside)
    (NativeWindowHistoryDynamicNet.source_common_work_bound seed horizon M 1 time inside)).trans_eq (by ring))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem centeredRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    centeredRate seed M (step.2.clockAdvance+time)=centeredRate step.1 M time :=
  congrArg residual (NativeWindowHistoryOseen.rateHistory_next seed M step generated time time0)

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    work seed M (step.2.clockAdvance+time)=work step.1 M time :=
  congrArg₂ (fun w q : H => 2*form nu M w q)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
    (congrArg₂ (fun (J : H →L[ℝ] H) (q : H) => J q)
      (NativeWindowHistoryJacobianControl.jacobian_next seed M step generated time time0) (centeredRate_next seed M step generated time time0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCenteredNet

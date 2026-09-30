import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.AdjointHeatSource
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.CenteredNet

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointDefect
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action adjoint)
open NativeWindowHistoryDynamicHistory (kernelAction)
open NativeWindowHistoryJacobianControl (form heat)
open NativeWindowHistoryAdjointHeatSource (pullback)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse temporalBudget)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowTraceWholeHistory (projected)
noncomputable section
variable {nu : Viscosity}

def advection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  NativeWindowHistorySchurAdvectorAction.xAction seed M time+NativeWindowHistorySchurAdvectorAction.wAction seed M time

private theorem convection_split {E : Type*} [AddCommGroup E] (a d x y : E) (same : a= -d+x+y) : x+y=a+d := by
  rw [same]
  abel

theorem advection_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    advection seed M time v=action seed M time v+nu.coeff • laplacianAction nu M v := by
  have source := congrArg (fun A : H →L[ℝ] H => A v)
    (NativeWindowHistorySchurAdvectorAction.source_action_split seed M time)
  have diff := (NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M v).trans (neg_smul nu.coeff (laplacianAction nu M v))
  have original := source.trans (congrArg (fun d : H => d+NativeWindowHistorySchurAdvectorAction.xAction seed M time v+
    NativeWindowHistorySchurAdvectorAction.wAction seed M time v) diff)
  exact convection_split (E := H) _ _ _ _ original

private theorem dual_split {E : Type*} [AddCommGroup E] (a b d n : E)
    (sum : a+b= -d-d) (read : n=a+d) : b= -d-n := by
  calc
    b=(a+b)-a := by abel
    _=(-d-d)-a := congrArg (fun x : E => x-a) sum
    _= -d-(a+d) := by abel
    _= -d-n := congrArg (fun x : E => -d-x) read.symm

theorem dual_advection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    adjoint seed M time v= -(nu.coeff • laplacianAction nu M v)-advection seed M time v := by
  have diff := (NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M v).trans (neg_smul nu.coeff (laplacianAction nu M v))
  have doubled := congrArg (fun d : H => d+d) diff
  have source := (NativeWindowHistoryMeanBlocks.action_sum seed M time v).trans
    ((two_smul ℝ ((NativeWindowHistoryMeanBlocks.diffusion nu M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure v)).trans doubled)
  apply dual_split (E := H) _ _ _ _ _ (advection_original seed M time v)
  exact source.trans (by abel)

def defect (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) : H :=
  projected M v-pullback seed M time v

theorem projected_heat (nu : Viscosity) (M : ℕ) (v : H) :
    projected M (heat nu M v)=heat nu M (projected M v) := by
  have same := NativeWindowHistoryAdjointHeatSource.laplacian_projection nu M v
  have kept : projected M (laplacianAction nu M v)=laplacianAction nu M v := by
    apply Lp.ext
    filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL (laplacianAction nu M v),
      (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M).coeFn_compLpL v] with lag first last
    exact first.trans ((congrArg (NativeWindowTraceWholeHistory.projection M) last).trans
      ((NativeWindowHistoryOseenGap.projection_lift M _ (v lag)).trans last.symm))
  have distribute := ((NativeWindowTraceWholeHistory.projection M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure).map_add
    v (nu.coeff • laplacianAction nu M v)
  have scalar := ((NativeWindowTraceWholeHistory.projection M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure).map_smul
    nu.coeff (laplacianAction nu M v)
  exact distribute.trans ((congrArg (fun x : H => projected M v+x) scalar).trans
    (congrArg (fun x : H => projected M v+nu.coeff • x) (kept.trans same.symm)))

private theorem solve_defect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E) (u p d n : E) (heat : G p=p+d) (equation : p-(-d-n)=G u) : G (u-p)=n := by
  rw [map_sub,heat,← equation]
  abel

theorem defect_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    heat nu M (defect seed M time v)=advection seed M time (pullback seed M time v) := by
  let p := pullback seed M time v
  have equation := NativeWindowHistoryAdjointHeatKernel.adjoint_write seed M time (heat nu M v)
  have dual := dual_advection seed M time p
  have rewritten := (congrArg (fun a : H => p-a) dual).symm.trans (equation.trans (projected_heat nu M v))
  simpa only [defect,p] using! solve_defect (E := H) (heat nu M) (projected M v) p
    (nu.coeff • laplacianAction nu M p) (advection seed M time p) rfl rewritten

private theorem difference_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E) (p v : E) (same : inner ℝ p (G p)=inner ℝ p (G v)) :
    inner ℝ p (G (v-p))=0 := by rw [map_sub,inner_sub_right,← same,sub_self]

theorem orthogonal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    form nu M (pullback seed M time v) (defect seed M time v)=0 := by
  have source := NativeWindowHistoryAdjointHeatSource.pullback_energy seed M time (projected M v)
  rw [NativeWindowHistoryAdjointHeatSource.input_projection] at source
  have same := (NativeWindowHistoryJacobianControl.form_self nu M (pullback seed M time v)).trans source
  simpa only [form,defect] using! difference_pair (E := H) (heat nu M) (pullback seed M time v) (projected M v) same

private theorem energy_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E) (symmetric : ∀ u v,inner ℝ u (G v)=inner ℝ v (G u))
    (p z : E) (perpendicular : inner ℝ p (G z)=0) :
    inner ℝ (p+z) (G (p+z))=inner ℝ p (G p)+inner ℝ z (G z) := by
  simp only [map_add,inner_add_left,inner_add_right,perpendicular,symmetric z p,add_zero,zero_add]

theorem pythagoras (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    energy nu M (pullback seed M time v)+energy nu M (defect seed M time v)=energy nu M (projected M v) := by
  have perpendicular : inner ℝ (pullback seed M time v) (heat nu M (defect seed M time v))=0 := by
    simpa only [form] using! orthogonal seed M time v
  have split : ∀ p z : H,inner ℝ p (heat nu M z)=0 →
      inner ℝ (p+z) (heat nu M (p+z))=inner ℝ p (heat nu M p)+inner ℝ z (heat nu M z) := by
    simpa only [] using! energy_split (E := H) (heat nu M) (NativeWindowHistoryJacobianControl.form_symmetric nu M)
  have source := split (pullback seed M time v) (defect seed M time v) perpendicular
  have sum : pullback seed M time v+defect seed M time v=projected M v := by unfold defect; abel
  change form nu M (pullback seed M time v+defect seed M time v) (pullback seed M time v+defect seed M time v)=
    form nu M (pullback seed M time v) (pullback seed M time v)+form nu M (defect seed M time v) (defect seed M time v) at source
  have normalized : energy nu M (pullback seed M time v+defect seed M time v)=
      energy nu M (pullback seed M time v)+energy nu M (defect seed M time v) := by
    simpa only [NativeWindowHistoryJacobianControl.form_self] using source
  exact normalized.symm.trans (congrArg (energy nu M) sum)

def source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  defect seed M time (temporalResponse seed M time)

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) : energy nu M (source seed M time) ≤ temporalBudget seed horizon := by
  have source := pythagoras seed M time (temporalResponse seed M time)
  rw [NativeWindowHistoryDynamicEnergy.residual_projected] at source
  have positive := NativeWindowHistorySchurTemporalControl.energy_nonnegative seed M (pullback seed M time (temporalResponse seed M time))
  have paid := NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  change energy nu M (defect seed M time (temporalResponse seed M time)) ≤ _
  linarith only [source,positive,paid]

theorem source_advection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    advection seed M time (NativeWindowHistoryAdjointHeatSource.source seed M time)=heat nu M (source seed M time) :=
  (defect_equation seed M time (temporalResponse seed M time)).symm

theorem source_weak_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time ∈ Icc 0 horizon) (epsilon : ℝ) (positive : 0 < epsilon) (v : H) :
    |2*inner ℝ v (advection seed M time (NativeWindowHistoryAdjointHeatSource.source seed M time))| ≤
      epsilon*energy nu M v+temporalBudget seed horizon/epsilon := by
  have first := NativeWindowHistoryJacobianControl.form_young seed M v (source seed M time) epsilon
  have last := NativeWindowHistoryJacobianControl.form_young seed M v (source seed M time) (-epsilon)
  have paid := source_bound seed horizon M time inside
  rw [source_advection]
  apply abs_le.mpr
  constructor
  · have cancel : (epsilon*energy nu M v+temporalBudget seed horizon/epsilon)*epsilon=
        epsilon^2*energy nu M v+temporalBudget seed horizon := by field_simp
    change -(epsilon*energy nu M v+temporalBudget seed horizon/epsilon) ≤ 2*form nu M v (source seed M time)
    apply (mul_le_mul_iff_left₀ positive).mp
    nlinarith only [last,paid,cancel]
  · have cancel : (epsilon*energy nu M v+temporalBudget seed horizon/epsilon)*epsilon=
        epsilon^2*energy nu M v+temporalBudget seed horizon := by field_simp
    change 2*form nu M v (source seed M time) ≤ _
    apply (mul_le_mul_iff_left₀ positive).mp
    nlinarith only [first,paid,cancel]

theorem source_test (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryDynamicEnergy.test seed M time (temporalResponse seed M time)=
      heat nu M (NativeWindowHistoryAdjointHeatSource.source seed M time)+
        advection seed M time (NativeWindowHistoryAdjointHeatSource.source seed M time)-
      ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)
        (NativeWindowHistorySchurTranspose.transposeAction seed M time) (NativeWindowHistoryAdjointHeatSource.source seed M time) := by
  have sourceRead : source seed M time=temporalResponse seed M time-NativeWindowHistoryAdjointHeatSource.source seed M time :=
    congrArg (fun w : H => w-NativeWindowHistoryAdjointHeatSource.source seed M time)
      (NativeWindowHistoryDynamicEnergy.residual_projected seed M time)
  have nonlinear := (source_advection seed M time).trans ((congrArg (heat nu M) sourceRead).trans (map_sub _ _ _))
  have sum : heat nu M (temporalResponse seed M time)=heat nu M (NativeWindowHistoryAdjointHeatSource.source seed M time)+
      advection seed M time (NativeWindowHistoryAdjointHeatSource.source seed M time) := by rw [nonlinear]; abel
  have principal : NativeWindowHistoryDynamicEnergy.principal nu M (temporalResponse seed M time)=
      heat nu M (temporalResponse seed M time) := by
    exact congrArg (fun w : H => w+nu.coeff • laplacianAction nu M (temporalResponse seed M time))
      (NativeWindowHistoryDynamicEnergy.residual_projected seed M time)
  exact (NativeWindowHistoryAdjointHeatSource.test_original seed M time (temporalResponse seed M time)).trans
    (congrArg (fun x : H => x-ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)
      (NativeWindowHistorySchurTranspose.transposeAction seed M time) (NativeWindowHistoryAdjointHeatSource.source seed M time))
      (principal.trans sum))

private theorem test_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G T : E →L[ℝ] E) (q p n : E) :
    2*inner ℝ q (G p+n-T.adjoint p)=2*inner ℝ q (G p)+2*inner ℝ q n-2*inner ℝ (T q) p := by
  rw [inner_sub_right,inner_add_right,ContinuousLinearMap.adjoint_inner_right]
  ring

theorem centered_work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryCenteredNet.work seed M time=
      2*form nu M (NativeWindowHistoryCenteredNet.centeredRate seed M time) (NativeWindowHistoryAdjointHeatSource.source seed M time)+
      2*inner ℝ (NativeWindowHistoryCenteredNet.centeredRate seed M time)
        (advection seed M time (NativeWindowHistoryAdjointHeatSource.source seed M time))-
      2*inner ℝ (NativeWindowHistorySchurTranspose.transposeAction seed M time (NativeWindowHistoryCenteredNet.centeredRate seed M time))
        (NativeWindowHistoryAdjointHeatSource.source seed M time) := by
  have original := (NativeWindowHistoryCenteredNet.work_test seed M time).trans
    (congrArg (fun t : H => 2*inner ℝ (NativeWindowHistoryCenteredNet.centeredRate seed M time) t) (source_test seed M time))
  apply original.trans
  simpa only [form] using! test_pair (E := H) (heat nu M) (NativeWindowHistorySchurTranspose.transposeAction seed M time)
    (NativeWindowHistoryCenteredNet.centeredRate seed M time) (NativeWindowHistoryAdjointHeatSource.source seed M time)
    (advection seed M time (NativeWindowHistoryAdjointHeatSource.source seed M time))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem defect_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) (v : H) :
    defect seed M (step.2.clockAdvance+time) v=defect step.1 M time v :=
  congrArg (fun p : H => projected M v-p) (NativeWindowHistoryAdjointHeatSource.pullback_next seed M step generated time time0 v)

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    source seed M (step.2.clockAdvance+time)=source step.1 M time :=
  (defect_next seed M step generated time time0 (temporalResponse seed M (step.2.clockAdvance+time))).trans
    (congrArg (defect step.1 M time) (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointDefect

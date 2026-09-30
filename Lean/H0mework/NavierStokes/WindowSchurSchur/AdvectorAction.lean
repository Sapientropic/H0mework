import H0mework.NavierStokes.WindowSchurSchur.AdvectorFiber
import H0mework.NavierStokes.WindowHistoryAnnihilation.Control

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurAdvectorAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeWindowHistorySchurAdvectorFiber (family xProfile wProfile)
open NativeWindowHistoryAnnihilationControl (laplacianAction graphCost)
open NativeWindowHistoryCreationGeometry (transport square)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def xAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (family nu M).holderL averageMeasure ∞ 2 2 (xProfile seed M time)

def wAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (family nu M).holderL averageMeasure ∞ 2 2 (wProfile seed M time)

theorem xAction_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    xAction seed M time r=ᵐ[averageMeasure] fun lag => family nu M (completion seed M time lag) (r lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (family nu M) (xProfile seed M time) r,NativeWindowHistorySchurAdvectorFiber.xProfile_ae seed M time]
    with lag applied source
  change xAction seed M time r lag=family nu M (xProfile seed M time lag) (r lag) at applied
  rw [applied,source]

theorem wAction_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    wAction seed M time r=ᵐ[averageMeasure] fun lag => family nu M (temporalResponse seed M time lag) (r lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (family nu M) (wProfile seed M time) r,NativeWindowHistorySchurAdvectorFiber.wProfile_ae seed M time]
    with lag applied source
  change wAction seed M time r lag=family nu M (wProfile seed M time lag) (r lag) at applied
  rw [applied,source]

theorem source_action_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    action seed M time=(diffusion nu M).compLpL 2 averageMeasure+xAction seed M time+wAction seed M time := by
  apply ContinuousLinearMap.ext
  intro r
  apply Lp.ext
  filter_upwards [NativeWindowHistoryOseen.action_ae seed M time r,
    (diffusion nu M).coeFn_compLpL r,xAction_ae seed M time r,wAction_ae seed M time r,
    Lp.coeFn_add ((diffusion nu M).compLpL 2 averageMeasure r) (xAction seed M time r),
    Lp.coeFn_add ((diffusion nu M).compLpL 2 averageMeasure r+xAction seed M time r) (wAction seed M time r),
    NativeWindowHistoryOseen.history_original seed M time,Lp.coeFn_add (completion seed M time) (temporalResponse seed M time)]
    with lag actual heat x w first last original added
  have native:=congrArg (fun h : H => h lag) (NativeWindowHistorySchurCompletion.source_split seed M time)
  rw [original,added,Pi.add_apply] at native
  change action seed M time r lag=(((diffusion nu M).compLpL 2 averageMeasure r+xAction seed M time r)+wAction seed M time r) lag
  have evaluated:(((diffusion nu M).compLpL 2 averageMeasure r+xAction seed M time r)+wAction seed M time r) lag=
      diffusion nu M (r lag)+family nu M (completion seed M time lag) (r lag)+family nu M (temporalResponse seed M time lag) (r lag) :=
    last.trans (congrArg₂ (fun a b : wholePhysical => a+b)
      (first.trans (congrArg₂ (fun a b : wholePhysical => a+b) heat x)) w)
  have source:=NativeWindowHistorySchurAdvectorFiber.family_source seed M (time-lag) (r lag)
  have sourceRead:family nu M (NativeWindowHistoryOseen.velocityPath seed M (time-lag)) (r lag)=
      family nu M (completion seed M time lag) (r lag)+family nu M (temporalResponse seed M time lag) (r lag) :=
    (congrArg (fun u : wholePhysical => family nu M u (r lag)) native).trans
      (congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A (r lag)) ((family nu M).map_add _ _))
  exact actual.trans (source.symm.trans ((congrArg (fun u : wholePhysical => diffusion nu M (r lag)+u) sourceRead).trans
    ((show diffusion nu M (r lag)+(family nu M (completion seed M time lag) (r lag)+family nu M (temporalResponse seed M time lag) (r lag))=
      diffusion nu M (r lag)+family nu M (completion seed M time lag) (r lag)+family nu M (temporalResponse seed M time lag) (r lag) by abel).trans evaluated.symm)))

theorem transport_graph_bound (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M))
    (B epsilon : ℝ) (positive : 0 < epsilon)
    (coefficient : ‖NativeWindowStressHeatSource.physical (square (modes M) u)‖ ≤ B) :
    ‖coefficients (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu u v)‖^2 ≤
      epsilon*pairing (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
        (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)+
      NativeWindowHistoryCreationForm.budget B (epsilon*(2*Real.pi)^2)*curlPair (modes M) v.1 v.1 := by
  have paid:=(NativeWindowHistoryCreationGeometry.transport_bound (modes M) (modes_zero M) (modes_closed M) nu u v).trans
    (NativeWindowHistoryCreationGeometry.gradient_absorption _ (modes M) (modes_zero M) (modes_closed M) nu v epsilon positive)
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left coefficient (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have budget:NativeWindowHistoryCreationForm.budget ‖NativeWindowStressHeatSource.physical (square (modes M) u)‖ (epsilon*(2*Real.pi)^2) ≤
      NativeWindowHistoryCreationForm.budget B (epsilon*(2*Real.pi)^2) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  exact paid.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right budget (NativeWindowHistorySchurSampleControl.gradient_nonnegative M v)))

theorem source_graph_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,∀ r : H,
      ‖xAction seed M time r‖^2 ≤ epsilon*‖laplacianAction nu M r‖^2+C*gradient M r := by
  obtain ⟨low,B,B0,paid⟩:=NativeWindowHistorySchurAdvectorFiber.source_square_bound seed horizon nonnegative
  let C:=NativeWindowHistoryCreationForm.budget B (epsilon*(2*Real.pi)^2)
  have C0:0 ≤ C:=by unfold C NativeWindowHistoryCreationForm.budget; positivity
  refine ⟨low,C,C0,fun M above time inside r => ?_⟩
  let rows:=fun lag => ‖family nu M (completion seed M time lag) (r lag)‖^2
  have rowPaid:Integrable rows averageMeasure := by
    apply ((Lp.memLp (xAction seed M time r)).integrable_norm_pow (by decide : (2 : ℕ)≠0)).congr
    filter_upwards [xAction_ae seed M time r] with lag original
    rw [original]
  have graphPaid:=NativeWindowHistoryAnnihilationControl.graph_integrable nu M r
  have gradientPaid:=NativeWindowTraceWholeHistory.gradient_integrable nu M r
  have bound:=integral_mono_ae rowPaid ((graphPaid.const_mul epsilon).add (gradientPaid.const_mul C)) (by
    filter_upwards [paid M above time inside] with lag coefficient
    change rows lag ≤ epsilon*graphCost nu M r lag+C*curlPair (modes M)
      (NativeWindowHistoryAnnihilationRows.input M r lag).1 (NativeWindowHistoryAnnihilationRows.input M r lag).1
    dsimp only [rows]
    rw [NativeWindowHistorySchurAdvectorFiber.family_original,include_norm (modes M) (modes_zero M)]
    exact transport_graph_bound nu M (NativeWindowHistorySchurSampleControl.sample seed M time lag)
      (NativeWindowHistoryAnnihilationRows.input M r lag) B epsilon positive coefficient)
  have native:‖xAction seed M time r‖^2=∫lag,rows lag ∂averageMeasure := by
    rw [NativeWindowTraceWholeHistory.norm_square]
    apply integral_congr_ae
    filter_upwards [xAction_ae seed M time r] with lag original
    rw [original]
  rw [native]
  simp only [Pi.add_apply] at bound
  rw [integral_add (graphPaid.const_mul epsilon) (gradientPaid.const_mul C),integral_const_mul,integral_const_mul] at bound
  exact bound.trans_eq (congrArg₂ (fun x y : ℝ => epsilon*x+C*y)
    (NativeWindowHistoryAnnihilationControl.laplacian_square nu M r).symm rfl)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem actions_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (xAction seed M (step.2.clockAdvance+time),wAction seed M (step.2.clockAdvance+time))=
      (xAction step.1 M time,wAction step.1 M time) := by
  simpa only [xAction,wAction] using! congrArg
    (fun profiles : Lp wholePhysical ∞ averageMeasure × Lp wholePhysical ∞ averageMeasure =>
      ((family nu M).holderL averageMeasure ∞ 2 2 profiles.1,(family nu M).holderL averageMeasure ∞ 2 2 profiles.2))
      (NativeWindowHistorySchurAdvectorFiber.profiles_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurAdvectorAction

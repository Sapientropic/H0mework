import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Momentum
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurCenteredGraph
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeWindowHistorySchurMomentum (xJoint)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

def centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H := Q (completion seed M time)

theorem centered_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    centered seed M time=NativeWindowHistorySchurAction.response seed M time (mean (finiteHistory seed time M)) :=
  NativeWindowHistorySchurCompletion.complete_residual seed M time _

theorem laplacian_center (nu : Viscosity) (M : ℕ) (v : H) :
    Q (laplacianAction nu M v)=laplacianAction nu M (Q v) :=
  NativeWindowHistoryMeanProjection.residual_comp (laplacianFiber nu M) v

theorem centered_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    centered seed M time+nu.coeff • laplacianAction nu M (centered seed M time)=Q (xJoint seed M time) := by
  have source:=congrArg Q (NativeWindowHistorySchurMomentum.xJoint_equation seed M time)
  have heat:Q ((diffusion nu M).compLpL 2 averageMeasure (completion seed M time))=
      (-nu.coeff) • laplacianAction nu M (centered seed M time) :=
    (NativeWindowHistoryMeanProjection.residual_comp (diffusion nu M) (completion seed M time)).trans
      (NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M (centered seed M time))
  have distribute:Q (xJoint seed M time)=centered seed M time-
      (-nu.coeff) • laplacianAction nu M (centered seed M time)-0 :=
    source.trans (((Q).map_sub _ _).trans (congrArg₂ (fun u v : H => u-v)
      (((Q).map_sub _ _).trans (congrArg₂ (fun u v : H => u-v) rfl heat))
      (NativeWindowHistorySchurCompletion.residual_embed (commonForce seed M time))))
  symm
  simpa only [sub_zero,neg_smul,sub_neg_eq_add] using! distribute

private theorem positive_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (positive : 0 < a) (z l f : E) (source : z+a • l=f) (green : 0 ≤ inner ℝ z l) :
    a^2*‖l‖^2 ≤ ‖f‖^2 := by
  have actual:=congrArg (fun v : E => ‖v‖^2) source
  rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,abs_of_pos positive,real_inner_smul_right] at actual
  nlinarith only [actual,sq_nonneg ‖z‖,mul_nonneg positive.le green]

theorem residual_norm_square (v : H) : ‖Q v‖^2 ≤ ‖v‖^2 := by
  have split:=NativeWindowMetricGraphGreen.mass_split v
  nlinarith only [split,sq_nonneg ‖mean v‖]

theorem centered_graph_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    nu.coeff^2*‖laplacianAction nu M (centered seed M time)‖^2 ≤ ‖xJoint seed M time‖^2 := by
  have green:0 ≤ inner ℝ (centered seed M time) (laplacianAction nu M (centered seed M time)) :=
    (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (centered seed M time)).trans_eq
      (NativeWindowMetricGraphHistory.history_gradient nu M (centered seed M time)).symm
  exact (positive_graph (E := H) nu.coeff nu.coeff_pos _ _ _ (centered_equation seed M time) green).trans
    (residual_norm_square (xJoint seed M time))

theorem source_centered_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖laplacianAction nu M (centered seed M time)‖^2 ≤ epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  have viscous:0 < nu.coeff^2:=sq_pos_of_pos nu.coeff_pos
  obtain ⟨low,C,C0,source⟩:=NativeWindowHistorySchurMomentum.source_joint_bound seed horizon nonnegative
    (nu.coeff^2*epsilon) (mul_pos viscous positive)
  refine ⟨low,C/nu.coeff^2,div_nonneg C0 viscous.le,fun M above time inside => ?_⟩
  have paid:=(centered_graph_bound seed M time).trans (source M above time inside)
  have cancel:nu.coeff^2*(C/nu.coeff^2)=C:=mul_div_cancel₀ _ viscous.ne'
  nlinarith only [paid,cancel,viscous]

theorem temporal_difference (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    temporalResponse seed M time=Q (finiteHistory seed time M)-centered seed M time := by
  exact (NativeWindowHistorySchurTemporalControl.temporal_original seed M time).trans
    (congrArg (fun v : H => Q (finiteHistory seed time M)-v) (centered_original seed M time).symm)

theorem residual_graph_bound (nu : Viscosity) (M : ℕ) (v : H) :
    ‖laplacianAction nu M (Q v)‖^2 ≤ ‖laplacianAction nu M v‖^2 :=
  (congrArg (fun u : H => ‖u‖^2) (laplacian_center nu M v)).symm.trans_le
    (residual_norm_square (laplacianAction nu M v))

private theorem difference_square {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have bound:=pow_le_pow_left₀ (norm_nonneg (a-b)) (norm_sub_le a b) 2
  nlinarith only [bound,sq_nonneg (‖a‖-‖b‖)]

theorem source_temporal_graph (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖laplacianAction nu M (temporalResponse seed M time)‖^2 ≤ 3*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  obtain ⟨low,C,C0,source⟩:=source_centered_bound seed horizon nonnegative (1/2) (by norm_num)
  refine ⟨low,2*C,mul_nonneg (by norm_num) C0,fun M above time inside => ?_⟩
  have original:laplacianAction nu M (temporalResponse seed M time)=
      laplacianAction nu M (Q (finiteHistory seed time M))-laplacianAction nu M (centered seed M time) :=
    (congrArg (laplacianAction nu M) (temporal_difference seed M time)).trans
      ((laplacianAction nu M).map_sub (Q (finiteHistory seed time M)) (centered seed M time))
  have paid:=(congrArg (fun v : H => ‖v‖^2) original).trans_le
    (difference_square (E := H) (laplacianAction nu M (Q (finiteHistory seed time M))) (laplacianAction nu M (centered seed M time)))
  have first:=residual_graph_bound nu M (finiteHistory seed time M)
  have last:=source M above time inside
  nlinarith only [paid,first,last]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem centered_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    centered seed M (step.2.clockAdvance+time)=centered step.1 M time :=
  congrArg Q (NativeWindowHistorySchurCompletion.completion_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurCenteredGraph

import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointHeatKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H action adjoint)
open NativeWindowHistoryDynamicHistory (kernelAction kernelAction_ae)
open NativeWindowTraceWholeHistory (projection projected gradient)
open NativeWindowHistorySchurTemporalControl (energy)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem projection_symmetric (M : ℕ) (u v : H) :
    inner ℝ (projected M u) v=inner ℝ u (projected M v) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(projection M).coeFn_compLpL u,(projection M).coeFn_compLpL v] with lag first last
  exact (congrArg (fun x : wholePhysical => inner ℝ x (v lag)) first).trans
    ((NativeWindowHistoryDynamicTest.projection_symmetric M (u lag) (v lag)).trans
      (congrArg (fun x : wholePhysical => inner ℝ (u lag) x) last.symm))

theorem kernel_projection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    kernelAction seed M time (projected M v)=kernelAction seed M time v := by
  apply Lp.ext
  filter_upwards [kernelAction_ae seed M time (projected M v),kernelAction_ae seed M time v,
    (projection M).coeFn_compLpL v] with lag first last source
  have point : projected M v lag=projection M (v lag) := source
  exact first.trans ((congrArg (NativeWindowHistoryFrozenInverse.kernel seed M (time-lag)) point).trans
    ((NativeWindowHistoryFrozenInverse.kernel_projection seed M (time-lag) (v lag)).trans last.symm))

theorem projected_kernel (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    projected M (kernelAction seed M time v)=kernelAction seed M time v := by
  apply Lp.ext
  filter_upwards [(projection M).coeFn_compLpL (kernelAction seed M time v),kernelAction_ae seed M time v] with lag first last
  exact first.trans ((congrArg (projection M) last).trans
    ((NativeWindowHistoryFrozenInverse.kernel_projected seed M (time-lag) (v lag)).trans last.symm))

theorem kernel_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    kernelAction seed M time (v-action seed M time v)=projected M v := by
  apply Lp.ext
  filter_upwards [kernelAction_ae seed M time (v-action seed M time v),Lp.coeFn_sub v (action seed M time v),
    NativeWindowHistoryOseen.action_ae seed M time v,(projection M).coeFn_compLpL v] with lag solved sub original last
  have difference : (v-action seed M time v) lag=v lag-NativeWindowHistoryOseen.forwardFiber seed M (time-lag) (v lag) :=
    sub.trans (congrArg (fun x : wholePhysical => v lag-x) original)
  exact solved.trans ((congrArg (NativeWindowHistoryFrozenInverse.kernel seed M (time-lag)) difference).trans
    ((NativeWindowHistoryFrozenInverse.kernel_inverse seed M (time-lag) (v lag)).trans last.symm))

private theorem supported_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P K : E →L[ℝ] E) (symmetric : ∀ u v,inner ℝ (P u) v=inner ℝ u (P v))
    (supported : ∀ v,K (P v)=K v) (g : E) : P (K.adjoint g)=K.adjoint g := by
  apply ext_inner_left ℝ
  intro v
  rw [← symmetric,ContinuousLinearMap.adjoint_inner_right,supported,ContinuousLinearMap.adjoint_inner_right]

theorem adjoint_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (g : H) :
    projected M ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g)=(ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g := by
  simpa only [] using! supported_adjoint (E := H) ((projection M).compLpL 2 averageMeasure)
    (kernelAction seed M time) (projection_symmetric M) (kernel_projection seed M time) g

private theorem adjoint_support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P K : E →L[ℝ] E) (symmetric : ∀ u v,inner ℝ (P u) v=inner ℝ u (P v))
    (supported : ∀ v,P (K v)=K v) (g : E) : K.adjoint (P g)=K.adjoint g := by
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right,← symmetric,supported,ContinuousLinearMap.adjoint_inner_right]

theorem adjoint_projection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (g : H) :
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) (projected M g)=(ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g := by
  simpa only [] using! adjoint_support (E := H) ((projection M).compLpL 2 averageMeasure)
    (kernelAction seed M time) (projection_symmetric M) (projected_kernel seed M time) g

private theorem inverse_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P K A B : E →L[ℝ] E) (symmetric : ∀ u v,inner ℝ (P u) v=inner ℝ u (P v))
    (paired : ∀ u v,inner ℝ (A u) v=inner ℝ u (B v))
    (inverse : ∀ v,K (v-A v)=P v) (g : E) : K.adjoint g-B (K.adjoint g)=P g := by
  apply ext_inner_left ℝ
  intro v
  rw [inner_sub_right,← paired,← inner_sub_left,ContinuousLinearMap.adjoint_inner_right,inverse,symmetric]

theorem adjoint_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (g : H) :
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g-adjoint seed M time ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g)=projected M g := by
  simpa only [] using! inverse_adjoint (E := H) ((projection M).compLpL 2 averageMeasure)
    (kernelAction seed M time) (action seed M time) (adjoint seed M time) (projection_symmetric M)
    (NativeWindowHistoryOseen.action_adjoint seed M time) (kernel_inverse seed M time) g

private theorem diagonal_read {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p b : E) : inner ℝ p (p-b)=‖p‖^2-inner ℝ p b := by
  rw [inner_sub_right,real_inner_self_eq_norm_sq]

theorem adjoint_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (g : H) :
    energy nu M ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g)=inner ℝ ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g) g := by
  let p := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernelAction seed M time)) g
  have paired : inner ℝ p (adjoint seed M time p)=-nu.coeff*gradient M p :=
    (NativeWindowHistoryOseen.action_adjoint seed M time p p).symm.trans
      ((real_inner_comm (F := H) p (action seed M time p)).trans (NativeWindowHistoryOseenGap.action_energy seed M time p))
  have first := (congrArg (fun x : H => inner ℝ p x) (adjoint_write seed M time g)).symm.trans
    ((diagonal_read (E := H) p (adjoint seed M time p)).trans
      (congrArg (fun r : ℝ => ‖p‖^2-r) paired))
  have source : inner ℝ p (projected M g)=inner ℝ p g :=
    (projection_symmetric M p g).symm.trans
      (congrArg (fun x : H => inner ℝ x g) (adjoint_projected seed M time g))
  change energy nu M p=inner ℝ p g
  unfold energy
  linarith only [first,source]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointHeatKernel

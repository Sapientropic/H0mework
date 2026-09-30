import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.ForcedResponse

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalDissipation
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowHistoryCausalBath (propagate)
open NativeWindowHistoryCausalMean (residual)
open NativeWindowHistoryCausalForcedResponse (meanCurve createdResponse forcedResponse)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

private theorem zero_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : ℝ → E) (a B : ℝ) (_aB : a ≤ B) (initial : x a=0)
    (derivative : ∀t∈Icc a B,HasDerivWithinAt x 0 (Icc a B) t)
    (b : ℝ) (inside : b∈Icc a B) : x b=0 := by
  have continuous : ContinuousOn x (Icc a b) := fun t ht =>
    ((derivative t ⟨ht.1,ht.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have rate (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt x 0 t :=
    (derivative t ⟨ht.1.le,ht.2.le.trans inside.2⟩).hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le inside.2))
  have written:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 continuous rate (intervalIntegrable_const (c := (0:E)))
  simpa only [intervalIntegral.integral_zero,initial,sub_zero] using written.symm

private theorem centered_of_mean (v : H) (zero : mean v=0) : Q v=v := by
  change v-embed (mean v)=v
  rw [zero,map_zero,sub_zero]

theorem mean_bath (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) (v : H) : mean (bath seed M t v)=0 :=
  NativeWindowHistoryMeanProjection.mean_residual _

def freeResponse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) (t : ℝ) : H :=
  propagate seed M a B aB a t (residual seed M a)

theorem free_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) :
    freeResponse seed M a B aB a=residual seed M a :=
  congrArg (fun A : H →L[ℝ] H => A (residual seed M a))
    (NativeWindowHistoryCausalBath.propagate_initial seed M a B aB a (left_mem_Icc.mpr aB))

theorem free_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (t : ℝ) (inside : t∈Icc a B) : HasDerivWithinAt (freeResponse seed M a B aB)
      (bath seed M t (freeResponse seed M a B aB t)) (Icc a B) t :=
  NativeWindowHistoryCausalBath.propagate_derivative seed M a B aB a (residual seed M a) t inside

theorem free_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b∈Icc a B) : Q (freeResponse seed M a B aB b)=freeResponse seed M a B aB b := by
  have initial:mean (freeResponse seed M a B aB a)=0 :=
    (congrArg mean (free_initial seed M a B aB)).trans (NativeWindowHistoryMeanProjection.mean_residual _)
  have derivative (t : ℝ) (ht : t∈Icc a B) :
      HasDerivWithinAt (fun s => mean (freeResponse seed M a B aB s)) 0 (Icc a B) t := by
    have actual:=mean.hasFDerivAt.comp_hasDerivWithinAt t (free_derivative seed M a B aB t ht)
    exact actual.congr_deriv (mean_bath seed M t _)
  exact centered_of_mean _ (zero_curve _ a B aB initial derivative b inside)

private theorem map_two_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (u v : E)
    (first : L u=0) (last : L v=0) : L (u+v)=0 := by rw [map_add,first,last,add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem created_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b∈Icc a B) : Q (createdResponse seed M a B aB b)=createdResponse seed M a B aB b := by
  have initial:mean (createdResponse seed M a B aB a)=0 :=
    (congrArg mean (NativeWindowHistoryCausalForcedResponse.created_initial seed M a B aB)).trans (map_zero mean)
  have derivative (t : ℝ) (ht : t∈Icc a B) :
      HasDerivWithinAt (fun s => mean (createdResponse seed M a B aB s)) 0 (Icc a B) t := by
    have actual:=mean.hasFDerivAt.comp_hasDerivWithinAt t (NativeWindowHistoryCausalForcedResponse.created_derivative seed M a B aB t ht)
    exact actual.congr_deriv (map_two_zero (E := H) mean _ _ (mean_bath seed M t _)
      (NativeWindowHistoryMeanAction.creation_centered seed M t _))
  exact centered_of_mean _ (zero_curve _ a B aB initial derivative b inside)

private theorem mapped_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (u v w : E) (first : L u=u) (middle : L v=v) (last : L w=w) :
    L (u-v-w)=u-v-w := by rw [map_sub,map_sub,first,middle,last]

set_option backward.isDefEq.respectTransparency false in
theorem forced_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b∈Icc a B) : Q (forcedResponse seed M a B aB b)=forcedResponse seed M a B aB b := by
  simpa only [] using! mapped_three (E := H) Q (residual seed M b) (freeResponse seed M a B aB b)
    (createdResponse seed M a B aB b) (NativeWindowHistoryBathResolvent.residual_square (finiteHistory seed b M))
    (free_centered seed M a B aB b inside) (created_centered seed M a B aB b inside)

theorem gradient_continuous (nu : Viscosity) (M : ℕ) : Continuous (gradient M) :=
  (continuous_id.inner (𝕜 := ℝ) (NativeWindowHistoryAnnihilationControl.laplacianAction nu M).continuous).congr
    (NativeWindowMetricGraphHistory.history_gradient nu M)

private theorem quadratic_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (positive : ∀v,0 ≤ inner ℝ v (L v)) (v w : E) :
    inner ℝ (v-w) (L (v-w)) ≤ 2*inner ℝ v (L v)+2*inner ℝ w (L w) := by
  have nonnegative:=positive (v+w)
  simp only [map_sub,map_add,inner_sub_left,inner_sub_right,inner_add_left,inner_add_right] at nonnegative ⊢
  linarith only [nonnegative]

theorem gradient_sub (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v w : H) :
    gradient M (v-w) ≤ 2*gradient M v+2*gradient M w := by
  have positive (u : H) : 0 ≤ inner ℝ u (NativeWindowHistoryAnnihilationControl.laplacianAction nu M u) :=
    (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M u).trans_eq
      (NativeWindowMetricGraphHistory.history_gradient nu M u).symm
  simpa only [NativeWindowMetricGraphHistory.history_gradient] using! quadratic_sub (E := H)
    (NativeWindowHistoryAnnihilationControl.laplacianAction nu M) positive v w

set_option backward.isDefEq.respectTransparency false in
theorem energy_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (x f : ℝ → H)
    (a B : ℝ) (_aB : a ≤ B) (fc : ContinuousOn f (Icc a B))
    (derivative : ∀t∈Icc a B,HasDerivWithinAt x (bath seed M t (x t)+f t) (Icc a B) t)
    (centered : ∀t∈Icc a B,Q (x t)=x t) (b : ℝ) (inside : b∈Icc a B) :
    ‖x b‖^2+2*nu.coeff*(∫t in a..b,gradient M (x t))=
      ‖x a‖^2+2*(∫t in a..b,inner ℝ (f t) (x t)) := by
  have xc : ContinuousOn x (Icc a b) := fun t ht =>
    ((derivative t ⟨ht.1,ht.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have gc : IntervalIntegrable (fun t => gradient M (x t)) volume a b :=
    ((gradient_continuous nu M).comp_continuousOn xc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have work:=((fc.mono (Icc_subset_Icc le_rfl inside.2)).inner (𝕜 := ℝ) xc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have rate (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun s => ‖x s‖^2) ((-2*nu.coeff)*gradient M (x t)+2*inner ℝ (f t) (x t)) t := by
    have actual:=(derivative t ⟨ht.1.le,ht.2.le.trans inside.2⟩).hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le inside.2))
    convert! HasDerivAt.norm_sq (F := H) actual using 1
    rw [inner_add_right,NativeWindowHistoryBathResolvent.bath_energy,centered t ⟨ht.1.le,ht.2.le.trans inside.2⟩,
      real_inner_comm (x t) (f t)]
    ring
  have written:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 (xc.norm.pow 2) rate
    ((gc.const_mul (-2*nu.coeff)).add (work.const_mul 2))
  rw [intervalIntegral.integral_add (gc.const_mul (-2*nu.coeff)) (work.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at written
  simp only [Pi.pow_apply] at written
  linarith only [written]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalDissipation

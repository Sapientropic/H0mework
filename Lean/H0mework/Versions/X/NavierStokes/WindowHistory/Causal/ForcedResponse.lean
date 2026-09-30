import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Passivity
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Forcing

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalForcedResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H forcingHistory)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowHistoryCausalBath (kernel propagate)
open NativeWindowHistoryCausalMean (residual)
open NativeWindowHistoryCausalPassivity (creationResponse creationInput)
open NativeWindowHistorySchurTemporalControl (massBudget)
open NativeWholeResolvent (wholePhysical)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

private theorem inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f p : ℝ → E) (a b : ℝ) (ab : a≤b)
    (integrable : IntervalIntegrable f volume a b) (continuous : ContinuousOn p (Icc a b)) :
    IntervalIntegrable (fun t => inner ℝ (f t) (p t)) volume a b := by
  obtain ⟨C,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn continuous
  have first:=(intervalIntegrable_iff_integrableOn_Icc_of_le ab).mp integrable
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mpr
  refine (first.norm.mul_const C).mono' (first.aestronglyMeasurable.inner
    (continuous.aestronglyMeasurable measurableSet_Icc)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (norm_inner_le_norm (f t) (p t)).trans
    (mul_le_mul_of_nonneg_left (bounded t ht) (norm_nonneg _))

private theorem split_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r p c z : E) : inner ℝ (r-p-c) z=(inner ℝ r z-inner ℝ p z)-inner ℝ c z := by
  rw [inner_sub_left,inner_sub_left]

private theorem split_input {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c f z : E) : inner ℝ f z=inner ℝ (c+f) z-inner ℝ c z := by rw [inner_add_left]; ring

private theorem norm_from_square (x D : ℝ) (x0 : 0≤x) (D0 : 0≤D) (paid : x^2≤D) : x≤Real.sqrt D :=
  (sq_le_sq₀ x0 (Real.sqrt_nonneg D)).mp ((Real.sq_sqrt D0).symm ▸ paid)

private theorem norm_from_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (C : ℝ) (C0 : 0≤C) (paid : inner ℝ v v≤C*‖v‖) : ‖v‖≤C := by
  rw [real_inner_self_eq_norm_sq] at paid
  nlinarith [norm_nonneg v]

def meanCurve (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : wholePhysical := mean (finiteHistory seed t M)

theorem mean_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (meanCurve seed M) :=
  mean.continuous.comp (NativeWindowHistoryOseen.history_continuous seed M)

def createdResponse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) : ℝ → H :=
  creationResponse seed M (meanCurve seed M) (mean_continuous seed M) a B aB

def forcedResponse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : H :=
  residual seed M t-propagate seed M a B aB a t (residual seed M a)-createdResponse seed M a B aB t

theorem created_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) : createdResponse seed M a B aB a=0 :=
  NativeWindowHistoryCausalPassivity.bathResponse_initial seed M _ _ a B aB

theorem created_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (createdResponse seed M a B aB)
      (bath seed M t (createdResponse seed M a B aB t)+creation seed M t (meanCurve seed M t)) (Icc a B) t :=
  NativeWindowHistoryCausalPassivity.bathResponse_derivative seed M _ _ a B aB t inside

theorem created_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) (z : H) :
    inner ℝ (createdResponse seed M a B aB b) z=
      ∫ t in a..b,inner ℝ (creation seed M t (meanCurve seed M t)) (kernel seed M a B aB t b z) :=
  NativeWindowHistoryCausalPassivity.bathResponse_green seed M _ _ a B aB b inside z

theorem propagate_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (s b : ℝ) (v z : H) :
    inner ℝ (propagate seed M a B aB s b v) z=inner ℝ v (kernel seed M a B aB s b z) := by
  simpa only [propagate] using! ContinuousLinearMap.adjoint_inner_left (𝕜 := ℝ) (E := H) (F := H)
    (kernel seed M a B aB s b) z v

private theorem forcing_integral_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) (z : H) :
    (∫t in a..b,inner ℝ (Q (forcingHistory seed M t)) (kernel seed M a B aB t b z))=
      (∫t in a..b,inner ℝ (NativeWindowHistoryCausalMean.input seed M t) (kernel seed M a B aB t b z))-
        ∫t in a..b,inner ℝ (creation seed M t (meanCurve seed M t)) (kernel seed M a B aB t b z) := by
  let p:=fun t => kernel seed M a B aB t b z
  have pc : ContinuousOn p (Icc a b) := fun t ht =>
    ((NativeWindowHistoryCausalBath.kernel_derivative seed M a B aB b z t
      ⟨ht.1,ht.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have fc:=NativeWindowHistoryCausalPassivity.creationInput_continuous seed M (meanCurve seed M) (mean_continuous seed M)
  have total:=inner_integrable (E := H) (NativeWindowHistoryCausalMean.input seed M) p a b inside.1
    (NativeWindowHistoryCausalMean.input_integrable seed M a b) pc
  have formed:=inner_integrable (E := H) (creationInput seed M (meanCurve seed M)) p a b inside.1
    (fc.intervalIntegrable a b) pc
  have subtract : (∫t in a..b,inner ℝ (Q (forcingHistory seed M t)) (p t))=
      (∫t in a..b,inner ℝ (NativeWindowHistoryCausalMean.input seed M t) (p t))-
        ∫t in a..b,inner ℝ (creation seed M t (meanCurve seed M t)) (p t) := by
    calc
      _=∫t in a..b,(inner ℝ (NativeWindowHistoryCausalMean.input seed M t) (p t)-
        inner ℝ (creation seed M t (meanCurve seed M t)) (p t)) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact split_input (E := H) _ _ _
      _=_ := intervalIntegral.integral_sub total formed
  exact subtract

theorem forced_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) (z : H) :
    inner ℝ (forcedResponse seed M a B aB b) z=
      ∫ t in a..b,inner ℝ (Q (forcingHistory seed M t)) (kernel seed M a B aB t b z) := by
  have pair:=split_pair (E := H) (residual seed M b) (propagate seed M a B aB a b (residual seed M a))
    (createdResponse seed M a B aB b) z
  have propagated:=congrArg (fun q : ℝ => inner ℝ (residual seed M b) z-q)
    (propagate_pair seed M a B aB a b (residual seed M a) z)
  have full:=propagated.trans (NativeWindowHistoryCausalMean.source_green seed M a B aB b inside z)
  have reduced:=congrArg₂ (fun x y : ℝ => x-y) full (created_green seed M a B aB b inside z)
  exact pair.trans (reduced.trans (forcing_integral_split seed M a B aB b inside z).symm)

theorem forced_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) : forcedResponse seed M a B aB a=0 := by
  have initial:=congrArg (fun A : H →L[ℝ] H => A (residual seed M a))
    (NativeWindowHistoryCausalBath.propagate_initial seed M a B aB a (left_mem_Icc.mpr aB))
  simp only [forcedResponse,initial,ContinuousLinearMap.id_apply,created_initial,sub_self]

private theorem derivative_balance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (x y z : ℝ → E) (g f : E) (t : ℝ) (I : Set ℝ)
    (dx : HasDerivWithinAt x (A (x t)+(g+f)) I t)
    (dy : HasDerivWithinAt y (A (y t)) I t) (dz : HasDerivWithinAt z (A (z t)+g) I t) :
    HasDerivWithinAt (fun s => x s-y s-z s) (A (x t-y t-z t)+f) I t := by
  have actual:=(dx.sub dy).sub dz
  have same : A (x t)+(g+f)-A (y t)-(A (z t)+g)=A (x t-y t-z t)+f := by
    rw [map_sub,map_sub]
    abel
  have sameCurve : (fun s => x s-y s-z s)=x-y-z := by funext s; rfl
  rw [sameCurve]
  exact actual.congr_deriv same

set_option backward.isDefEq.respectTransparency false in
theorem forced_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (forcedResponse seed M a B aB)
      (bath seed M t (forcedResponse seed M a B aB t)+Q (forcingHistory seed M t)) (Icc a B) t := by
  simpa only [] using! derivative_balance (E := H) (bath seed M t) (residual seed M)
    (fun s => propagate seed M a B aB a s (residual seed M a)) (createdResponse seed M a B aB)
    (creation seed M t (meanCurve seed M t)) (Q (forcingHistory seed M t)) t (Icc a B)
    ((NativeWindowHistoryCausalMean.source_derivative seed M t).hasDerivWithinAt (s := Icc a B))
    (NativeWindowHistoryCausalBath.propagate_derivative seed M a B aB a (residual seed M a) t inside)
    (created_derivative seed M a B aB t inside)

theorem forced_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Ioo a B) :
    HasDerivAt (forcedResponse seed M a B aB)
      (bath seed M t (forcedResponse seed M a B aB t)+Q (forcingHistory seed M t)) t :=
  (forced_derivative seed M a B aB t (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)

theorem source_created_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      ‖createdResponse seed M a horizon start.2 b‖≤Real.sqrt D*(b-a) := by
  obtain ⟨D,D0,paid⟩:=NativeWindowHistoryCreationMean.source seed horizon
  refine ⟨D,D0,fun M a start b inside => ?_⟩
  let z:=createdResponse seed M a horizon start.2 b
  have point (t : ℝ) (ht : t∈uIoc a b) :
      ‖inner ℝ (creation seed M t (meanCurve seed M t)) (kernel seed M a horizon start.2 t b z)‖≤Real.sqrt D*‖z‖ := by
    rw [uIoc_of_le inside.1] at ht
    have formed:=norm_from_square _ D (norm_nonneg _) D0 (paid M t ⟨start.1.trans ht.1.le,ht.2.trans inside.2⟩)
    exact (norm_inner_le_norm (𝕜 := ℝ) (E := H) _ _).trans (mul_le_mul formed
      (NativeWindowHistoryCausalBath.kernel_contracts seed M a horizon start.2 b inside z t ⟨ht.1.le,ht.2⟩)
      (norm_nonneg _) (Real.sqrt_nonneg D))
  have integrated:=intervalIntegral.norm_integral_le_of_norm_le_const point
  rw [abs_of_nonneg (sub_nonneg.mpr inside.1),← created_green seed M a horizon start.2 b inside z,Real.norm_eq_abs] at integrated
  have bound : inner ℝ z z≤(Real.sqrt D*(b-a))*‖z‖ :=
    (le_abs_self _).trans (integrated.trans_eq (by ring))
  exact norm_from_self (E := H) z _ (mul_nonneg (Real.sqrt_nonneg D) (sub_nonneg.mpr inside.1)) bound

theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      ‖forcedResponse seed M a horizon start.2 b‖≤C := by
  obtain ⟨D,D0,created⟩:=source_created_bound seed horizon
  let R:=Real.sqrt (massBudget seed)
  have bounded (M : ℕ) (t : ℝ) (t0 : 0≤t) : ‖residual seed M t‖≤R :=
    norm_from_square _ _ (norm_nonneg _) (NativeWindowHistorySchurTemporalControl.massBudget_nonnegative seed)
      (NativeWindowHistoryCausalForcing.residual_bound seed M t t0)
  refine ⟨2*R+Real.sqrt D*horizon,by positivity,fun M a start b inside => ?_⟩
  have first:=bounded M b (start.1.trans inside.1)
  have initial:=(NativeWindowHistoryCausalBath.propagate_contracts seed M a horizon start.2 b inside
    (residual seed M a) a (left_mem_Icc.mpr inside.1)).trans (bounded M a start.1)
  have last:=(created M a start b inside).trans (mul_le_mul_of_nonneg_left
    (by linarith [start.1,inside.2] : b-a≤horizon) (Real.sqrt_nonneg D))
  have triangle:=(norm_sub_le (residual seed M b-propagate seed M a horizon start.2 a b (residual seed M a))
    (createdResponse seed M a horizon start.2 b)).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add first initial)) last)
  exact triangle.trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalForcedResponse

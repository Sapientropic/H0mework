import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Budget

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalForcing
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H forcingHistory)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryCausalBath (kernel)
open NativeWindowHistoryCausalMean (memory residual)
open NativeWindowHistoryCausalBudget (effect)
open NativeWindowHistorySchurTemporalControl (massBudget)
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeFiniteActionResolvent (physicalSpace pairing)
open NativeCommonAdvectorAction (curlPair)
open NativeWindowOperatorGreen (laplacian)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

private theorem abs_difference (x y : ℝ) : |x-y|≤|x|+|y| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le x y

private theorem product_bound (z x y D : ℝ) (bound : z≤x*y) (paid : x^2≤D) :
    z≤D+y^2 := by nlinarith only [bound,paid,sq_nonneg y,sq_nonneg (x-y)]

private theorem remainder (x y z : ℝ) (same : x=y+z) : z=x-y := by linarith only [same]

private theorem sum_budget (m d h z : ℝ) : m+z^2+(d+z^2)*h=m+h*d+(1+h)*z^2 := by ring

def forcing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (u : wholePhysical) : ℝ :=
  ∫ t in a..b,inner ℝ (Q (forcingHistory seed M t))
    (kernel seed M a B aB t b (creation seed M b u))

theorem residual_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time) :
    ‖residual seed M time‖^2≤ massBudget seed :=
  (NativeWindowHistorySchurCenteredGraph.residual_norm_square (finiteHistory seed time M)).trans
    (NativeWindowHistorySchurTemporalControl.source_mass seed M time nonnegative)

theorem memory_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B) (u : wholePhysical) :
    |memory seed M a B aB b u|≤ massBudget seed+‖creation seed M b u‖^2 := by
  have source:=NativeWindowHistoryCausalMean.source_green seed M a B aB b inside (creation seed M b u)
  change _=memory seed M a B aB b u at source
  have first:=abs_real_inner_le_norm (residual seed M b) (creation seed M b u)
  have last:=(abs_real_inner_le_norm (residual seed M a) (kernel seed M a B aB a b (creation seed M b u))).trans
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryCausalBath.kernel_contracts seed M a B aB b inside
      (creation seed M b u) a (left_mem_Icc.mpr inside.1)) (norm_nonneg _))
  have triangle:=abs_difference (inner ℝ (residual seed M b) (creation seed M b u))
    (inner ℝ (residual seed M a) (kernel seed M a B aB a b (creation seed M b u)))
  rw [source] at triangle
  nlinarith only [first,last,triangle,residual_bound seed M a a0,residual_bound seed M b (a0.trans inside.1),
    sq_nonneg (‖residual seed M a‖-‖creation seed M b u‖),sq_nonneg (‖residual seed M b‖-‖creation seed M b u‖)]

theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      |forcing seed M a horizon start.2 b (mean (finiteHistory seed b M))|≤C := by
  obtain ⟨D,D0,created⟩:=NativeWindowHistoryCreationMean.source seed horizon
  obtain ⟨K,K0,history⟩:=NativeWindowHistoryCausalBudget.source_created_bound seed horizon nonnegative
  refine ⟨massBudget seed+D+K,by positivity [NativeWindowHistorySchurTemporalControl.massBudget_nonnegative seed],?_⟩
  intro M a start b inside
  have full:=(memory_bound seed M a horizon start.2 start.1 b inside (mean (finiteHistory seed b M))).trans
    (add_le_add (le_refl (massBudget seed)) (created M b ⟨start.1.trans inside.1,inside.2⟩))
  have split:=NativeWindowHistoryCausalBudget.complete_memory seed M a horizon start.2 b inside
  change _=_+forcing seed M a horizon start.2 b (mean (finiteHistory seed b M)) at split
  have same:forcing seed M a horizon start.2 b (mean (finiteHistory seed b M))=
      memory seed M a horizon start.2 b (mean (finiteHistory seed b M))-
        NativeWindowHistoryCausalBudget.createdMemory seed M a horizon start.2 b := remainder _ _ _ split
  rw [same]
  exact (abs_difference _ _).trans (add_le_add full (history M a start b inside))

private theorem created_test_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,∀ u : wholePhysical,
      |∫t in a..b,effect seed M a horizon start.2 t b u (mean (finiteHistory seed t M))|≤
        (D+‖creation seed M b u‖^2)*horizon := by
  obtain ⟨D,D0,paid⟩:=NativeWindowHistoryCreationMean.source seed horizon
  refine ⟨D,D0,fun M a start b inside u => ?_⟩
  have point (t : ℝ) (ht : t∈uIoc a b) :
      ‖effect seed M a horizon start.2 t b u (mean (finiteHistory seed t M))‖≤D+‖creation seed M b u‖^2 := by
    rw [uIoc_of_le inside.1] at ht
    have bound:=NativeWindowHistoryCausalBudget.effect_bound seed M a horizon start.2 b inside t ⟨ht.1.le,ht.2⟩
      u (mean (finiteHistory seed t M))
    have formed:=paid M t ⟨start.1.trans ht.1.le,ht.2.trans inside.2⟩
    rw [Real.norm_eq_abs]
    exact product_bound _ _ _ D bound formed
  have integrated:=intervalIntegral.norm_integral_le_of_norm_le_const point
  rw [abs_of_nonneg (sub_nonneg.mpr inside.1),Real.norm_eq_abs] at integrated
  exact integrated.trans (mul_le_mul_of_nonneg_left
    (by linarith [start.1,inside.2] : b-a≤horizon) (add_nonneg D0 (sq_nonneg _)))

theorem forcing_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,∀ u : wholePhysical,
      |forcing seed M a horizon start.2 b u|≤ massBudget seed+horizon*D+(1+horizon)*‖creation seed M b u‖^2 := by
  obtain ⟨D,D0,paid⟩:=created_test_bound seed horizon
  refine ⟨D,D0,fun M a start b inside u => ?_⟩
  let I:=∫t in a..b,effect seed M a horizon start.2 t b u (mean (finiteHistory seed t M))
  have split:=NativeWindowHistoryCausalMean.memory_decomposition seed M a horizon start.2 b inside u
  change memory seed M a horizon start.2 b u=I+forcing seed M a horizon start.2 b u at split
  have same : forcing seed M a horizon start.2 b u=memory seed M a horizon start.2 b u-I := remainder _ _ _ split
  have triangle:=(abs_difference (memory seed M a horizon start.2 b u) I).trans
    (add_le_add (memory_bound seed M a horizon start.2 start.1 b inside u) (paid M a start b inside u))
  exact (congrArg abs same).trans_le (triangle.trans_eq (sum_budget _ _ _ _))

theorem source_form_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ)
    (nonnegative : 0≤horizon) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,∀ u : physicalSpace (modes M),
      |forcing seed M a horizon start.2 b (includeCLM (modes M) (modes_closed M) u)|≤
        epsilon*pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu u)
          (laplacian (modes M) (modes_zero M) (modes_closed M) nu u)+C*(curlPair (modes M) u.1 u.1+1) := by
  obtain ⟨D,D0,paid⟩:=forcing_bound seed horizon
  let δ:=epsilon/(1+horizon)
  have δ0 : 0<δ:=div_pos positive (by linarith)
  let B:=(1+horizon)*NativeWindowHistoryCreationSource.budget seed horizon δ
  let K:=massBudget seed+horizon*D
  have B0 : 0≤B:=mul_nonneg (by linarith) (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon δ δ0)
  have K0 : 0≤K:=add_nonneg (NativeWindowHistorySchurTemporalControl.massBudget_nonnegative seed) (mul_nonneg nonnegative D0)
  refine ⟨B+K,add_nonneg B0 K0,fun M a start b inside u => ?_⟩
  have full:=paid M a start b inside (includeCLM (modes M) (modes_closed M) u)
  have created:=NativeWindowHistoryCreationSource.source_creation_bound seed horizon δ δ0 M b
    ⟨start.1.trans inside.1,inside.2⟩ u
  have scaled:=mul_le_mul_of_nonneg_left created (show 0≤1+horizon by linarith)
  have cancel : (1+horizon)*δ=epsilon:=mul_div_cancel₀ _ (show 1+horizon≠0 by linarith)
  have grad0 : 0≤curlPair (modes M) u.1 u.1 := by
    rw [NativeWindowHistoryCreationGeometry.curl_mass (modes M) (modes_zero M)]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => mul_nonneg
      (ThreeDimensionalVorticityCoefficientRawSourceCore.integerWaveNormSq_nonneg k)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have reduced : (1+horizon)*‖creation seed M b (includeCLM (modes M) (modes_closed M) u)‖^2≤
      epsilon*pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu u)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu u)+B*curlPair (modes M) u.1 u.1 := by
    simpa only [mul_add,← mul_assoc,cancel,B] using scaled
  have extra:=mul_nonneg K0 grad0
  dsimp only [B,K] at B0 K0 extra reduced ⊢
  nlinarith only [full,reduced,extra,B0]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem forcing_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B) (u : wholePhysical) :
    forcing seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+b) u=forcing step.1 M a B aB b u := by
  unfold forcing
  rw [← intervalIntegral.integral_comp_add_left _ step.2.clockAdvance]
  apply intervalIntegral.integral_congr
  intro t ht
  have sample : t∈Icc a b:=by simpa only [uIcc_of_le inside.1] using ht
  have force:=congrArg Q (NativeWindowHistoryOseen.forcingHistory_next seed M step generated t (a0.trans sample.1))
  have source:=congrArg (fun A : wholePhysical →L[ℝ] H => A u)
    (NativeWindowHistoryMeanBlocks.creation_next seed M step generated b (a0.trans inside.1))
  have moved:=congrArg₂ (fun (A : H →L[ℝ] H) (v : H) => A v)
    (NativeWindowHistoryCausalBath.kernel_next seed M step generated a B aB a0 b inside t sample) source
  exact congrArg₂ (inner ℝ) force moved

theorem source_forcing_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B) :
    forcing seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+b) (mean (finiteHistory seed (step.2.clockAdvance+b) M))=
      forcing step.1 M a B aB b (mean (finiteHistory step.1 b M)) := by
  have same:=congrArg mean (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated b (a0.trans inside.1) M)
  exact (congrArg (forcing seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
    (step.2.clockAdvance+b)) same).trans (forcing_next seed M step generated a B aB a0 b inside _)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalForcing

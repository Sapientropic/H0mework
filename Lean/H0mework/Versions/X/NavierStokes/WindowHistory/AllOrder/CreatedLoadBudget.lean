import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.CreatedLoadTranspose
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Energy

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCreatedLoadBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient finiteHistory)
open NativeWindowHistorySpatialWords (history operator rate fiber)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created load)
open NativeWindowHistoryOseen (action)
open NativeWindowHistoryAllOrderCreatedLoadTranspose (pairing transpose inputBudget)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

theorem history_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) :
    Continuous (history seed M word) := continuous_iff_continuousAt.mpr fun t =>
  (NativeWindowHistorySpatialWords.source_hasDerivAt seed M word t).continuousAt

theorem load_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) :
    load seed M word t=rate seed M word t-action seed M t (history seed M word t) := by
  rw [NativeWindowHistorySpatialWords.rate_original]
  dsimp only [load]
  abel

theorem load_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (a b : ℝ) :
    IntervalIntegrable (load seed M word) volume a b := by
  have raw:=NativeWindowHistoryOseen.rateHistory_integrable seed M a b
  have mapped : IntervalIntegrable (rate seed M word) volume a b :=
    ⟨by simpa only [] using! (operator M word).integrable_comp (H := H) (E := H) (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) raw.1,
      by simpa only [] using! (operator M word).integrable_comp (H := H) (E := H) (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) raw.2⟩
  have acted:Continuous (fun t => action seed M t (history seed M word t)) :=
    Continuous.clm_apply (𝕜 := ℝ) (E := H) (F := H) (NativeWindowHistoryOseen.action_continuous seed M)
      (history_continuous seed M word)
  exact ((mapped.sub (acted.intervalIntegrable a b))).congr (fun t _ => (load_original seed M word t).symm)

private theorem inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f p : ℝ → E) (a b : ℝ) (ab : a ≤ b) (fi : IntervalIntegrable f volume a b) (pc : ContinuousOn p (Icc a b)) :
    IntervalIntegrable (fun t => inner ℝ (f t) (p t)) volume a b := by
  obtain ⟨C,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn pc
  have first:=(intervalIntegrable_iff_integrableOn_Icc_of_le ab).mp fi
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mpr
  refine (first.norm.mul_const C).mono' (first.aestronglyMeasurable.inner (pc.aestronglyMeasurable measurableSet_Icc)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_left (bounded t ht) (norm_nonneg _))

theorem transpose_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) : ContinuousOn (transpose seed M word a B aB) (Icc a B) := by
  have yc : ContinuousOn (created seed M word a B aB) (Icc a B) := fun t ht =>
    (NativeWindowHistoryAllOrderCausal.created_derivative seed M word a B aB t ht).continuousWithinAt
  have xc:=(history_continuous seed M word).continuousOn (s := Icc a B)
  have act:= (NativeWindowHistoryOseen.action_continuous seed M).continuousOn (s := Icc a B)
  have cv:= (NativeWindowHistoryCausalPassivity.creationInput_continuous seed M (value seed M word)
    (NativeWindowHistoryAllOrderCausal.value_continuous seed M word)).continuousOn (s := Icc a B)
  have ay:=ContinuousOn.clm_apply (𝕜 := ℝ) (E := H) (F := H) act yc
  have ax:=ContinuousOn.clm_apply (𝕜 := ℝ) (E := H) (F := H) act xc
  exact ((((ay.inner (𝕜 := ℝ) xc).add (yc.inner (𝕜 := ℝ) ax)).const_mul 2).add
    ((cv.inner (𝕜 := ℝ) yc).const_mul 2)).add ((cv.inner (𝕜 := ℝ) xc).const_mul 2)

theorem transpose_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B) :
    (∫t in a..b,2*inner ℝ (created seed M word a B aB t) (load seed M word t))=
      pairing seed M word a B aB b-∫t in a..b,transpose seed M word a B aB t := by
  have subset:Icc a b ⊆ Icc a B:=Icc_subset_Icc le_rfl inside.2
  have yc : ContinuousOn (created seed M word a B aB) (Icc a b) := fun t ht =>
    ((NativeWindowHistoryAllOrderCausal.created_derivative seed M word a B aB t (subset ht)).mono subset).continuousWithinAt
  have xc:=(history_continuous seed M word).continuousOn (s := Icc a b)
  have work : IntervalIntegrable (fun t => 2*inner ℝ (created seed M word a B aB t) (load seed M word t)) volume a b := by
    have first:=inner_integrable (E := H) (load seed M word) (created seed M word a B aB) a b inside.1
      (load_integrable seed M word a b) yc
    simpa only [real_inner_comm] using first.const_mul 2
  have transposed:=((transpose_continuous seed M word a B aB).mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1
  have pc:ContinuousOn (pairing seed M word a B aB) (Icc a b):=(yc.inner (𝕜 := ℝ) xc).const_mul 2
  have derivative (t : ℝ) (ht : t∈Ioo a b) :=
    (NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing_hasDerivWithinAt seed M word a B aB t
      ⟨ht.1.le,ht.2.le.trans inside.2⟩).hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le inside.2))
  have written:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 pc derivative (work.add transposed)
  rw [intervalIntegral.integral_add work transposed] at written
  have initial:pairing seed M word a B aB a=0 := by
    rw [pairing,NativeWindowHistoryAllOrderCausalEnergy.created_initial,inner_zero_left (𝕜 := ℝ) (E := H),mul_zero]
  rw [initial,sub_zero] at written
  linarith only [written]

theorem first_history_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M (j : Coordinate) t,t∈Icc 0 horizon → ‖history seed M [j] t‖^2 ≤ C := by
  obtain ⟨C,C0,paid⟩:=NativeWindowAbsoluteTimeEnergy.source_first_jet_bound seed horizon
  refine ⟨C,C0,fun M j t inside => ?_⟩
  have natural:=NativeWindowAbsoluteTimeIsometry.naturality NativeWholeResolvent.wholePhysical (fiber M [j]) t (finiteHistory seed t M)
  have mapped:=congrArg ((fiber M [j]).compLpL 2 (volume : Measure ℝ)) (NativeWindowAbsoluteTimeBridge.finite_map seed M t)
  have read:=natural.trans (mapped.trans (NativeWindowAbsoluteTimeEnergy.word_project M j.succ (NativeWindowAbsoluteTimeSource.history seed t)))
  have norms:=congrArg (fun v : NativeWindowAbsoluteTimeSource.H => ‖v‖^2) read
  rw [NativeWindowAbsoluteTimeIsometry.norm_map] at norms
  change ‖history seed M [j] t‖^2 = ‖NativeWindowAbsoluteTimeEnergy.value seed M t j.succ‖^2 at norms
  exact norms.trans_le (by
    have lower:=sq_nonneg ‖NativeWindowAbsoluteTimeEnergy.tangent seed M t j.succ‖
    linarith only [paid M j.succ t inside,lower])

set_option backward.isDefEq.respectTransparency false in
theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ)
    (nonnegative : 0 ≤ horizon) (positive : 0<epsilon) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      |∫t in a..b,2*inner ℝ (created seed M [j] a horizon start.2 t) (load seed M [j] t)| ≤
        epsilon*(∫t in a..b,gradient M (history seed M [j] t))+C := by
  obtain ⟨X,X0,hist⟩:=first_history_bound seed horizon
  obtain ⟨Y,Y0,resp⟩:=NativeWindowHistoryCausalFirstResponse.source_first_word seed horizon nonnegative
  let A:=8*nu.coeff^2/epsilon+1
  let P:=(1+2/epsilon)*inputBudget seed horizon
  have A0 : 0 ≤ A:=by positivity
  have P0 : 0 ≤ P:=mul_nonneg (by positivity) (NativeWindowHistoryAllOrderCreatedLoadTranspose.inputBudget_nonnegative seed horizon)
  refine ⟨X+Y+A*(Y/nu.coeff)+P*horizon,by positivity [nu.coeff_pos],fun M j a start b inside => ?_⟩
  let x:=history seed M [j]
  let y:=created seed M [j] a horizon start.2
  have xc:=(history_continuous seed M [j]).continuousOn (s := Icc a b)
  have yc : ContinuousOn y (Icc a b) := fun t ht =>
    ((NativeWindowHistoryAllOrderCausal.created_derivative seed M [j] a horizon start.2 t
      ⟨ht.1,ht.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have gx : IntervalIntegrable (fun t => gradient M (x t)) volume a b :=((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp_continuousOn xc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have gy : IntervalIntegrable (fun t => gradient M (y t)) volume a b :=((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp_continuousOn yc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have response:=resp M j a start b inside
  have g0:0 ≤ ∫t in a..b,gradient M (y t) := intervalIntegral.integral_nonneg_of_forall inside.1
    (fun t => NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (y t))
  have yb:‖y b‖^2 ≤ Y:=by nlinarith only [response,mul_nonneg nu.coeff_pos.le g0]
  have integralY:(∫t in a..b,gradient M (y t)) ≤ Y/nu.coeff := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    nlinarith only [response,sq_nonneg ‖y b‖]
  have point (t : ℝ) (ht : t∈Ioc a b) : ‖transpose seed M [j] a horizon start.2 t‖ ≤
      epsilon*gradient M (x t)+A*gradient M (y t)+P := by
    exact (Real.norm_eq_abs _).trans_le (NativeWindowHistoryAllOrderCreatedLoadTranspose.transpose_bound seed horizon epsilon positive M j
      a horizon start.2 t ⟨start.1.trans ht.1.le,ht.2.trans inside.2⟩)
  have integrated:=intervalIntegral.norm_integral_le_of_norm_le inside.1 (Eventually.of_forall point)
    (((gx.const_mul epsilon).add (gy.const_mul A)).add (intervalIntegrable_const (c := P)))
  rw [Real.norm_eq_abs,intervalIntegral.integral_add ((gx.const_mul epsilon).add (gy.const_mul A)) (intervalIntegrable_const (c := P)),
    intervalIntegral.integral_add (gx.const_mul epsilon) (gy.const_mul A),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul] at integrated
  have boundT : |∫t in a..b,transpose seed M [j] a horizon start.2 t| ≤
      epsilon*(∫t in a..b,gradient M (x t))+A*(Y/nu.coeff)+P*horizon := by
    apply integrated.trans
    have duration:=mul_le_mul_of_nonneg_right (by linarith [start.1,inside.2] : b-a ≤ horizon) P0
    have gradients:=mul_le_mul_of_nonneg_left integralY A0
    linarith only [duration,gradients]
  have endpoint : |pairing seed M [j] a horizon start.2 b| ≤ X+Y := by
    have paired:=abs_real_inner_le_norm (y b) (x b)
    have bound:=hist M j b ⟨start.1.trans inside.1,inside.2⟩
    have scale:|pairing seed M [j] a horizon start.2 b|=2*|inner ℝ (y b) (x b)| := by
      rw [pairing,abs_mul]
      norm_num
      rfl
    rw [scale]
    nlinarith only [paired,bound,yb,sq_nonneg (‖y b‖-‖x b‖)]
  rw [transpose_write seed M [j] a horizon start.2 b inside]
  have triangle : |pairing seed M [j] a horizon start.2 b-∫t in a..b,transpose seed M [j] a horizon start.2 t| ≤
      |pairing seed M [j] a horizon start.2 b|+|∫t in a..b,transpose seed M [j] a horizon start.2 t| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (pairing seed M [j] a horizon start.2 b) (∫t in a..b,transpose seed M [j] a horizon start.2 t)
  exact (triangle.trans (add_le_add endpoint boundT)).trans_eq (by ring)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a ≤ B) (a0 : 0 ≤ a) (t : ℝ) (inside : t∈Icc a B) :
    2*inner ℝ (created seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t)) (load seed M word (step.2.clockAdvance+t))=
      2*inner ℝ (created step.1 M word a B aB t) (load step.1 M word t) :=
  congrArg₂ (fun (x y : H) => 2*inner ℝ x y)
    (NativeWindowHistoryAllOrderCausal.created_next seed M word step generated a B aB a0 t inside)
    (NativeWindowHistoryAllOrderCausal.load_next seed M word step generated t (a0.trans inside.1))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCreatedLoadBudget

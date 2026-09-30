import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Response
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Budget

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalPassivity
open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryCausalResponse
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanBlocks (bath bath_dissipative)
open NativeWindowHistoryCausalBath (kernel dual bath_continuous)
open NativeWindowHistoryMeanAction (creation)
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryCausalBudget (effect createdMemory)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private theorem green_write {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A D : ℝ → E → E) (dual : ∀ t u v,inner ℝ (A t u) v=inner ℝ u (D t v))
    (x p f : ℝ → E) (fc : Continuous f) (a b : ℝ) (ab : a≤b)
    (dx : ∀ t∈Icc a b,HasDerivWithinAt x (A t (x t)+f t) (Icc a b) t)
    (dp : ∀ t∈Icc a b,HasDerivWithinAt p (-D t (p t)) (Icc a b) t) :
    inner ℝ (x b) (p b)-inner ℝ (x a) (p a)=∫ t in a..b,inner ℝ (f t) (p t) := by
  have xc : ContinuousOn x (Icc a b) := fun t ht => (dx t ht).continuousWithinAt
  have pc : ContinuousOn p (Icc a b) := fun t ht => (dp t ht).continuousWithinAt
  have derivative (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun s => inner ℝ (x s) (p s)) (inner ℝ (f t) (p t)) t := by
    have first := (dx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have last := (dp t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    convert! first.inner ℝ last using 1
    rw [inner_neg_right,inner_add_left,dual]
    ring
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ab (xc.inner (𝕜 := ℝ) pc)
    derivative ((fc.continuousOn.inner (𝕜 := ℝ) pc).intervalIntegrable_of_Icc ab)).symm

def bathResponse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (f : ℝ → H) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) : ℝ → H := response (bath seed M) (bath_continuous seed M) f fc a B aB

theorem bathResponse_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (f : ℝ → H) (fc : Continuous f) (a B : ℝ) (aB : a≤B) : bathResponse seed M f fc a B aB a=0 :=
  response_initial (E := H) _ _ f fc a B aB

theorem bathResponse_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (f : ℝ → H) (fc : Continuous f) (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (bathResponse seed M f fc a B aB)
      (bath seed M t (bathResponse seed M f fc a B aB t)+f t) (Icc a B) t :=
  response_derivative (E := H) _ _ f fc a B aB t inside

theorem bathResponse_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (f : ℝ → H) (fc : Continuous f) (a B : ℝ) (aB : a≤B)
    (b : ℝ) (inside : b∈Icc a B) (terminal : H) :
    inner ℝ (bathResponse seed M f fc a B aB b) terminal=
      ∫ s in a..b,inner ℝ (f s) (kernel seed M a B aB s b terminal) := by
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have dx (t : ℝ) (ht : t∈Icc a b) : HasDerivWithinAt (bathResponse seed M f fc a B aB)
      (bath seed M t (bathResponse seed M f fc a B aB t)+f t) (Icc a b) t := by
    exact (bathResponse_derivative seed M f fc a B aB t (subset ht)).mono subset
  have dp (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt (fun s => kernel seed M a B aB s b terminal)
        (-dual seed M t (kernel seed M a B aB t b terminal)) (Icc a b) t := by
    exact (NativeWindowHistoryCausalBath.kernel_derivative seed M a B aB b terminal t (subset ht)).mono subset
  have written := green_write (E := H) (fun t v => bath seed M t v) (fun t v => dual seed M t v)
    (NativeWindowHistoryCausalBath.bath_dual seed M) (bathResponse seed M f fc a B aB)
    (fun t => kernel seed M a B aB t b terminal) f fc a b inside.1 dx dp
  simpa only [NativeWindowHistoryCausalBath.kernel_terminal seed M a B aB b inside terminal,
    bathResponse_initial seed M f fc a B aB,inner_zero_left,sub_zero] using! written

theorem creation_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    Continuous (creation seed M) :=
  Continuous.clm_comp (𝕜 := ℝ) (E := wholePhysical) (F := H) (G := H) continuous_const
    (Continuous.clm_comp (𝕜 := ℝ) (E := wholePhysical) (F := H) (G := H)
      (NativeWindowHistoryOseen.action_continuous seed M) continuous_const)

def creationInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : ℝ → wholePhysical) (t : ℝ) : H :=
  creation seed M t (v t)

theorem creationInput_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → wholePhysical) (vc : Continuous v) : Continuous (creationInput seed M v) :=
  Continuous.clm_apply (𝕜 := ℝ) (E := wholePhysical) (F := H) (creation_continuous seed M) vc

def creationResponse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → wholePhysical) (vc : Continuous v) (a B : ℝ) (aB : a≤B) : ℝ → H :=
  bathResponse seed M (creationInput seed M v) (creationInput_continuous seed M v vc) a B aB

theorem creation_memory_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → wholePhysical) (vc : Continuous v) (a B : ℝ) (aB : a≤B)
    (b : ℝ) (inside : b∈Icc a B) :
    (∫ s in a..b,effect seed M a B aB s b (v b) (v s))=
      inner ℝ (creationInput seed M v b) (creationResponse seed M v vc a B aB b) := by
  have read := bathResponse_green seed M (creationInput seed M v)
    (creationInput_continuous seed M v vc) a B aB b inside (creationInput seed M v b)
  have commuted : inner ℝ (creationResponse seed M v vc a B aB b) (creationInput seed M v b)=
      inner ℝ (creationInput seed M v b) (creationResponse seed M v vc a B aB b) := by
    simpa only [] using! (real_inner_comm (creationInput seed M v b) (creationResponse seed M v vc a B aB b))
  exact read.symm.trans commuted

theorem creation_memory_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → wholePhysical) (vc : Continuous v) (a B : ℝ) (aB : a≤B)
    (b : ℝ) (inside : b∈Icc a B) :
    (∫ t in a..b,∫ s in a..t,effect seed M a B aB s t (v t) (v s))=
      ‖creationResponse seed M v vc a B aB b‖^2/2-
        ∫ t in a..b,inner ℝ (creationResponse seed M v vc a B aB t)
          (bath seed M t (creationResponse seed M v vc a B aB t)) := by
  calc
    _ = ∫ t in a..b,inner ℝ (creationInput seed M v t) (creationResponse seed M v vc a B aB t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le inside.1] at ht
      exact creation_memory_read seed M v vc a B aB t ⟨ht.1,ht.2.trans inside.2⟩
    _ = _ := by
      simpa only [creationResponse,bathResponse] using! response_energy (E := H)
        (bath seed M) (bath_continuous seed M) (creationInput seed M v)
        (creationInput_continuous seed M v vc) a B aB b inside

theorem creation_memory_passive (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → wholePhysical) (vc : Continuous v) (a B : ℝ) (aB : a≤B)
    (b : ℝ) (inside : b∈Icc a B) :
    0≤∫ t in a..b,∫ s in a..t,effect seed M a B aB s t (v t) (v s) := by
  have same : (∫ t in a..b,∫ s in a..t,effect seed M a B aB s t (v t) (v s))=
      ∫ t in a..b,inner ℝ (creationInput seed M v t) (creationResponse seed M v vc a B aB t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le inside.1] at ht
    exact creation_memory_read seed M v vc a B aB t ⟨ht.1,ht.2.trans inside.2⟩
  rw [same]
  simpa only [creationResponse,bathResponse] using! response_passive (E := H)
    (bath seed M) (bath_continuous seed M) (bath_dissipative seed M)
    (creationInput seed M v) (creationInput_continuous seed M v vc) a B aB b inside

theorem source_created_passive (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) :
    0≤∫ t in a..b,createdMemory seed M a B aB t := by
  exact creation_memory_passive seed M (fun t => mean (finiteHistory seed t M))
    (mean.continuous.comp (NativeWindowHistoryOseen.history_continuous seed M)) a B aB b inside

theorem source_complete_work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) :
    0≤∫ t in a..b,NativeWindowHistoryCausalMean.memory seed M a B aB t (mean (finiteHistory seed t M))-
      ∫ s in a..t,inner ℝ (NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryOseen.forcingHistory seed M s))
        (kernel seed M a B aB s t (creation seed M t (mean (finiteHistory seed t M)))) := by
  have same : (∫ t in a..b,NativeWindowHistoryCausalMean.memory seed M a B aB t (mean (finiteHistory seed t M))-
      ∫ s in a..t,inner ℝ (NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryOseen.forcingHistory seed M s))
        (kernel seed M a B aB s t (creation seed M t (mean (finiteHistory seed t M)))))=
      ∫ t in a..b,createdMemory seed M a B aB t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le inside.1] at ht
    have paid := NativeWindowHistoryCausalBudget.complete_memory seed M a B aB t ⟨ht.1,ht.2.trans inside.2⟩
    exact sub_eq_iff_eq_add.mpr paid
  rw [same]
  exact source_created_passive seed M a B aB b inside
end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalPassivity

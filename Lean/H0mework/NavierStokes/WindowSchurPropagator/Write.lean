import H0mework.NavierStokes.WindowSchurPropagator.Kernel
import H0mework.NavierStokes.WindowHistoryOseen.Equation

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPropagator
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action adjoint action_continuous adjoint_continuous forcingHistory)
open NativeWindowTraceWholeHistory (finiteHistory)
noncomputable section
variable {nu : Viscosity}

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_growth (x rate : ℝ → E) (a b : ℝ)
    (dx : ∀ t∈Icc a b,HasDerivWithinAt x (rate t) (Icc a b) t)
    (sign : ∀ t∈Icc a b,0 ≤ inner ℝ (x t) (rate t)) :
    MonotoneOn (fun t => ‖x t‖^2) (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun t ht => ((dx t ht).continuousWithinAt.norm.pow 2))
  · intro t ht
    exact ((dx t (interior_subset ht)).norm_sq).mono interior_subset
  · intro t ht
    exact mul_nonneg (by norm_num) (sign t (interior_subset ht))

private theorem inner_integrable (f p : ℝ → E) (a b : ℝ) (ab : a ≤ b)
    (integrable : IntervalIntegrable f volume a b) (continuous : ContinuousOn p (Icc a b)) :
    IntervalIntegrable (fun t => inner ℝ (f t) (p t)) volume a b := by
  obtain ⟨C,bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous
  have first : IntegrableOn f (Icc a b) := (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mp integrable
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ab).mpr
  refine (first.norm.mul_const C).mono' (first.aestronglyMeasurable.inner
    (continuous.aestronglyMeasurable measurableSet_Icc)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (norm_inner_le_norm (f t) (p t)).trans (mul_le_mul_of_nonneg_left (bounded t ht) (norm_nonneg _))

private theorem green_write (A D : ℝ → E →L[ℝ] E)
    (dual : ∀ t u v,inner ℝ (A t u) v=inner ℝ u (D t v))
    (x p f : ℝ → E) (a b : ℝ) (ab : a ≤ b)
    (dx : ∀ t∈Icc a b,HasDerivWithinAt x (A t (x t)+f t) (Icc a b) t)
    (dp : ∀ t∈Icc a b,HasDerivWithinAt p (-D t (p t)) (Icc a b) t)
    (integrable : IntervalIntegrable f volume a b) :
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
    derivative (inner_integrable f p a b ab integrable pc)).symm
end Hilbert

theorem kernel_mass_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B) (terminal : H)
    (s : ℝ) (sample : s∈Icc a b) : ‖kernel seed M a B aB s b terminal‖ ≤ ‖terminal‖ := by
  let p := fun t => kernel seed M a B aB t b terminal
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have derivative (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt p (-adjoint seed M t (p t)) (Icc a b) t :=
    HasDerivWithinAt.mono (F := H) (kernel_derivative seed M a B aB b terminal t (subset ht)) subset
  have sign (t : ℝ) (_ht : t∈Icc a b) : 0 ≤ inner ℝ (p t) (-adjoint seed M t (p t)) := by
    rw [inner_neg_right (𝕜 := ℝ) (p t),← NativeWindowHistoryOseen.action_adjoint,real_inner_comm (p t) (action seed M t (p t))]
    exact neg_nonneg.mpr (NativeWindowHistoryOseen.action_dissipative seed M t (p t))
  have order := norm_growth (E := H) p (fun t => -adjoint seed M t (p t)) a b derivative sign
  have bound := order sample (right_mem_Icc.mpr inside.1) sample.2
  have terminalRead : p b=terminal := kernel_terminal seed M a B aB b inside terminal
  have squareRead := congrArg (fun v : H => ‖v‖^2) terminalRead
  exact (sq_le_sq₀ (norm_nonneg (p s)) (norm_nonneg terminal)).mp (bound.trans_eq squareRead)

theorem source_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B) (terminal : H) :
    inner ℝ (finiteHistory seed b M) terminal-
      inner ℝ (finiteHistory seed a M) (kernel seed M a B aB a b terminal)=
        ∫ t in a..b,inner ℝ (forcingHistory seed M t) (kernel seed M a B aB t b terminal) := by
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have written := green_write (E := H) (action seed M) (adjoint seed M)
    (NativeWindowHistoryOseen.action_adjoint seed M) (fun t => finiteHistory seed t M)
    (fun t => kernel seed M a B aB t b terminal) (forcingHistory seed M) a b inside.1
    (fun t _ => (NativeWindowHistoryOseen.source_hasDerivAt seed M t).hasDerivWithinAt)
    (fun t ht => (kernel_derivative seed M a B aB b terminal t (subset ht)).mono subset)
    (NativeWindowHistoryOseen.forcingHistory_integrable seed M a b)
  have terminalRead := kernel_terminal seed M a B aB b inside terminal
  exact (congrArg (fun v : H => inner ℝ (finiteHistory seed b M) v-
    inner ℝ (finiteHistory seed a M) (kernel seed M a B aB a b terminal)) terminalRead).symm.trans written

theorem joint_source_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (frame : ℝ) (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector) (R : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B) :
    inner ℝ (finiteHistory seed b M) (NativeWindowTraceWholeHistory.jointHistory seed frame b M F R)-
      inner ℝ (finiteHistory seed a M) (kernel seed M a B aB a b
        (NativeWindowTraceWholeHistory.jointHistory seed frame b M F R))=
      ∫ t in a..b,inner ℝ (forcingHistory seed M t) (kernel seed M a B aB t b
        (NativeWindowTraceWholeHistory.jointHistory seed frame b M F R)) :=
  source_green seed M a B aB b inside _

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem kernel_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a ≤ B) (a0 : 0 ≤ a) (b : ℝ) (inside : b∈Icc a B)
    (s : ℝ) (sample : s∈Icc a b) :
    kernel seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+s) (step.2.clockAdvance+b)=kernel step.1 M a B aB s b := by
  apply ContinuousLinearMap.ext
  intro terminal
  let c := step.2.clockAdvance
  let p := fun t => kernel seed M (c+a) (c+B) (add_le_add_right aB c) (c+t) (c+b) terminal
  have terminalRead : p b=terminal := kernel_terminal seed M (c+a) (c+B) (add_le_add_right aB c)
    (c+b) ⟨add_le_add_right inside.1 c,add_le_add_right inside.2 c⟩ terminal
  have derivative (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt p (-adjoint step.1 M t (p t)) (Icc a b) t := by
    have into : MapsTo (fun r : ℝ => c+r) (Icc a b) (Icc (c+a) (c+B)) :=
      fun r hr => ⟨add_le_add_right hr.1 c,add_le_add_right (hr.2.trans inside.2) c⟩
    have old := kernel_derivative seed M (c+a) (c+B) (add_le_add_right aB c) (c+b) terminal (c+t) (into ht)
    have shifted := HasDerivWithinAt.scomp (F := H) t old ((hasDerivAt_id t).const_add c).hasDerivWithinAt into
    have actual := (congrArg Prod.snd (NativeWindowHistoryOseen.whole_next seed M step generated t (a0.trans ht.1)))
    have valueRead := congrArg (fun op : H →L[ℝ] H => -(op (p t))) actual
    have rate : HasDerivWithinAt p (-adjoint seed M (c+t) (p t)) (Icc a b) t := by
      simpa only [one_smul,Function.comp_def] using! shifted
    exact valueRead ▸ rate
  exact (kernel_original step.1 M a B aB b inside terminal p terminalRead derivative sample).symm

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPropagator

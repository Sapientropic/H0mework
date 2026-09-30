import H0mework.NavierStokes.WindowSchurPropagator.Flow

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPropagator
open Set Filter MeasureTheory
open PhysicsCore.StageNineDiracMatterGalerkinEvolution
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action adjoint action_continuous adjoint_continuous)
noncomputable section
variable {nu : Viscosity}

def endpoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) (b : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (forward seed M a B aB b)

private theorem pairing_constant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A D : ℝ → E →L[ℝ] E) (dual : ∀ t u v,inner ℝ (A t u) v=inner ℝ u (D t v))
    (x y : ℝ → E) (a b : ℝ) (ab : a ≤ b)
    (dx : ∀ t∈Icc a b,HasDerivWithinAt x (A t (x t)) (Icc a b) t)
    (dy : ∀ t∈Icc a b,HasDerivWithinAt y (-D t (y t)) (Icc a b) t) :
    inner ℝ (x b) (y b)=inner ℝ (x a) (y a) := by
  have first : ContinuousOn x (Icc a b) := fun t ht => (dx t ht).continuousWithinAt
  have last : ContinuousOn y (Icc a b) := fun t ht => (dy t ht).continuousWithinAt
  have derivative (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun s => inner ℝ (x s) (y s)) 0 t := by
    have before := (dx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have after := (dy t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    convert! before.inner ℝ after using 1
    rw [inner_neg_right,dual]
    ring
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ab (first.inner (𝕜 := ℝ) last)
    derivative (intervalIntegrable_const (c := (0 : ℝ)))
  rw [intervalIntegral.integral_zero] at written
  exact sub_eq_zero.mp written.symm

private theorem matrix_adjoint_original {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A D : ℝ → E →L[ℝ] E) (continuous : Continuous A)
    (dual : ∀ t u v,inner ℝ (A t u) v=inner ℝ u (D t v))
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b ∈ Icc a B) (terminal : E)
    (path : ℝ → E) (atTerminal : path b=terminal)
    (evolution : ∀ t∈Icc a b,HasDerivWithinAt path (-D t (path t)) (Icc a b) t) :
    (matrix A continuous a B aB b).adjoint terminal=path a := by
  apply ext_inner_left ℝ
  intro initial
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have atStart : matrix A continuous a B aB a initial=initial :=
    congrArg (fun op : E →L[ℝ] E => op initial) (matrix_initial A continuous a B aB)
  have same := pairing_constant A D dual (fun t => matrix A continuous a B aB t initial) path a b inside.1
    (fun t ht => (applied_derivative A continuous a B aB initial t (subset ht)).mono subset) evolution
  rw [atStart,atTerminal] at same
  exact (ContinuousLinearMap.adjoint_inner_right (matrix A continuous a B aB b) initial terminal).trans same

theorem endpoint_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b ∈ Icc a B) (terminal : H) (path : ℝ → H) (atTerminal : path b=terminal)
    (evolution : ∀ t ∈ Icc a b,HasDerivWithinAt path (-adjoint seed M t (path t)) (Icc a b) t) :
    endpoint seed M a B aB b terminal=path a := by
  simpa only [endpoint,forward] using! matrix_adjoint_original (E := H) (action seed M) (adjoint seed M) (action_continuous seed M)
    (NativeWindowHistoryOseen.action_adjoint seed M) a B aB b inside terminal path atTerminal evolution

def kernel (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) (s b : ℝ) : H →L[ℝ] H :=
  (backwardFlow seed M a B aB s).comp (endpoint seed M a B aB b)

theorem kernel_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (terminal : H) (s : ℝ) (inside : s ∈ Icc a B) :
    HasDerivWithinAt (fun t => kernel seed M a B aB t b terminal)
      (-adjoint seed M s (kernel seed M a B aB s b terminal)) (Icc a B) s :=
  backwardFlow_derivative seed M a B aB (endpoint seed M a B aB b terminal) s inside

theorem kernel_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b ∈ Icc a B) (terminal : H) (path : ℝ → H) (atTerminal : path b=terminal)
    (evolution : ∀ t ∈ Icc a b,HasDerivWithinAt path (-adjoint seed M t (path t)) (Icc a b) t) :
    EqOn (fun t => kernel seed M a B aB t b terminal) path (Icc a b) := by
  have start := endpoint_original seed M a B aB b inside terminal path atTerminal evolution
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have opStart : backwardFlow seed M a B aB a=ContinuousLinearMap.id ℝ H :=
    matrix_initial (E := H) _ _ a B aB
  have atStart : kernel seed M a B aB a b terminal=path a :=
    (congrArg (fun op : H →L[ℝ] H => op (endpoint seed M a B aB b terminal)) opStart).trans start
  apply galerkinLinearCoefficientCurve_eqOn_Icc (E := H) (fun t => -adjoint seed M t)
    (adjoint_continuous seed M).neg _ path (path a) a b inside.1
  · exact atStart
  · rfl
  · intro t ht
    exact (backwardFlow_derivative seed M a B aB (endpoint seed M a B aB b terminal) t (subset ht)).mono subset
  · exact evolution

theorem kernel_terminal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b ∈ Icc a B) (terminal : H) : kernel seed M a B aB b b terminal=terminal := by
  obtain ⟨path,atTerminal,evolution⟩ := NativeWindowHistoryOseen.exists_backward seed M terminal a b inside.1
  exact (kernel_original seed M a B aB b inside terminal path atTerminal evolution (right_mem_Icc.mpr inside.1)).trans atTerminal

theorem endpoint_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) :
    ContinuousOn (endpoint seed M a B aB) (Icc a B) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)).continuous.comp_continuousOn
    (matrix_continuous (E := H) _ _ a B aB)

theorem kernel_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) :
    ContinuousOn (fun pair : ℝ × ℝ => kernel seed M a B aB pair.1 pair.2) ((Icc a B) ×ˢ (Icc a B)) := by
  have before : ContinuousOn (fun pair : ℝ × ℝ => backwardFlow seed M a B aB pair.1) ((Icc a B) ×ˢ (Icc a B)) :=
    (matrix_continuous (E := H) _ _ a B aB).comp continuous_fst.continuousOn (fun _ h => h.1)
  have after : ContinuousOn (fun pair : ℝ × ℝ => endpoint seed M a B aB pair.2) ((Icc a B) ×ˢ (Icc a B)) :=
    (endpoint_continuous seed M a B aB).comp continuous_snd.continuousOn (fun _ h => h.2)
  exact ContinuousOn.clm_comp (𝕜 := ℝ) (E := H) (F := H) (G := H) before after

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPropagator

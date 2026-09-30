import H0mework.Versions.X.NavierStokes.WindowSchurMean.Blocks
import H0mework.Versions.X.NavierStokes.WindowSchurPropagator.Flow

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalBath
open Set Filter MeasureTheory
open PhysicsCore.StageNineDiracMatterGalerkinEvolution
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanBlocks (bath bath_dissipative)
open NativeWindowHistoryPropagator (matrix matrix_initial matrix_derivative matrix_continuous applied_derivative applied_original)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

-- The only generator is the original time-dependent Q A(t) Q.
theorem bath_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (bath seed M) := by
  exact Continuous.clm_comp (𝕜 := ℝ) (E := H) (F := H) (G := H) continuous_const
    (Continuous.clm_comp (𝕜 := ℝ) (E := H) (F := H) (G := H)
      (NativeWindowHistoryOseen.action_continuous seed M) continuous_const)

def dual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (bath seed M t)

theorem dual_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (dual seed M) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)).continuous.comp (bath_continuous seed M)

theorem bath_dual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) (u v : H) :
    inner ℝ (bath seed M t u) v = inner ℝ u (dual seed M t v) := by
  simpa only [dual] using! (ContinuousLinearMap.adjoint_inner_right (𝕜 := ℝ) (E := H) (F := H) (bath seed M t) u v).symm

def forward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) : ℝ → H →L[ℝ] H :=
  matrix (E := H) (bath seed M) (bath_continuous seed M) a B aB

def backwardFlow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) : ℝ → H →L[ℝ] H :=
  matrix (E := H) (fun t => -dual seed M t) (dual_continuous seed M).neg a B aB

theorem forward_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) :
    forward seed M a B aB a = ContinuousLinearMap.id ℝ H :=
  matrix_initial (E := H) _ _ a B aB

theorem forward_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (v : H) (t : ℝ) (inside : t ∈ Icc a B) :
    HasDerivWithinAt (fun s => forward seed M a B aB s v)
      (bath seed M t (forward seed M a B aB t v)) (Icc a B) t :=
  applied_derivative (E := H) _ _ a B aB v t inside

theorem backwardFlow_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (v : H) (t : ℝ) (inside : t ∈ Icc a B) :
    HasDerivWithinAt (fun s => backwardFlow seed M a B aB s v)
      (-dual seed M t (backwardFlow seed M a B aB t v)) (Icc a B) t :=
  applied_derivative (E := H) _ _ a B aB v t inside

theorem exists_backward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H)
    (a b : ℝ) (ab : a ≤ b) :
    ∃ path : ℝ → H, path b=v ∧ ∀ t∈Icc a b,
      HasDerivWithinAt path (-dual seed M t (path t)) (Icc a b) t := by
  obtain ⟨path,initial,evolution⟩ := exists_galerkinLinearCoefficientCurve_on_Icc
    (fun t => dual seed M (-t)) ((dual_continuous seed M).comp continuous_neg) v (-b) (-a) (neg_le_neg ab)
  refine ⟨fun t => path (-t),initial,?_⟩
  intro t inside
  have into : MapsTo (fun s : ℝ => -s) (Icc a b) (Icc (-b) (-a)) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have actual := (evolution (-t) (into inside)).scomp t (hasDerivAt_neg t).hasDerivWithinAt into
  simpa only [neg_neg,neg_smul,one_smul,galerkinLinearVelocity] using! actual

-- Dissipativity generates the bound; no operator-norm or solution certificate is an input.
theorem forward_contracts (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (v : H) (t : ℝ) (inside : t ∈ Icc a B) : ‖forward seed M a B aB t v‖ ≤ ‖v‖ := by
  let path := fun s => forward seed M a B aB s v
  have energy (s : ℝ) (hs : s∈Icc a B) := HasDerivWithinAt.norm_sq (F := H) (forward_derivative seed M a B aB v s hs)
  have decreasing : AntitoneOn (fun s => ‖path s‖^2) (Icc a B) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a B)
      (fun s hs => (energy s hs).continuousWithinAt)
    · intro s hs
      exact (energy s (interior_subset hs)).mono interior_subset
    · intro s _
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (bath_dissipative seed M s (path s))
  have paid:=decreasing (left_mem_Icc.mpr aB) inside inside.1
  have initial : path a=v := congrArg (fun op : H →L[ℝ] H => op v) (forward_initial seed M a B aB)
  change ‖path t‖^2 ≤ ‖path a‖^2 at paid
  rw [initial] at paid
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp paid


def endpoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) (b : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (forward seed M a B aB b)

private theorem abstract_pairing_constant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

private theorem abstract_matrix_adjoint_original {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
  have same := abstract_pairing_constant A D dual (fun t => matrix A continuous a B aB t initial) path a b inside.1
    (fun t ht => (applied_derivative A continuous a B aB initial t (subset ht)).mono subset) evolution
  rw [atStart,atTerminal] at same
  exact (ContinuousLinearMap.adjoint_inner_right (matrix A continuous a B aB b) initial terminal).trans same


theorem endpoint_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b ∈ Icc a B) (terminal : H) (path : ℝ → H) (atTerminal : path b=terminal)
    (evolution : ∀ t∈Icc a b,HasDerivWithinAt path (-dual seed M t (path t)) (Icc a b) t) :
    endpoint seed M a B aB b terminal=path a := by
  simpa only [endpoint,forward] using! abstract_matrix_adjoint_original (E := H)
    (bath seed M) (dual seed M) (bath_continuous seed M) (bath_dual seed M)
    a B aB b inside terminal path atTerminal evolution

def kernel (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) (s b : ℝ) : H →L[ℝ] H :=
  (backwardFlow seed M a B aB s).comp (endpoint seed M a B aB b)

theorem kernel_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (terminal : H) (s : ℝ) (inside : s ∈ Icc a B) :
    HasDerivWithinAt (fun t => kernel seed M a B aB t b terminal)
      (-dual seed M s (kernel seed M a B aB s b terminal)) (Icc a B) s :=
  backwardFlow_derivative seed M a B aB (endpoint seed M a B aB b terminal) s inside

theorem kernel_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b ∈ Icc a B) (terminal : H) (path : ℝ → H) (atTerminal : path b=terminal)
    (evolution : ∀ t∈Icc a b,HasDerivWithinAt path (-dual seed M t (path t)) (Icc a b) t) :
    EqOn (fun t => kernel seed M a B aB t b terminal) path (Icc a b) := by
  have start := endpoint_original seed M a B aB b inside terminal path atTerminal evolution
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have opStart : backwardFlow seed M a B aB a=ContinuousLinearMap.id ℝ H :=
    matrix_initial (E := H) _ _ a B aB
  have atStart : kernel seed M a B aB a b terminal=path a :=
    (congrArg (fun op : H →L[ℝ] H => op (endpoint seed M a B aB b terminal)) opStart).trans start
  apply galerkinLinearCoefficientCurve_eqOn_Icc (E := H) (fun t => -dual seed M t)
    (dual_continuous seed M).neg _ path (path a) a b inside.1
  · exact atStart
  · rfl
  · intro t ht
    exact (kernel_derivative seed M a B aB b terminal t (subset ht)).mono subset
  · exact evolution

theorem kernel_terminal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b ∈ Icc a B) (terminal : H) : kernel seed M a B aB b b terminal=terminal := by
  obtain ⟨path,atTerminal,evolution⟩ := exists_backward seed M terminal a b inside.1
  exact (kernel_original seed M a B aB b inside terminal path atTerminal evolution
    (right_mem_Icc.mpr inside.1)).trans atTerminal

theorem kernel_contracts (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b∈Icc a B) (terminal : H) (s : ℝ) (sample : s∈Icc a b) :
    ‖kernel seed M a B aB s b terminal‖ ≤ ‖terminal‖ := by
  let p := fun t => kernel seed M a B aB t b terminal
  have subset : Icc a b ⊆ Icc a B := Icc_subset_Icc le_rfl inside.2
  have derivative (t : ℝ) (ht : t∈Icc a b) :
      HasDerivWithinAt p (-dual seed M t (p t)) (Icc a b) t :=
    HasDerivWithinAt.mono (F := H) (kernel_derivative seed M a B aB b terminal t (subset ht)) subset
  have sign (t : ℝ) : 0 ≤ inner ℝ (p t) (-dual seed M t (p t)) := by
    rw [inner_neg_right (𝕜 := ℝ) (p t),← bath_dual,real_inner_comm (p t) (bath seed M t (p t))]
    exact neg_nonneg.mpr (bath_dissipative seed M t (p t))
  have increasing : MonotoneOn (fun t => ‖p t‖^2) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun t ht => ((derivative t ht).continuousWithinAt.norm.pow 2))
    · intro t ht
      exact (HasDerivWithinAt.norm_sq (F := H) (derivative t (interior_subset ht))).mono interior_subset
    · intro t _
      exact mul_nonneg (by norm_num) (sign t)
  have bound := increasing sample (right_mem_Icc.mpr inside.1) sample.2
  change ‖p s‖^2 ≤ ‖p b‖^2 at bound
  have terminalRead : p b=terminal := kernel_terminal seed M a B aB b inside terminal
  rw [terminalRead] at bound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp bound

theorem kernel_norm_le_one (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b∈Icc a B) (s : ℝ) (sample : s∈Icc a b) :
    ‖kernel seed M a B aB s b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using kernel_contracts seed M a B aB b inside v s sample

theorem kernel_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) :
    ContinuousOn (fun pair : ℝ×ℝ => kernel seed M a B aB pair.1 pair.2) ((Icc a B) ×ˢ (Icc a B)) := by
  have before : ContinuousOn (fun pair : ℝ×ℝ => backwardFlow seed M a B aB pair.1)
      ((Icc a B) ×ˢ (Icc a B)) :=
    (matrix_continuous (E := H) _ _ a B aB).comp continuous_fst.continuousOn (fun _ h => h.1)
  have after : ContinuousOn (endpoint seed M a B aB) (Icc a B) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H)).continuous.comp_continuousOn
      (matrix_continuous (E := H) _ _ a B aB)
  exact ContinuousOn.clm_comp (𝕜 := ℝ) (E := H) (F := H) (G := H) before
    (after.comp continuous_snd.continuousOn (fun _ h => h.2))


-- The adjoint kernel is the actual forward two-time propagator, with upper-time derivative B(t)U.
def propagate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B) (s b : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (kernel seed M a B aB s b)

theorem propagate_apply (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (s b : ℝ) (v : H) : propagate seed M a B aB s b v =
      forward seed M a B aB b
        (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (backwardFlow seed M a B aB s) v) := by
  have composed:=ContinuousLinearMap.adjoint_comp (𝕜 := ℝ) (E := H) (F := H) (G := H)
    (backwardFlow seed M a B aB s)
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (forward seed M a B aB b))
  have applied:=congrArg (fun op : H →L[ℝ] H => op v) composed
  simpa only [propagate,kernel,endpoint,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_apply] using! applied

theorem propagate_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (s : ℝ) (v : H) (t : ℝ) (inside : t ∈ Icc a B) :
    HasDerivWithinAt (fun b => propagate seed M a B aB s b v)
      (bath seed M t (propagate seed M a B aB s t v)) (Icc a B) t := by
  simpa only [propagate_apply] using! forward_derivative seed M a B aB
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (backwardFlow seed M a B aB s) v) t inside

theorem propagate_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (s : ℝ) (inside : s ∈ Icc a B) : propagate seed M a B aB s s = ContinuousLinearMap.id ℝ H := by
  have identity : kernel seed M a B aB s s=ContinuousLinearMap.id ℝ H :=
    ContinuousLinearMap.ext (kernel_terminal seed M a B aB s inside)
  simp only [propagate,identity,ContinuousLinearMap.adjoint_id]

theorem propagate_contracts (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a B : ℝ) (aB : a ≤ B)
    (b : ℝ) (inside : b∈Icc a B) (v : H) (s : ℝ) (sample : s∈Icc a b) :
    ‖propagate seed M a B aB s b v‖ ≤ ‖v‖ := by
  have normed : ‖propagate seed M a B aB s b‖ ≤ 1 := by
    rw [propagate,LinearIsometryEquiv.norm_map]
    exact kernel_norm_le_one seed M a B aB b inside s sample
  exact ((propagate seed M a B aB s b).le_opNorm v).trans
    ((mul_le_mul_of_nonneg_right normed (norm_nonneg v)).trans_eq (one_mul _))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem bath_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    bath seed M (step.2.clockAdvance+time)=bath step.1 M time :=
  congrArg (fun blocks => blocks.2.2.2)
    (NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative)

theorem dual_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    dual seed M (step.2.clockAdvance+time)=dual step.1 M time :=
  congrArg (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H))
    (bath_next seed M step generated time nonnegative)

theorem kernel_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a ≤ B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B)
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
      HasDerivWithinAt p (-dual step.1 M t (p t)) (Icc a b) t := by
    have into : MapsTo (fun r : ℝ => c+r) (Icc a b) (Icc (c+a) (c+B)) :=
      fun r hr => ⟨add_le_add_right hr.1 c,add_le_add_right (hr.2.trans inside.2) c⟩
    have old := kernel_derivative seed M (c+a) (c+B) (add_le_add_right aB c) (c+b) terminal (c+t) (into ht)
    have shifted := HasDerivWithinAt.scomp (F := H) t old ((hasDerivAt_id t).const_add c).hasDerivWithinAt into
    have actual := dual_next seed M step generated t (a0.trans ht.1)
    have valueRead := congrArg (fun op : H →L[ℝ] H => -(op (p t))) actual
    have rate : HasDerivWithinAt p (-dual seed M (c+t) (p t)) (Icc a b) t := by
      simpa only [one_smul,Function.comp_def] using! shifted
    exact valueRead ▸ rate
  exact (kernel_original step.1 M a B aB b inside terminal p terminalRead derivative sample).symm

theorem propagate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a ≤ B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B)
    (s : ℝ) (sample : s∈Icc a b) :
    propagate seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+s) (step.2.clockAdvance+b)=propagate step.1 M a B aB s b :=
  congrArg (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H))
    (kernel_next seed M step generated a B aB a0 b inside s sample)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalBath

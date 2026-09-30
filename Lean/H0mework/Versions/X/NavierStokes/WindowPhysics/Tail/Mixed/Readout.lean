import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Mixed.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeMixedHeatReadout
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowSpacetimeFourier NativeMixedHeatSource
noncomputable section

section Calculus
variable {Parameter Index E F G : Type*} {filter : Filter Parameter}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem clm_jets_uniform (L : F →L[ℝ] G) (f : Parameter → E → F) (target : E → F)
    {s : Set E} (opened : IsOpen s) (smooth : ∀ p, ContDiffOn ℝ ∞ (f p) s)
    (targetSmooth : ContDiffOn ℝ ∞ target s) (n : ℕ)
    (converges : TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (f p))
      (iteratedFDeriv ℝ n target) filter s) :
    TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (L ∘ f p))
      (iteratedFDeriv ℝ n (L ∘ target)) filter s := by
  let action := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => E) F G L
  have result := action.uniformContinuous.comp_tendstoUniformlyOn converges
  have changed := result.congr (Eventually.of_forall fun p x inside =>
    (L.iteratedFDeriv_comp_left ((smooth p).contDiffAt (opened.mem_nhds inside))
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).symm)
  exact changed.congr_right (fun x inside =>
    (L.iteratedFDeriv_comp_left (targetSmooth.contDiffAt (opened.mem_nhds inside))
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).symm)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem uniform_finset_sum (indices : Finset Index) (f : Index → Parameter → E → F) (target : Index → E → F)
    {s : Set E} (converges : ∀ i ∈ indices, TendstoUniformlyOn (f i) (target i) filter s) :
    TendstoUniformlyOn (fun p x => ∑ i∈indices, f i p x) (fun x => ∑ i∈indices, target i x) filter s := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (tendsto_const_nhds :
      Tendsto (fun _ : Parameter => (0 : F)) filter (𝓝 0)).tendstoUniformlyOn_const s
  | @insert i indices outside previous =>
    simpa only [Finset.sum_insert outside,Pi.add_apply] using!
      (converges i (Finset.mem_insert_self i indices)).add
        (previous (fun j member => converges j (Finset.mem_insert_of_mem member)))

theorem sum_jets_uniform (indices : Finset Index) (f : Index → Parameter → E → F) (target : Index → E → F)
    {s : Set E} (opened : IsOpen s)
    (smooth : ∀ i ∈ indices, ∀ p, ContDiffOn ℝ ∞ (f i p) s)
    (targetSmooth : ∀ i ∈ indices, ContDiffOn ℝ ∞ (target i) s) (n : ℕ)
    (converges : ∀ i ∈ indices, TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (f i p))
      (iteratedFDeriv ℝ n (target i)) filter s) :
    TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (fun x => ∑ i∈indices,f i p x))
      (iteratedFDeriv ℝ n (fun x => ∑ i∈indices,target i x)) filter s := by
  have result := uniform_finset_sum indices _ _ converges
  have changed := result.congr (Eventually.of_forall fun p x inside =>
    (iteratedFDeriv_fun_sum_apply (fun i member =>
      ((smooth i member p).contDiffAt (opened.mem_nhds inside)).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))).symm)
  exact changed.congr_right (fun x inside =>
    (iteratedFDeriv_fun_sum_apply (fun i member =>
      ((targetSmooth i member).contDiffAt (opened.mem_nhds inside)).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))).symm)

theorem add_jets_uniform (f g : Parameter → E → F) (first last : E → F)
    {s : Set E} (opened : IsOpen s)
    (smoothF : ∀ p, ContDiffOn ℝ ∞ (f p) s) (smoothG : ∀ p, ContDiffOn ℝ ∞ (g p) s)
    (smoothFirst : ContDiffOn ℝ ∞ first s) (smoothLast : ContDiffOn ℝ ∞ last s) (n : ℕ)
    (one : TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (f p)) (iteratedFDeriv ℝ n first) filter s)
    (two : TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (g p)) (iteratedFDeriv ℝ n last) filter s) :
    TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (fun x => f p x+g p x))
      (iteratedFDeriv ℝ n (fun x => first x+last x)) filter s := by
  have identity (u v : E → F) (us : ContDiffOn ℝ ∞ u s) (vs : ContDiffOn ℝ ∞ v s)
      (x : E) (inside : x∈s) :
      iteratedFDeriv ℝ n (fun x => u x+v x) x=iteratedFDeriv ℝ n u x+iteratedFDeriv ℝ n v x :=
    iteratedFDeriv_add_apply ((us.contDiffAt (opened.mem_nhds inside)).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤)))
      ((vs.contDiffAt (opened.mem_nhds inside)).of_le (by exact_mod_cast (le_top : (n : ℕ∞)≤⊤)))
  exact ((one.add two).congr (Eventually.of_forall fun p x inside =>
    (identity (f p) (g p) (smoothF p) (smoothG p) x inside).symm)).congr_right
      (fun x inside => (identity first last smoothFirst smoothLast x inside).symm)

theorem prod_jets_uniform (f : Parameter → E → F) (g : Parameter → E → G) (first : E → F) (last : E → G)
    {s : Set E} (opened : IsOpen s)
    (smoothF : ∀ p, ContDiffOn ℝ ∞ (f p) s) (smoothG : ∀ p, ContDiffOn ℝ ∞ (g p) s)
    (smoothFirst : ContDiffOn ℝ ∞ first s) (smoothLast : ContDiffOn ℝ ∞ last s) (n : ℕ)
    (one : TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (f p)) (iteratedFDeriv ℝ n first) filter s)
    (two : TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (g p)) (iteratedFDeriv ℝ n last) filter s) :
    TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (fun x => (f p x,g p x)))
      (iteratedFDeriv ℝ n (fun x => (first x,last x))) filter s := by
  let L:=ContinuousLinearMap.inl ℝ F G
  let R:=ContinuousLinearMap.inr ℝ F G
  have one' := clm_jets_uniform L f first opened smoothF smoothFirst n one
  have two' := clm_jets_uniform R g last opened smoothG smoothLast n two
  simpa only [L,R,Function.comp_apply,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,zero_add,add_zero] using add_jets_uniform
      (fun p => L ∘ f p) (fun p => R ∘ g p) (L ∘ first) (R ∘ last) opened
      (fun p => L.contDiff.comp_contDiffOn (smoothF p)) (fun p => R.contDiff.comp_contDiffOn (smoothG p))
      (L.contDiff.comp_contDiffOn smoothFirst) (R.contDiff.comp_contDiffOn smoothLast) n one' two'

theorem fderiv_jets_uniform (f : Parameter → E → F) (target : E → F)
    {s : Set E} (n : ℕ)
    (converges : TendstoUniformlyOn (fun p => iteratedFDeriv ℝ (n+1) (f p))
      (iteratedFDeriv ℝ (n+1) target) filter s) :
    TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (fderiv ℝ (f p)))
      (iteratedFDeriv ℝ n (fderiv ℝ target)) filter s := by
  have same (g : E → F) (x : E) : iteratedFDeriv ℝ n (fderiv ℝ g) x =
      continuousMultilinearCurryRightEquiv' ℝ n E F (iteratedFDeriv ℝ (n+1) g x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact (continuousMultilinearCurryRightEquiv' ℝ n E F).apply_symm_apply _ |>.symm
  have result :=
    (continuousMultilinearCurryRightEquiv' ℝ n E F).toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformlyOn converges
  exact (result.congr (Eventually.of_forall fun p x _ => (same (f p) x).symm)).congr_right
    (fun x _ => (same target x).symm)
end Calculus

section Assembly
variable {Index E Parameter : Type*} [Fintype Index] [DecidableEq Index]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {filter : Filter Parameter}

def realInjection (i : Index) : ℂ →L[ℝ] EuclideanSpace ℝ Index :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Index => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Index => if j=i then Complex.reCLM else 0)

omit [Fintype Index] in
theorem realInjection_apply (i j : Index) (z : ℂ) : realInjection i z j=if j=i then z.re else 0 := by
  by_cases same : j=i <;> simp [realInjection,same]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem assemble_eq (f : Index → E → ℂ) (x : E) :
    (WithLp.toLp 2 fun i => (f i x).re : EuclideanSpace ℝ Index)=∑ i,realInjection i (f i x) := by
  apply PiLp.ext
  intro j
  change (f j x).re=(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) j) (∑ i,realInjection i (f i x))
  rw [map_sum]
  simp only [PiLp.proj_apply,realInjection_apply]
  simp

theorem assembly_jets_uniform (f : Index → Parameter → E → ℂ) (target : Index → E → ℂ)
    {s : Set E} (opened : IsOpen s) (smooth : ∀ i p, ContDiffOn ℝ ∞ (f i p) s)
    (targetSmooth : ∀ i, ContDiffOn ℝ ∞ (target i) s) (n : ℕ)
    (converges : ∀ i, TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (f i p))
      (iteratedFDeriv ℝ n (target i)) filter s) :
    TendstoUniformlyOn (fun p => iteratedFDeriv ℝ n (fun x => (WithLp.toLp 2 fun i => (f i p x).re : EuclideanSpace ℝ Index)))
      (iteratedFDeriv ℝ n (fun x => (WithLp.toLp 2 fun i => (target i x).re : EuclideanSpace ℝ Index))) filter s := by
  simp_rw [assemble_eq]
  exact sum_jets_uniform Finset.univ (fun i p => realInjection i ∘ f i p)
    (fun i => realInjection i ∘ target i) opened
    (fun i _ p => (realInjection i).contDiff.comp_contDiffOn (smooth i p))
    (fun i _ => (realInjection i).contDiff.comp_contDiffOn (targetSmooth i)) n
    (fun i _ => clm_jets_uniform (realInjection i) (f i) (target i) opened (smooth i) (targetSmooth i) n (converges i))
end Assembly
end
end SaturationMonoid.NavierStokes.NativeMixedHeatReadout

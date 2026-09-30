import H0mework.Physics.LowEnergy.Quantum.SourceRetardedGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Finite source-core compressions. The finite sets generate their own
domain inclusion; no spectral domain or propagator is supplied. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.FiniteCoreEvolution
open SymmetricGraphClosure
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

def coreSpan (T : E →ₗ.[ℂ] E) (F : Finset T.domain) : Submodule ℂ E :=
  Submodule.span ℂ ((fun x : T.domain => (x : E)) '' (F : Set T.domain))

instance coreSpan_finite (T : E →ₗ.[ℂ] E) (F : Finset T.domain) :
    FiniteDimensional ℂ (coreSpan T F) :=
  FiniteDimensional.span_of_finite ℂ (F.finite_toSet.image _)

omit [CompleteSpace E] in
theorem coreSpan_le (T : E →ₗ.[ℂ] E) (F : Finset T.domain) : coreSpan T F ≤ T.domain := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, _, rfl⟩
  exact x.property

omit [CompleteSpace E] in
theorem mem_coreSpan (T : E →ₗ.[ℂ] E) (F : Finset T.domain) (x : T.domain) (hx : x ∈ F) :
    (x : E) ∈ coreSpan T F :=
  Submodule.subset_span ⟨x, hx, rfl⟩

omit [CompleteSpace E] in
theorem coreSpan_mono (T : E →ₗ.[ℂ] E) : Monotone (coreSpan T) := by
  intro F G h
  exact Submodule.span_mono (Set.image_mono h)

def finiteAction (T : E →ₗ.[ℂ] E) (F : Finset T.domain) : coreSpan T F →L[ℂ] coreSpan T F :=
  (((coreSpan T F).orthogonalProjectionOnto).toLinearMap.comp
    (T.toFun.comp (Submodule.inclusion (coreSpan_le T F)))).toContinuousLinearMap

omit [CompleteSpace E] in
theorem finiteAction_symmetric (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (F : Finset T.domain) : (finiteAction T F).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ ((coreSpan T F).orthogonalProjectionOnto (T ⟨x.val, coreSpan_le T F x.property⟩)) y =
    inner ℂ x ((coreSpan T F).orthogonalProjectionOnto (T ⟨y.val, coreSpan_le T F y.property⟩))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact symmetric ⟨x.val, coreSpan_le T F x.property⟩ ⟨y.val, coreSpan_le T F y.property⟩

def compression (T : E →ₗ.[ℂ] E) (F : Finset T.domain) : E →L[ℂ] E :=
  (coreSpan T F).subtypeL.comp ((finiteAction T F).comp (coreSpan T F).orthogonalProjectionOnto)

omit [CompleteSpace E] in
theorem compression_symmetric (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (F : Finset T.domain) : (compression T F).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ ((finiteAction T F ((coreSpan T F).orthogonalProjectionOnto x) : coreSpan T F) : E) y =
    inner ℂ x ((finiteAction T F ((coreSpan T F).orthogonalProjectionOnto y) : coreSpan T F) : E)
  rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact finiteAction_symmetric T symmetric F _ _

theorem compression_selfAdjoint (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (F : Finset T.domain) : IsSelfAdjoint (compression T F) :=
  (compression_symmetric T symmetric F).isSelfAdjoint

omit [CompleteSpace E] in
theorem compression_core (T : E →ₗ.[ℂ] E) (F : Finset T.domain)
    (x : T.domain) (hx : (x : E) ∈ coreSpan T F) :
    compression T F (x : E) = (coreSpan T F).starProjection (T x) := by
  change ((finiteAction T F ((coreSpan T F).orthogonalProjectionOnto (x : E))) : E) = _
  have hp : (coreSpan T F).orthogonalProjectionOnto (x : E) = ⟨(x : E), hx⟩ :=
    (coreSpan T F).orthogonalProjectionOnto_mem_subspace_eq_self ⟨(x : E), hx⟩
  rw [hp]
  rfl

omit [CompleteSpace E] in
theorem compression_core_bound (T : E →ₗ.[ℂ] E) (F : Finset T.domain)
    (x : T.domain) (hx : (x : E) ∈ coreSpan T F) :
    ‖compression T F (x : E)‖ ≤ ‖T x‖ := by
  rw [compression_core T F x hx]
  exact (coreSpan T F).norm_starProjection_apply_le (T x)

omit [CompleteSpace E] in
theorem compression_core_exact (T : E →ₗ.[ℂ] E) (F : Finset T.domain)
    (x : T.domain) (hTx : T x ∈ T.domain) (hx : x ∈ F)
    (hTxF : (⟨T x, hTx⟩ : T.domain) ∈ F) : compression T F (x : E) = T x := by
  rw [compression_core T F x (mem_coreSpan T F x hx)]
  exact Submodule.starProjection_eq_self_iff.mpr (mem_coreSpan T F ⟨T x, hTx⟩ hTxF)

def evolution (T : E →ₗ.[ℂ] E) (F : Finset T.domain) (t : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp (t • ((-Complex.I) • compression T F))

theorem evolution_unitary (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (F : Finset T.domain) (t : ℝ) : evolution T F t ∈ unitary (E →L[ℂ] E) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, (compression_selfAdjoint T symmetric F).star_eq]

theorem evolution_norm (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (F : Finset T.domain) (t : ℝ) (x : E) : ‖evolution T F t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (evolution_unitary T symmetric F t) x

theorem evolution_commute (T : E →ₗ.[ℂ] E) (F : Finset T.domain) (t : ℝ) :
    evolution T F t * compression T F = compression T F * evolution T F t := by
  have h : Commute (t • ((-Complex.I) • compression T F)) (compression T F) := by
    show (t • ((-Complex.I) • compression T F)) * compression T F =
      compression T F * (t • ((-Complex.I) • compression T F))
    simp only [smul_mul_assoc, mul_smul_comm]
  exact h.exp_left.eq

theorem evolution_derivative (T : E →ₗ.[ℂ] E) (F : Finset T.domain) (t : ℝ) (x : E) :
    HasDerivAt (fun s => evolution T F s x)
      ((-Complex.I) • evolution T F t (compression T F x)) t := by
  have h := hasDerivAt_exp_smul_const ((-Complex.I) • compression T F) t
  let ev := (ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ
  have he := ev.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt (fun s => evolution T F s x)
    ((evolution T F t) (((-Complex.I) • compression T F) x)) t at he
  simpa only [smul_apply, map_smul] using he

theorem evolution_core_uniform (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (F : Finset T.domain) (x : T.domain) (hx : (x : E) ∈ coreSpan T F) (s t : ℝ) :
    ‖evolution T F t (x : E)-evolution T F s (x : E)‖ ≤ ‖T x‖ * ‖t-s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun u _ => (evolution_derivative T F u (x : E)).hasDerivWithinAt)
    (fun u _ => ?_) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul, evolution_norm T symmetric F]
  exact compression_core_bound T F x hx

omit [CompleteSpace E] in
theorem projection_tendsto (T : E →ₗ.[ℂ] E) (dense : Dense (T.domain : Set E)) (x : E) :
    Filter.Tendsto (fun F : Finset T.domain => (coreSpan T F).starProjection x)
      Filter.atTop (nhds x) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  obtain ⟨y, hy, near⟩ := Metric.mem_closure_iff.mp (dense x) epsilon positive
  refine Filter.eventually_atTop.mpr ⟨{⟨y, hy⟩}, fun F hF => ?_⟩
  have hyF : y ∈ coreSpan T F := mem_coreSpan T F ⟨y, hy⟩
    (hF (Finset.mem_singleton_self (⟨y, hy⟩ : T.domain)))
  have bound : ‖x-(coreSpan T F).starProjection x‖ ≤ ‖x-y‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
      (⟨y, hyF⟩ : coreSpan T F)
  rw [dist_eq_norm, norm_sub_rev]
  exact bound.trans_lt (by simpa only [dist_eq_norm] using near)

omit [CompleteSpace E] in
theorem compression_tendsto (T : E →ₗ.[ℂ] E) (dense : Dense (T.domain : Set E))
    (x : T.domain) : Filter.Tendsto (fun F : Finset T.domain => compression T F (x : E))
      Filter.atTop (nhds (T x)) := by
  classical
  apply (projection_tendsto T dense (T x)).congr'
  refine Filter.eventually_atTop.mpr ⟨{x}, fun F hF => ?_⟩
  exact (compression_core T F x (mem_coreSpan T F x (hF (Finset.mem_singleton_self x)))).symm

theorem evolution_core_remainder (T : E →ₗ.[ℂ] E) (symmetric : FormalAdjointPair T T)
    (x : T.domain) (hTx : T x ∈ T.domain) (F : Finset T.domain)
    (hx : x ∈ F) (hTxF : (⟨T x, hTx⟩ : T.domain) ∈ F) (t h : ℝ) :
    ‖evolution T F (t+h) (x : E)-evolution T F t (x : E) -
      h • ((-Complex.I) • evolution T F t (T x))‖ ≤ ‖T ⟨T x, hTx⟩‖ * ‖h‖^2 := by
  let tx : T.domain := ⟨T x, hTx⟩
  have inF : T x ∈ coreSpan T F := mem_coreSpan T F tx hTxF
  have exactCore := compression_core_exact T F x hTx hx hTxF
  let velocity := (-Complex.I) • evolution T F t (T x)
  let f := fun u : ℝ => evolution T F u (x : E)-u • velocity
  let df := fun u : ℝ => (-Complex.I) • evolution T F u (T x)-velocity
  have hd (u : ℝ) : HasDerivAt f (df u) u := by
    have hg := (evolution_derivative T F u (x : E)).sub ((hasDerivAt_id u).smul_const velocity)
    change HasDerivAt f ((-Complex.I) • evolution T F u (compression T F (x : E)) -
      (1 : ℝ) • velocity) u at hg
    simpa only [df, exactCore, one_smul] using hg
  have hb (u : ℝ) (hu : u ∈ Metric.closedBall t ‖h‖) : ‖df u‖ ≤ ‖T tx‖*‖h‖ := by
    have hg := evolution_core_uniform T symmetric F tx inF t u
    have distance : ‖u-t‖ ≤ ‖h‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
    calc
      ‖df u‖ = ‖evolution T F u (T x)-evolution T F t (T x)‖ := by
        simp only [df, velocity, ← smul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul]
      _ ≤ ‖T tx‖*‖u-t‖ := hg
      _ ≤ ‖T tx‖*‖h‖ := mul_le_mul_of_nonneg_left distance (norm_nonneg _)
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Metric.closedBall t ‖h‖) => (hd u).hasDerivWithinAt) hb
    (convex_closedBall t ‖h‖) (Metric.mem_closedBall_self (norm_nonneg h))
    (show t+h ∈ Metric.closedBall t ‖h‖ by simp [Metric.mem_closedBall, dist_eq_norm])
  have identity : f (t+h)-f t = evolution T F (t+h) (x : E)-evolution T F t (x : E)-h • velocity := by
    simp only [f, add_smul]
    abel
  simpa only [identity, add_sub_cancel_left, mul_assoc, ← pow_two, velocity, tx] using estimate

#print axioms compression_selfAdjoint
#print axioms compression_core
#print axioms compression_core_bound
#print axioms evolution_norm
#print axioms evolution_core_uniform
#print axioms compression_tendsto
#print axioms evolution_core_remainder
end LowEnergy.FiniteCoreEvolution

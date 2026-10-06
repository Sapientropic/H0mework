import H0mework.Realization.Perfectification.Quantum.Forms.Inverse

/-! Orthogonal projection onto an actual closed derivative graph generates
its variational resolvent. The derivative graph supplies both the domain
and the positive energy identity. -/

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Forms.Graph

noncomputable section

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev Product := WithLp 2 (H × F)

def lift : H →L[ℂ] Product (H := H) (F := F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H F).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ H F)

omit [CompleteSpace H] [CompleteSpace F] in
theorem lift_apply (x : H) : lift (F := F) x = WithLp.toLp 2 (x, 0) := rfl

theorem lift_adjoint_apply (w : Product (H := H) (F := F)) : lift.adjoint w = w.fst := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, lift_apply, WithLp.prod_inner_apply]
  simp

variable (A : H →ₗ.[ℂ] F)

def graph : Submodule ℂ (Product (H := H) (F := F)) :=
  A.graph.comap (WithLp.linearEquiv 2 ℂ (H × F)).toLinearMap

omit [CompleteSpace H] [CompleteSpace F] in
theorem graph_closed (closed : A.IsClosed) : IsClosed (graph A : Set (Product (H := H) (F := F))) :=
  closed.preimage (WithLp.prod_continuous_ofLp 2 H F)

def projection (closed : A.IsClosed) : Product (H := H) (F := F) →L[ℂ] Product (H := H) (F := F) := by
  letI : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  exact (graph A).starProjection

theorem projection_mem (closed : A.IsClosed) (w : Product (H := H) (F := F)) : projection A closed w ∈ graph A := by
  let : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  exact (graph A).starProjection_apply_mem w

theorem projection_selfAdjoint (closed : A.IsClosed) : IsSelfAdjoint (projection A closed) := by
  let : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  exact isSelfAdjoint_starProjection (graph A)

def resolvent (closed : A.IsClosed) : H →L[ℂ] H :=
  lift.adjoint.comp ((projection A closed).comp lift)

theorem resolvent_selfAdjoint (closed : A.IsClosed) : IsSelfAdjoint (resolvent A closed) :=
  (projection_selfAdjoint A closed).adjoint_conj lift

theorem resolvent_apply (closed : A.IsClosed) (x : H) :
    resolvent A closed x = (projection A closed (lift x)).fst := lift_adjoint_apply _

theorem solution_mem (closed : A.IsClosed) (x : H) : resolvent A closed x ∈ A.domain := by
  have member := projection_mem A closed (lift x)
  change WithLp.ofLp (projection A closed (lift x)) ∈ A.graph at member
  obtain ⟨y, hy, _⟩ := A.mem_graph_iff.mp member
  rw [resolvent_apply]
  change (WithLp.ofLp (projection A closed (lift x))).1 ∈ A.domain
  rw [← hy]
  exact y.property

def solution (closed : A.IsClosed) (x : H) : A.domain := ⟨resolvent A closed x, solution_mem A closed x⟩

theorem solution_value (closed : A.IsClosed) (x : H) : A (solution A closed x) =
    (projection A closed (lift x)).snd := by
  have member := projection_mem A closed (lift x)
  change WithLp.ofLp (projection A closed (lift x)) ∈ A.graph at member
  obtain ⟨y, hy, hA⟩ := A.mem_graph_iff.mp member
  have same : y = solution A closed x := Subtype.ext (hy.trans (resolvent_apply A closed x).symm)
  rw [← same]
  exact hA

theorem projection_lift (closed : A.IsClosed) (x : H) :
    projection A closed (lift x) = WithLp.toLp 2 (resolvent A closed x, A (solution A closed x)) := by
  apply (WithLp.linearEquiv 2 ℂ (H × F)).injective
  exact Prod.ext (resolvent_apply A closed x).symm (solution_value A closed x).symm

theorem variational (closed : A.IsClosed) (x : H) (y : A.domain) :
    inner ℂ (x - resolvent A closed x) y.val = inner ℂ (A (solution A closed x)) (A y) := by
  let : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  have member : WithLp.toLp 2 (y.val, A y) ∈ graph A := A.mem_graph y
  have orthogonal := (graph A).starProjection_inner_eq_zero (lift x) (WithLp.toLp 2 (y.val, A y)) member
  change inner ℂ (lift x - projection A closed (lift x)) (WithLp.toLp 2 (y.val, A y)) = 0 at orthogonal
  rw [projection_lift, lift_apply, inner_sub_left, WithLp.prod_inner_apply, WithLp.prod_inner_apply] at orthogonal
  simp only [inner_zero_left, add_zero] at orthogonal
  rw [inner_sub_left]
  linear_combination orthogonal

theorem resolvent_injective (closed : A.IsClosed) (dense : Dense (A.domain : Set H)) :
    Function.Injective (resolvent A closed) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x zero
  change resolvent A closed x = 0 at zero
  have solutionZero : solution A closed x = 0 := Subtype.ext zero
  have mapZero : A (0 : A.domain) = 0 := A.toFun.map_zero
  apply dense.eq_zero_of_inner_left ℂ
  intro y hy
  have relation := variational A closed x ⟨y, hy⟩
  simpa only [zero, sub_zero, solutionZero, mapZero, inner_zero_left] using relation

theorem energy_identity (closed : A.IsClosed) (x : H) :
    (inner ℂ (x - resolvent A closed x) (resolvent A closed x)).re = ‖A (solution A closed x)‖ ^ 2 := by
  change (inner ℂ (x - resolvent A closed x) (solution A closed x).val).re = _
  rw [variational]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

end
end SaturationMonoid.Quantum.Forms.Graph

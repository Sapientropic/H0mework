import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceMinimalGraphParticular

/-! Weighted transposition uses the actual differential range, with no chosen extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceWeightedParticular
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (D : Submodule ℂ E) (P W : D →ₗ[ℂ] E)

def rangeClosure : Submodule ℂ E := (LinearMap.range P).topologicalClosure

instance : CompleteSpace (rangeClosure D P) := by
  unfold rangeClosure
  infer_instance

def intoRange : D →ₗ[ℂ] rangeClosure D P :=
  P.codRestrict _ (fun x => (LinearMap.range P).le_topologicalClosure
    (LinearMap.mem_range_self P x))

omit [CompleteSpace E] in
private theorem into_range_dense : DenseRange (intoRange D P) := by
  have hi : DenseRange (Set.inclusion
      (show (LinearMap.range P : Set E) ⊆ rangeClosure D P from
        (LinearMap.range P).le_topologicalClosure)) := by
    apply (denseRange_inclusion_iff _).mpr
    exact Set.Subset.rfl
  exact hi.comp P.surjective_rangeRestrict.denseRange (continuous_inclusion _)

def inverseOnRange : rangeClosure D P →L[ℂ] E := W.extendOfNorm (intoRange D P)

def solver : E →L[ℂ] E :=
  (rangeClosure D P).subtypeL.comp (inverseOnRange D P W).adjoint

variable (C : ℝ) (hC : 0 ≤ C) (localCost : ∀ v : D, ‖W v‖ ≤ C * ‖P v‖)

include localCost in
theorem range_return (v : D) : inverseOnRange D P W (intoRange D P v) = W v := by
  apply LinearMap.extendOfNorm_eq (into_range_dense D P)
  exact ⟨C, localCost⟩

include localCost hC in
theorem solver_bound : ‖solver D P W‖ ≤ C := by
  have hi : ‖inverseOnRange D P W‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    exact LinearMap.norm_extendOfNorm_apply_le (into_range_dense D P) C localCost
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖((inverseOnRange D P W).adjoint f : rangeClosure D P)‖ ≤ C * ‖f‖
  apply ((inverseOnRange D P W).adjoint.le_opNorm f).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right hi (norm_nonneg f)

include localCost in
/-- The equation is on the original tests, so the output need not be in the minimal graph. -/
theorem solver_equation (v : D) (f : E) :
    inner ℂ (P v) (solver D P W f) = inner ℂ (W v) f := by
  change inner ℂ (intoRange D P v) ((inverseOnRange D P W).adjoint f) = _
  rw [ContinuousLinearMap.adjoint_inner_right, range_return D P W C localCost]

end LowEnergy.SourceWeightedParticular

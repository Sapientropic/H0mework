import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.States.Vector
import Mathlib.Analysis.Normed.Module.WeakDual

/-! All coordinate vector states enter one weak-star compact set. Their
common cluster preserves positivity, normalization and the complete actual
conjugation action, without uniform time continuity of the bounded product. -/

set_option autoImplicit false

open Filter Topology
open scoped ComplexOrder

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]
  (U : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k))

def invariantBall : Set (WeakDual ℂ (Bounded E)) :=
  (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1) ∩ {φ | φ 1 = 1} ∩
    {φ | ∀ A, 0 ≤ φ (star A * A)} ∩ {φ | ∀ t A, φ (action E U t A) = φ A}

theorem invariantBall_compact : IsCompact (invariantBall E U) := by
  have normalized : IsClosed {φ : WeakDual ℂ (Bounded E) | φ 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have positive : IsClosed {φ : WeakDual ℂ (Bounded E) | ∀ A, 0 ≤ φ (star A * A)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun A => isClosed_le continuous_const (WeakDual.eval_continuous (star A * A))
  have invariant : IsClosed {φ : WeakDual ℂ (Bounded E) | ∀ t A, φ (action E U t A) = φ A} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun A =>
      isClosed_eq (WeakDual.eval_continuous (action E U t A)) (WeakDual.eval_continuous A)
  exact (((WeakDual.isCompact_closedBall (𝕜 := ℂ) (E := Bounded E) 0 1).inter_right normalized).inter_right
    positive).inter_right invariant

variable (v : ∀ k, E k) (normalized : ∀ k, ‖v k‖ = 1) (fixed : ∀ k t, U k t (v k) = v k)

def weakVector (k : ℕ) : WeakDual ℂ (Bounded E) := StrongDual.toWeakDual (vectorState E v k)

include normalized fixed in
theorem weakVector_mem (k : ℕ) : weakVector E v k ∈ invariantBall E U := by
  refine ⟨⟨⟨?_, vectorState_one E v normalized k⟩, vectorState_positive E v k⟩,
    fun t A => vectorState_invariant E v U fixed k t A⟩
  change vectorState E v k ∈ Metric.closedBall (0 : StrongDual ℂ (Bounded E)) 1
  simpa only [Metric.mem_closedBall, dist_zero_right] using vectorState_norm_le_one E v normalized k

include normalized fixed in
theorem invariant_cluster_exists : ∃ φ : Bounded E →L[ℂ] ℂ,
    ‖φ‖ ≤ 1 ∧ φ 1 = 1 ∧ (∀ A, 0 ≤ φ (star A * A)) ∧
      (∀ t A, φ (action E U t A) = φ A) ∧
      MapClusterPt (StrongDual.toWeakDual φ) atTop (weakVector E v) := by
  obtain ⟨φ, member, cluster⟩ := (invariantBall_compact E U).exists_mapClusterPt (f := atTop) <|
    Filter.tendsto_principal.mpr (Filter.Eventually.of_forall (weakVector_mem E U v normalized fixed))
  refine ⟨φ.toStrongDual, ?_, member.1.1.2, member.1.2, member.2, cluster⟩
  have bound := member.1.1.1
  change φ.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ (Bounded E)) 1 at bound
  simpa only [Metric.mem_closedBall, dist_zero_right] using bound

end
end SaturationMonoid.Quantum.Dynamics

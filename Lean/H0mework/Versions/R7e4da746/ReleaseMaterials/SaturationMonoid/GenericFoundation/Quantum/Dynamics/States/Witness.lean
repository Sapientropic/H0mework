import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.States.Asymptotic

/-! The original vector-state family generates one shared cluster witness. -/

set_option autoImplicit false

open Filter Topology
open scoped ComplexOrder

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]
  (U : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k)) (v : ∀ k, E k)

structure ClusterWitness where
  private mk ::
  full : Bounded E →L[ℂ] ℂ
  norm_bound : ‖full‖ ≤ 1
  normalized : full 1 = 1
  square_positive : ∀ A, 0 ≤ full (star A * A)
  invariant : ∀ t A, full (action E U t A) = full A
  cluster : MapClusterPt (StrongDual.toWeakDual full) atTop (weakVector E v)

theorem clusterWitness_exists (normalized : ∀ k, ‖v k‖ = 1) (fixed : ∀ k t, U k t (v k) = v k) :
    Nonempty (ClusterWitness E U v) := by
  obtain ⟨φ, bound, unit, positive, invariant, cluster⟩ := invariant_cluster_exists E U v normalized fixed
  exact ⟨⟨φ, bound, unit, positive, invariant, cluster⟩⟩

theorem clusterWitness_of_asymptotic (normalized : ∀ k, ‖v k‖ = 1)
    (sourceLimit : ∀ t A, Tendsto
      (fun k => vectorState E v k (action E U t A) - vectorState E v k A) atTop (𝓝 0)) :
    Nonempty (ClusterWitness E U v) := by
  obtain ⟨φ, bound, unit, positive, invariant, cluster⟩ :=
    asymptotic_invariant_cluster_exists E U v normalized sourceLimit
  exact ⟨⟨φ, bound, unit, positive, invariant, cluster⟩⟩

end
end SaturationMonoid.Quantum.Dynamics

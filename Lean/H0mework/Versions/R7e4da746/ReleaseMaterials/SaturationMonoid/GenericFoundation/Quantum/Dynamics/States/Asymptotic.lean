import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.States.Compact

/-! The existing cluster producer already supplies a common positive state.
Asymptotic source invariance determines its action without requiring an exact
fixed vector at each coordinate. -/

set_option autoImplicit false

open Filter Topology
open scoped ComplexOrder

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]
  (U : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k))
  (v : ∀ k, E k) (normalized : ∀ k, ‖v k‖ = 1)

include normalized in
theorem asymptotic_invariant_cluster_exists
    (sourceLimit : ∀ t A, Tendsto
      (fun k => vectorState E v k (action E U t A) - vectorState E v k A) atTop (𝓝 0)) :
    ∃ φ : Bounded E →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1 = 1 ∧ (∀ A, 0 ≤ φ (star A * A)) ∧
        (∀ t A, φ (action E U t A) = φ A) ∧
        MapClusterPt (StrongDual.toWeakDual φ) atTop (weakVector E v) := by
  obtain ⟨φ, bound, unit, positive, _, cluster⟩ :=
    invariant_cluster_exists E (fun _ => 1) v normalized (fun _ _ => rfl)
  refine ⟨φ, bound, unit, positive, ?_, cluster⟩
  intro t A
  let B : Bounded E := action E U t A - A
  have image := cluster.continuousAt_comp (WeakDual.eval_continuous B).continuousAt
  have limit : Tendsto ((fun ψ : WeakDual ℂ (Bounded E) => ψ B) ∘ weakVector E v)
      atTop (𝓝 0) := by
    change Tendsto (fun k => vectorState E v k (action E U t A - A)) atTop (𝓝 0)
    simpa only [map_sub] using sourceLimit t A
  have zero : φ B = 0 := eq_of_nhds_neBot (image.clusterPt.mono limit)
  exact sub_eq_zero.mp ((map_sub φ (action E U t A) A).symm.trans zero)

end
end SaturationMonoid.Quantum.Dynamics

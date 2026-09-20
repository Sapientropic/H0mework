import H0mework.Physics.MotherLaws.CompletionCompactDensity

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion

open Set Filter UniformSpace
open scoped Topology

noncomputable section

theorem compact_vector_approximation (n m : ℕ) (K : Set (Fin n → ℝ)) [CompactSpace K]
    (f : C((Fin n → ℝ), (Fin m → ℝ))) (ε : ℝ) (positive : 0 < ε) :
    ∃ p : Fin m → MvPolynomial (Fin n) ℚ, ∀ x ∈ K,
      dist (readPolynomials n m p x) (f x) < ε := by
  let component (i : Fin m) : C(K, ℝ) :=
    ⟨fun x => f x.val i, (continuous_apply i).comp (f.continuous.comp continuous_subtype_val)⟩
  have approximation (i : Fin m) :=
    compact_polynomial_approximation n K (component i) ε positive
  choose polynomial near using approximation
  refine ⟨polynomial, fun x hx => (dist_pi_lt_iff positive).mpr fun i => ?_⟩
  exact near i ⟨x, hx⟩

/-- Density is for the compact-convergence uniformity on the whole Euclidean domain. -/
theorem polynomials_dense (n m : ℕ) : DenseRange (readPolynomials n m) := by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity (Metric.uniformity_basis_dist.compactConvergenceUniformity))]
  rintro ⟨K, ε⟩ ⟨compact, positive⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp compact
  obtain ⟨polynomial, near⟩ := compact_vector_approximation n m K f ε positive
  refine ⟨readPolynomials n m polynomial, ⟨polynomial, rfl⟩, ?_⟩
  intro x hx
  exact near x hx

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion

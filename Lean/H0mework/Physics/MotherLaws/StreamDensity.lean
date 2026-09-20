import H0mework.Physics.MotherLaws.StreamSource
import H0mework.Physics.MotherLaws.StreamTopology
import H0mework.Physics.MotherLaws.CompletionNative

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws

open Set Filter UniformSpace MotherFamilyOccurrence
open Stage9C.Revision
open scoped Topology Uniformity

noncomputable section

theorem compact_stream_approximation (K : Set Stream) [CompactSpace K]
    (f : C(Stream, Stream)) (m : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ n, ∃ polynomial : Fin m → MvPolynomial (Fin n) ℚ,
      ∀ x ∈ K, ∀ output : Fin m,
        dist (liftFinite n m (MotherLawCompletion.readPolynomials n m polynomial) x output.val)
          (f x output.val) < ε := by
  let component (output : Fin m) : C(K, ℝ) :=
    ⟨fun x => f x.val output.val,
      (continuous_apply output.val).comp (f.continuous.comp continuous_subtype_val)⟩
  have approximation (output : Fin m) :=
    compact_scalar_approximation K (component output) ε positive
  choose family near using approximation
  obtain ⟨n, polynomial, generated⟩ := polynomial_prefix family
  refine ⟨n, polynomial, fun x hx output => ?_⟩
  rw [liftFinite_apply, MotherLawCompletion.readPolynomials_apply]
  have result := near output ⟨x, hx⟩
  have same : MotherLawCompletion.scalarPolynomial (family output) x =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (inputPrefix n x) (polynomial output) := by
    change MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (family output) = _
    rw [← generated output, MvPolynomial.eval₂_rename]
    rfl
  rw [same] at result
  exact result

/-- The source's finite laws are dense for compact convergence on the whole stream space. -/
theorem finiteNativeLaw_dense : DenseRange finiteNativeLaw := by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity stream_uniformity_basis.compactConvergenceUniformity)]
  rintro ⟨K, m, ε⟩ ⟨compact, positive⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp compact
  obtain ⟨n, polynomial, near⟩ := compact_stream_approximation K f m ε positive
  obtain ⟨polynomialCode, generated⟩ := MotherFiniteLaws.every_polynomial polynomial
  have finite_eq : MotherFiniteLaws.finiteLaw n m (SpinPair.visit (10 + polynomialCode)) =
      MotherLawCompletion.readPolynomials n m polynomial := by
    rw [MotherLawCompletion.finiteLaw_eq_polynomial, generated]
  obtain ⟨code, formed⟩ := every_finite_law n m (SpinPair.visit (10 + polynomialCode))
  rw [finite_eq] at formed
  refine ⟨finiteNativeLaw (SpinPair.visit (10 + code)), ⟨SpinPair.visit (10 + code), rfl⟩, ?_⟩
  rw [formed]
  intro x hx output bound
  exact near x hx ⟨output, bound⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws

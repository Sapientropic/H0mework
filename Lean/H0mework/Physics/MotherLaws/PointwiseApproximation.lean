import H0mework.Physics.MotherLaws.StreamSource
import H0mework.Physics.MotherLaws.CompletionNative

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws

open Set MotherStreamLaws MotherFamilyOccurrence
open Stage9C.Revision

noncomputable section

/-- The original mother-history factory, retaining its entire function value. -/
def finiteLaw (visit : MotherVisit) : Stream → Stream := finiteNativeLaw visit

theorem finite_polynomial_approximation (K : Set Stream) (finite : K.Finite)
    (target : Stream → Stream) (m : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ n, ∃ polynomial : Fin m → MvPolynomial (Fin n) ℚ,
      ∀ x ∈ K, ∀ output : Fin m,
        dist (liftFinite n m (MotherLawCompletion.readPolynomials n m polynomial) x output.val)
          (target x output.val) < ε := by
  have : Finite K := finite.to_subtype
  let component (output : Fin m) : C(K, ℝ) :=
    ⟨fun x => target x.val output.val, continuous_of_discreteTopology⟩
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

theorem finite_native_approximation (K : Set Stream) (finite : K.Finite)
    (target : Stream → Stream) (m : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ code : ℕ, ∀ x ∈ K, ∀ output < m,
      dist (finiteLaw (SpinPair.visit (10 + code)) x output) (target x output) < ε := by
  obtain ⟨n, polynomial, near⟩ := finite_polynomial_approximation K finite target m ε positive
  obtain ⟨polynomialCode, generated⟩ := MotherFiniteLaws.every_polynomial polynomial
  have finite_eq : MotherFiniteLaws.finiteLaw n m (SpinPair.visit (10 + polynomialCode)) =
      MotherLawCompletion.readPolynomials n m polynomial := by
    rw [MotherLawCompletion.finiteLaw_eq_polynomial, generated]
  obtain ⟨code, formed⟩ := every_finite_law n m (SpinPair.visit (10 + polynomialCode))
  rw [finite_eq] at formed
  refine ⟨code, fun x hx output bound => ?_⟩
  change dist (finiteNativeLaw (SpinPair.visit (10 + code)) x output) _ < ε
  rw [formed]
  exact near x hx ⟨output, bound⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws

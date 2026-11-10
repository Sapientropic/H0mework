import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Polynomials
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Quantum
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Terminal.Native.Lorentz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! The field-content clause of Yang--Mills recognition. The gauge-labelled
fields themselves generate the physical Hilbert space. This is a target clause;
its renormalization and short-distance identities are additional clauses, not
consequences of naming this linear map. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Terminal

noncomputable section

private def unitTerm (G : GaugeGroup) : PolynomialTerm G where
  arity := 0
  tensor := ⟨ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => G.Algebra) 1,
    by intro generator values; simp⟩
  addresses := Fin.elim0

def unitPolynomial (G : GaugeGroup) : differentialPolynomials G :=
  ⟨(unitTerm G).evaluate, Submodule.subset_span ⟨unitTerm G, rfl⟩⟩

theorem unitPolynomial_apply (G : GaugeGroup) (configuration : Connection G)
    (point : Spacetime) : (unitPolynomial G).val (configuration, point) = 1 := rfl

def polynomialLevel (G : GaugeGroup) (dimension : ℕ) :
    Submodule ℝ (differentialPolynomials G) :=
  (polynomialsAtMost G dimension).comap (differentialPolynomials G).subtype

theorem polynomialLevel_mono (G : GaugeGroup) : Monotone (polynomialLevel G) := by
  intro first second leq
  exact Submodule.comap_mono (polynomialsAtMost_mono G leq)

def testDerivative (direction : Fin 4) : Test →L[ℂ] Test :=
  LineDeriv.lineDerivOpCLM ℂ Test (axis direction)

def ClassicalDerivative (G : GaugeGroup) (direction : Fin 4)
    (before after : differentialPolynomials G) : Prop :=
  ∀ configuration point,
    HasDerivAt (fun parameter : ℝ =>
      before.val (configuration, point + parameter • axis direction))
      (after.val (configuration, point)) 0

/-- The correspondence is linear and may mix operators under renormalization.
It is not a pointwise algebra homomorphism or a canonical bijection. -/
structure GaugeFieldContent (G : GaugeGroup) (Q : QuantumCore) where
  renormalized : differentialPolynomials G →ₗ[ℝ] Q.Components
  unit : ∀ (test : Test) (vector : Q.domain),
    Q.field (renormalized (unitPolynomial G)) test vector =
      (∫ point : Spacetime, test point) • vector
  -- Physical fields, rather than auxiliary component labels, must transform
  -- as the actual curvature tensors at the same spacetime point.
  covariant : ∀ dimension spin (polynomial : polynomialLevel G dimension),
    ∃ transformed : polynomialLevel G dimension,
      NativeLorentz.Related G spin polynomial.val transformed.val ∧
        ∀ test (vector : Q.domain),
          Q.field (Q.componentAction spin (renormalized polynomial.val)) test vector =
            Q.field (renormalized transformed.val) test vector
  derivative : ∀ direction before after, ClassicalDerivative G direction before after →
    ∀ (test : Test) (vector : Q.domain),
      Q.field (renormalized after) test vector =
        -Q.field (renormalized before) (testDerivative direction test) vector
  cyclic : Dense ((Submodule.span ℂ (Set.range
    (fun word : List (differentialPolynomials G × Test) =>
      (word.foldr (fun letter vector => Q.field (renormalized letter.1) letter.2 vector)
        ⟨Q.vacuum, Q.vacuum_mem⟩).val))) : Set Q.Hilbert)

namespace GaugeFieldContent

variable {G : GaugeGroup} {Q : QuantumCore} (content : GaugeFieldContent G Q)

theorem lorentz_covariant (dimension : ℕ) (spin : Spin)
    (polynomial : polynomialLevel G dimension) :
    ∃ transformed : polynomialLevel G dimension,
      NativeLorentz.Related G spin polynomial.val transformed.val ∧
        ∀ test (vector : Q.domain),
          Q.lorentz spin (Q.field (content.renormalized polynomial.val) test vector).val =
            (Q.field (content.renormalized transformed.val) (lorentzTest spin test)
              ⟨Q.lorentz spin vector.val, Q.lorentz_domain spin vector⟩).val := by
  obtain ⟨transformed, related, same⟩ := content.covariant dimension spin polynomial
  refine ⟨transformed, related, ?_⟩
  intro test vector
  rw [Q.lorentz_covariant]
  exact congrArg Subtype.val (same _ _)

def word (letters : List (differentialPolynomials G × Test)) (vector : Q.domain) : Q.domain :=
  letters.foldr (fun letter value => Q.field (content.renormalized letter.1) letter.2 value) vector

def correlation (letters : List (differentialPolynomials G × Test)) : ℂ :=
  inner ℂ Q.vacuum (content.word letters ⟨Q.vacuum, Q.vacuum_mem⟩).val

def matrixElement (first second : Q.domain)
    (letters : List (differentialPolynomials G × Test)) : ℂ :=
  inner ℂ first.val (content.word letters second).val

end GaugeFieldContent
end
end SaturationMonoid.PhysicsCore.YangMills.Terminal

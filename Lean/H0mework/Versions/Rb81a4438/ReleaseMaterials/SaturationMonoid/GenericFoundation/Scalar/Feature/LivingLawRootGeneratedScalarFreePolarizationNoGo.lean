import H0mework.Realization.Feature.GramPerfectification

/-!
# No free natural positive polarization from algebraic duality

The complex line has a faithful purely algebraic dual evaluation.  Even so,
scaling by two proves that no sesquilinear form can be both nondegenerate and
invariant under every algebraic linear equivalence.  An actual feature map or
polarization incidence is therefore indispensable.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedComplexFeaturePerfectification

noncomputable section

/-- A faithful purely algebraic evaluation on the complex line. -/
def complexLineAlgebraicDualEvaluation :
    ℂ →ₗ[ℂ] Module.Dual ℂ ℂ :=
  LinearMap.lsmul ℂ ℂ

theorem complexLineAlgebraicDualEvaluation_injective :
    Function.Injective complexLineAlgebraicDualEvaluation := by
  intro left right equality
  have atOne := LinearMap.congr_fun equality 1
  simpa [complexLineAlgebraicDualEvaluation] using atOne

/-- Minimal laws inherited from a positive Hermitian polarization, together
with invariance under every algebraic linear equivalence.  `nonzero_one` is
strictly weaker than positive-definiteness. -/
structure NaturalAlgebraicPolarizationCandidate where
  form : ℂ → ℂ → ℂ
  smul_left : ∀ scalar left right,
    form (scalar * left) right = star scalar * form left right
  smul_right : ∀ scalar left right,
    form left (scalar * right) = scalar * form left right
  nonzero_one : form 1 1 ≠ 0
  invariant : ∀ equivalence : ℂ ≃ₗ[ℂ] ℂ, ∀ left right,
    form (equivalence left) (equivalence right) = form left right

def scaleTwo : ℂ ≃ₗ[ℂ] ℂ where
  toFun value := 2 * value
  invFun value := value / 2
  map_add' := by intro left right; ring
  map_smul' := by intro scalar value; simp only [RingHom.id_apply]; ring
  left_inv := by intro value; ring
  right_inv := by intro value; ring

/-- Scaling by two forces every universally natural sesquilinear form to
degenerate on the complex line. -/
theorem no_naturalAlgebraicPolarizationCandidate :
    IsEmpty NaturalAlgebraicPolarizationCandidate := by
  constructor
  intro candidate
  let diagonal := candidate.form 1 1
  have invariant := candidate.invariant scaleTwo 1 1
  have scaled : candidate.form (scaleTwo 1) (scaleTwo 1) =
      4 * diagonal := by
    calc
      candidate.form (scaleTwo 1) (scaleTwo 1) =
          candidate.form (2 * 1) (2 * 1) := rfl
      _ = star (2 : ℂ) * candidate.form 1 (2 * 1) :=
        candidate.smul_left 2 1 (2 * 1)
      _ = star (2 : ℂ) * ((2 : ℂ) * candidate.form 1 1) := by
        rw [candidate.smul_right]
      _ = 4 * diagonal := by
        simp [diagonal]
        ring
  have four_eq_one : 4 * diagonal = diagonal :=
    scaled.symm.trans invariant
  have three_mul_zero : (3 : ℂ) * diagonal = 0 := by
    calc
      (3 : ℂ) * diagonal = 4 * diagonal - diagonal := by ring
      _ = diagonal - diagonal := by rw [four_eq_one]
      _ = 0 := sub_self diagonal
  have diagonal_zero : diagonal = 0 :=
    (mul_eq_zero.mp three_mul_zero).resolve_left (by norm_num)
  exact candidate.nonzero_one diagonal_zero

theorem algebraicDualEvaluation_faithful_but_no_natural_polarization :
    Function.Injective complexLineAlgebraicDualEvaluation ∧
      IsEmpty NaturalAlgebraicPolarizationCandidate :=
  ⟨complexLineAlgebraicDualEvaluation_injective,
    no_naturalAlgebraicPolarizationCandidate⟩

end

end SourceGeneratedComplexFeaturePerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

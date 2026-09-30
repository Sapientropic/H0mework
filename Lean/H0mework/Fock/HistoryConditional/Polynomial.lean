import H0mework.Fock.HistoryConditional.WordOperatorConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

open SourceGeneratedActionWords SourceCyclicModule Polynomial
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem index_formula (word : List (Option Nat)) (state : Nat) :
    SourceCopyWordAffine.execute (SourceCopyWordAffine.compile word) state =
      (SourceCopyWordAffine.compile word).1 * state +
        ((SourceCopyWordAffine.compile word).1 + (SourceCopyWordAffine.compile word).2 - 1) := by
  apply Nat.add_right_cancel (m := 1)
  rw [index_exact, Nat.mul_add, Nat.mul_one]
  have positive := slope_positive word
  omega

def polynomial (depth : Nat) (word : List (Fock.Letter depth)) (p : Polynomial ℤ) : Polynomial ℤ :=
  coefficients.symm (action depth word (program p))

theorem polynomial_source (depth : Nat) (word : List (Fock.Letter depth)) (p : Polynomial ℤ) :
    program (polynomial depth word p) = action depth word (program p) := by
  rw [program_is_coefficients]
  exact coefficients.apply_symm_apply _

theorem polynomial_add (depth : Nat) (word : List (Fock.Letter depth)) (p q : Polynomial ℤ) :
    polynomial depth word (p + q) = polynomial depth word p + polynomial depth word q := by
  unfold polynomial
  rw [program_add, map_add, map_add]

theorem polynomial_monomial (depth : Nat) (word : List (Fock.Letter depth)) (state : Nat) (coefficient : ℤ) :
    polynomial depth word (monomial state coefficient) =
      monomial (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) state) coefficient := by
  apply program_injective
  rw [polynomial_source, program_monomial, program_monomial]
  exact Finsupp.mapDomain_single

theorem polynomial_formula (depth : Nat) (word : List (Fock.Letter depth)) (p : Polynomial ℤ) :
    polynomial depth word p =
      X ^ ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 +
        (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 - 1) *
          expand ℤ (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [polynomial_add, map_add, mul_add, hp, hq]
  | monomial n coefficient =>
      rw [polynomial_monomial, expand_monomial, ← monomial_one_right_eq_X_pow, monomial_mul_monomial, one_mul]
      apply congrArg (fun degree => monomial degree coefficient)
      rw [index_formula]
      ring

theorem complete_polynomial (depth : Nat) (word : List (Fock.Letter depth)) (p : Polynomial ℤ) :
    run (Fock.Complete.action depth) word (SourceCopyProgram.complete depth (program p)) =
      SourceCopyProgram.complete depth (program (polynomial depth word p)) := by
  rw [polynomial_source]
  exact complete_action depth word (program p)

end
end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Arithmetic.PrimeSearch.P337

/-!
# Proposition 338: unified P312+ direct package

P328 exposed the P312+ closed forms and a direct finite Goldbach search.
P337 refined the search surface so that the returned value itself is a sound
witness.  This file packages the three requested direct artifacts behind one
canonical certificate:

1. retention density/gamma-law closed forms;
2. sigma-atomic algebraic positions on the nondegenerate interval;
3. a direct Goldbach search algorithm returning a certified pair.

Boundary: this is still pointwise finite computation.  It proves that returned
witnesses are correct and that search success is equivalent to the pointwise
Goldbach predicate/coefficient positivity at the chosen input.  It does not
prove the global Goldbach conjecture.
-/

open MeasureTheory ProbabilityTheory
open scoped Real Topology ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Canonical direct Goldbach search -/

/-- Canonical one-dimensional Goldbach search: scan `p ≤ n` and return the
pair `(p, n-p)`. -/
def goldbachDirectSearch (n : ℕ) : Option (ℕ × ℕ) :=
  finitePairSearchPair n (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q)

/-- THEOREM 1: the canonical direct search returns only genuine Goldbach
pairs. -/
theorem goldbachDirectSearch_sound
    {n : ℕ} {pair : ℕ × ℕ}
    (h : goldbachDirectSearch n = some pair) :
    GoldbachPairPredicate n pair := by
  exact finitePairSearchPair_primePair_sound h

/-- THEOREM 2: a returned canonical pair has the shape `(p, n-p)` and both
entries are prime. -/
theorem goldbachDirectSearch_shape
    {n : ℕ} {pair : ℕ × ℕ}
    (h : goldbachDirectSearch n = some pair) :
    pair.1 ≤ n ∧ pair.2 = n - pair.1 ∧
      Nat.Prime pair.1 ∧ Nat.Prime pair.2 := by
  exact finitePairSearchPair_sound
    (P := fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) h

/-- THEOREM 3: canonical direct search succeeds exactly at the ordinary
pointwise Goldbach predicate. -/
theorem goldbachDirectSearch_isSome_iff_goldbach
    (n : ℕ) :
    (goldbachDirectSearch n).isSome = true ↔
      HasPrimeAdditiveDecomposition n := by
  exact finitePairSearchPair_primePair_isSome_iff_goldbach n

/-- THEOREM 4: canonical direct search succeeds exactly when the Goldbach
prime-indicator convolution coefficient is positive. -/
theorem goldbachDirectSearch_isSome_iff_coefficient_pos
    (n : ℕ) :
    (goldbachDirectSearch n).isSome = true ↔
      0 < goldbachConvolutionCoefficient n := by
  exact (goldbachDirectSearch_isSome_iff_goldbach n).trans
    (goldbachConvolutionCoefficient_pos_iff n).symm

/-! ## Unified direct certificate -/

/-- The direct P312+ package: closed-form retention, closed-form sigma-atomic
positions, and certified Goldbach direct search. -/
structure P338UnifiedP312PlusDirectCertificate where
  retention_density_closed :
    ∀ {shape rate time : ℝ}, 0 < shape -> 0 < rate -> 0 ≤ time ->
      GammaMixtureForgetting.normalizedGammaDensityLaplace shape rate time =
        (1 + time / rate) ^ (-shape)
  retention_gamma_measure_closed :
    ∀ {shape rate time : ℝ}, 0 < shape -> 0 < rate -> 0 ≤ time ->
      (∫ x, Real.exp (-(x * time)) ∂
        (ProbabilityTheory.gammaMeasure shape rate)) =
        (1 + time / rate) ^ (-shape)
  sigma_atomic_position_closed :
    ∀ (σ : ℝ) (p : PrimeExponent),
      sigmaAtomicClosedPosition σ p = 1 - (1 - σ) ^ p.1
  sigma_atomic_keep_closed :
    ∀ (σ : ℝ) (p : PrimeExponent),
      1 - sigmaAtomicClosedPosition σ p = (1 - σ) ^ p.1
  sigma_atomic_iterated_rate :
    ∀ (σ : ℝ) (p : PrimeExponent),
      sigmaAtomicClosedPosition σ p = iteratedRate σ p.1
  sigma_atomic_position_faithful :
    ∀ {σ : ℝ}, 0 < σ -> σ < 1 ->
      Function.Injective (sigmaAtomicClosedPosition σ)
  direct_search_sound :
    ∀ {n : ℕ} {pair : ℕ × ℕ},
      goldbachDirectSearch n = some pair -> GoldbachPairPredicate n pair
  direct_search_shape :
    ∀ {n : ℕ} {pair : ℕ × ℕ},
      goldbachDirectSearch n = some pair ->
        pair.1 ≤ n ∧ pair.2 = n - pair.1 ∧
          Nat.Prime pair.1 ∧ Nat.Prime pair.2
  direct_search_iff_goldbach :
    ∀ n : ℕ,
      (goldbachDirectSearch n).isSome = true ↔
        HasPrimeAdditiveDecomposition n
  direct_search_iff_coefficient_pos :
    ∀ n : ℕ,
      (goldbachDirectSearch n).isSome = true ↔
        0 < goldbachConvolutionCoefficient n

/-- THEOREM 5: the canonical unified P312+ direct package. -/
theorem p338UnifiedP312PlusDirectCertificate :
    P338UnifiedP312PlusDirectCertificate where
  retention_density_closed := by
    intro shape rate time hshape hrate htime
    exact retentionDensityClosedForm hshape hrate htime
  retention_gamma_measure_closed := by
    intro shape rate time hshape hrate htime
    exact retentionGammaMeasureClosedForm hshape hrate htime
  sigma_atomic_position_closed := by
    intro σ p
    rfl
  sigma_atomic_keep_closed := by
    intro σ p
    exact keep_sigmaAtomicClosedPosition σ p
  sigma_atomic_iterated_rate := by
    intro σ p
    exact sigmaAtomicClosedPosition_eq_iteratedRate σ p
  sigma_atomic_position_faithful := by
    intro σ hσ0 hσ1
    exact sigmaAtomicClosedPosition_injective_of_mem_Ioo hσ0 hσ1
  direct_search_sound := by
    intro n pair h
    exact goldbachDirectSearch_sound h
  direct_search_shape := by
    intro n pair h
    exact goldbachDirectSearch_shape h
  direct_search_iff_goldbach :=
    goldbachDirectSearch_isSome_iff_goldbach
  direct_search_iff_coefficient_pos :=
    goldbachDirectSearch_isSome_iff_coefficient_pos

end AffineRelaxation
end SaturationMonoid

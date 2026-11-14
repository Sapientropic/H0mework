import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyMomentWindow

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow

open Finset Polynomial
open scoped BigOperators Polynomial

variable {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem read_power (a : G →L[ℂ] G) (r : E →L[ℂ] E)
    (read : G →L[ℂ] E) (source : ∀ x, read (a x) = r (read x)) (n : Nat) (x : G) :
    read ((a^n) x) = (r^n) (read x) := by
  have source' : Function.Semiconj read a r := source
  simpa only [FunLike.coe_pow_eq_iterate] using (source'.iterate_right n x)

theorem read_polynomial (a : G →L[ℂ] G) (r : E →L[ℂ] E)
    (read : G →L[ℂ] E) (source : ∀ x, read (a x) = r (read x))
    (p : ℂ[X]) (x : G) : read (aeval a p x) = aeval r p (read x) := by
  rw [aeval_eq_sum_range a, aeval_eq_sum_range r]
  simp only [_root_.sum_apply, map_sum, smul_apply, map_smul, read_power a r read source]

private theorem first_moment_power (a : G →L[ℂ] G) (r : E →L[ℂ] E)
    (read log : G →L[ℂ] E) (κ : ℂ) (source : ∀ x, read (a x) = r (read x))
    (moment : ∀ x, log (a x) = r (log x) + κ • ((r^2) (read x)))
    (n : Nat) (x : G) :
    log ((a^n) x) = (r^n) (log x) + ((n : ℂ)*κ) • ((r^(n+1)) (read x)) := by
  induction n with
  | zero => simp
  | succ n previous =>
    rw [pow_succ', mul_apply_eq_comp, moment, previous, read_power a r read source]
    simp only [map_add, map_smul]
    have left : r ((r^n) (log x)) = (r^(n+1)) (log x) := by
      rw [pow_succ', mul_apply_eq_comp]
    have cross : r ((r^(n+1)) (read x)) = (r^(n+1+1)) (read x) := by
      rw [pow_succ' r (n+1), mul_apply_eq_comp]
    have right : (r^2) ((r^n) (read x)) = (r^(n+1+1)) (read x) := by
      rw [← mul_apply_eq_comp, ← pow_add, show 2+n = n+1+1 by omega]
    have scalar : ((n+1 : Nat) : ℂ)*κ = (n:ℂ)*κ+κ := by push_cast; ring
    rw [left, cross, right, scalar, add_smul]
    abel

/-- The exact first moment of the native action writes the derivative of its finite word. -/
theorem read_polynomial_first_moment (a : G →L[ℂ] G) (r : E →L[ℂ] E)
    (read log : G →L[ℂ] E) (κ : ℂ) (source : ∀ x, read (a x) = r (read x))
    (moment : ∀ x, log (a x) = r (log x) + κ • ((r^2) (read x)))
    (p : ℂ[X]) (x : G) :
    log (aeval a p x) =
      aeval r p (log x) + κ • (aeval r p.derivative ((r^2) (read x))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_apply, hp, hq, smul_add]
    abel
  | monomial n z =>
    cases n with
    | zero =>
      simp [Algebra.algebraMap_eq_smul_one]
    | succ n =>
      have index : (r^n) ((r^2) (read x)) = (r^(n+1+1)) (read x) := by
        rw [← mul_apply_eq_comp, ← pow_add]
      simp only [derivative_monomial_succ, aeval_monomial, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, smul_apply, map_smul, first_moment_power a r read log κ source moment,
        index, smul_add, smul_smul, Nat.cast_succ]
      congr 2
      ring

/-- A source polynomial whose first cutoff coefficients vanish is read entirely on its actual tail. -/
theorem smooth_written (a : G →L[ℂ] G) (d : ℝ) (cutoff length : Nat)
    (positive : 0 < length) (x : G) :
    let p := smoothWeights d cutoff length
    aeval a (smoothPolynomial d cutoff length) x =
      ∑ j ∈ range (p.natDegree+1), p.coeff j • ((a^(cutoff+j)) x) := by
  rw [smooth_factor d cutoff length positive, map_mul, aeval_X_pow, aeval_eq_sum_range a]
  simp only [Finset.sum_mul, smul_mul_assoc, ← pow_add, Nat.add_comm, _root_.sum_apply, smul_apply]

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

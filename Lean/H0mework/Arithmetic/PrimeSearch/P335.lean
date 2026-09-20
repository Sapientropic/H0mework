import H0mework.Realization.RelaxationFlow.P293
import H0mework.Realization.Residual.P334

/-!
# Proposition 335: unified exponent frontend

P292/P293 prove that a finite number of sampled saturation steps is exactly the
continuous relaxation envelope at the total sampled time.  P328/P332/P334 prove
that the same natural exponent also drives the finite Goldbach search,
prime-indicator coefficient, rate/satOr face, and headroom-multiplication face.

This file collects the exponent-level frontend:

* continuous sampling reads `n` as total time `n * step`;
* saturation reads `n` as `iteratedRate sigma n`;
* arithmetic search reads `n` as a finite two-prime witness problem;
* the coefficient frontend reads `n` as positivity of the prime-indicator
  convolution.

Boundary: this is a frontend-identification theorem.  It does not derive a
physical clock, prove global Goldbach, or infer any RH/Standard-Model claim.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Continuous sampling in `iteratedRate` coordinates -/

/-- THEOREM 1: the discrete `iteratedRate` of a one-step rate sampled from the
continuous envelope is exactly the continuous-envelope rate at total sampled
time. -/
theorem iteratedRate_realDecayRate_eq_realDecayRate_nat_mul
    (lambda step : ℝ) (n : ℕ) :
    iteratedRate (realDecayRate lambda step) n =
      realDecayRate lambda ((n : ℝ) * step) := by
  exact effective_rate_of_realDecayRate_pow_eq_realDecayRate_nat_mul
    lambda step n

/-- THEOREM 2: the headroom/residual of that sampled `iteratedRate` is exactly
the continuous residual at total sampled time. -/
theorem keep_iteratedRate_realDecayRate_eq_realDecayResidual_nat_mul
    (lambda step : ℝ) (n : ℕ) :
    1 - iteratedRate (realDecayRate lambda step) n =
      realDecayResidual lambda ((n : ℝ) * step) := by
  calc
    1 - iteratedRate (realDecayRate lambda step) n =
        ((1 : ℝ) - realDecayRate lambda step) ^ n := by
      exact keep_iteratedRate (realDecayRate lambda step) n
    _ = realDecayResidual lambda ((n : ℝ) * step) := by
      exact residual_power_of_realDecayRate_eq_realDecayResidual lambda step n

/-! ## Unified exponent frontend certificate -/

/-- A compact certificate that all certified frontends are reading the same
natural exponent.

The fields intentionally remain frontend equivalences.  They do not assert
that the Goldbach predicate or coefficient positivity holds for every even
input. -/
structure UnifiedExponentFrontendCertificate : Prop where
  sampled_rate :
    ∀ lambda step : ℝ, ∀ n : ℕ,
      iteratedRate (realDecayRate lambda step) n =
        realDecayRate lambda ((n : ℝ) * step)
  sampled_headroom :
    ∀ lambda step : ℝ, ∀ n : ℕ,
      1 - iteratedRate (realDecayRate lambda step) n =
        realDecayResidual lambda ((n : ℝ) * step)
  sampled_fixed_target_flow :
    ∀ {E : Type*} [AddCommGroup E] [Module ℝ E],
      ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : ℕ,
        (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
          realDecayRelaxFlow target lambda ((n : ℝ) * step) x
  sampled_single_total_time :
    ∀ {E : Type*} [AddCommGroup E] [Module ℝ E],
      ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : ℕ,
        (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
          relaxModule target (realDecayRate lambda ((n : ℝ) * step)) x
  finite_search :
    ∀ n : ℕ,
      (goldbachSearchNat n).isSome = true ↔
        HasPrimeAdditiveDecomposition n
  coefficient :
    ∀ n : ℕ,
      0 < goldbachConvolutionCoefficient n ↔
        HasPrimeAdditiveDecomposition n
  arbitrary_sigma_rate_frontend :
    ∀ {σ : ℝ}, 0 < σ -> σ < 1 -> ∀ n : ℕ,
      SigmaGoldbachDecomposition σ n ↔
        0 < goldbachConvolutionCoefficient n
  arbitrary_sigma_headroom_frontend :
    ∀ {σ : ℝ}, 0 < σ -> σ < 1 -> ∀ n : ℕ,
      HeadroomPrimeTwoFactorization σ n ↔
        0 < goldbachConvolutionCoefficient n

/-- THEOREM 3: the canonical unified exponent frontend certificate. -/
theorem unifiedExponentFrontendCertificate :
    UnifiedExponentFrontendCertificate where
  sampled_rate := iteratedRate_realDecayRate_eq_realDecayRate_nat_mul
  sampled_headroom := keep_iteratedRate_realDecayRate_eq_realDecayResidual_nat_mul
  sampled_fixed_target_flow := by
    intro E _ _ target lambda step x n
    exact relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow
      target lambda step x n
  sampled_single_total_time := by
    intro E _ _ target lambda step x n
    exact relaxModule_iterate_realDecayRate_eq_single_total_time
      target lambda step x n
  finite_search := goldbachSearchNat_isSome_iff
  coefficient := by
    intro n
    exact goldbachConvolutionCoefficient_pos_iff n
  arbitrary_sigma_rate_frontend := by
    intro σ hσ0 hσ1 n
    exact sigmaGoldbachDecomposition_iff_convolutionCoefficient_pos_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)
  arbitrary_sigma_headroom_frontend := by
    intro σ hσ0 hσ1 n
    exact headroomPrimeTwoFactorization_iff_convolutionCoefficient_pos_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)

end AffineRelaxation
end SaturationMonoid

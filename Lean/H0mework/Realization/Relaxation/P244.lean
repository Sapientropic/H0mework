import H0mework.Realization.Residual.P243

/-!
# Proposition 244: finite-iterate metric scaling

P243 proves the algebraic finite-iterate law for fixed target/rate relaxation:

`target - T^[n](x) = (1 - sigma)^n • (target - x)`.

This file pushes that law through the real and complex normed-vector carriers:
the distance between two iterated states scales by the norm of the residual
factor after `n` steps.

Boundary: this is still a finite discrete theorem.  It does not assert a
continuous-time ODE, a Hamiltonian generator, a physical time parameter, or an
empirical rate fit.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Real normed-vector finite-iterate metric laws -/

/-- In a real normed vector space, `n` fixed-rate same-target relaxation steps
scale pairwise distances by `|(1 - sigma)^n|`. -/
theorem dist_relaxModule_iterate_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) (x y : E) (n : Nat) :
    dist ((fun z : E => relaxModule target sigma z)^[n] x)
        ((fun z : E => relaxModule target sigma z)^[n] y) =
      |(1 - sigma) ^ n| * dist x y := by
  rw [relaxModule_iterate_eq_single_pow_rate]
  rw [relaxModule_iterate_eq_single_pow_rate]
  rw [dist_relaxModule_real]
  have h :
      (1 : ℝ) - (1 - (1 - sigma) ^ n) = (1 - sigma) ^ n := by
    ring
  rw [h]

/-- The same real finite-iterate distance factor, written as `|1-sigma|^n`. -/
theorem dist_relaxModule_iterate_real_abs_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) (x y : E) (n : Nat) :
    dist ((fun z : E => relaxModule target sigma z)^[n] x)
        ((fun z : E => relaxModule target sigma z)^[n] y) =
      |1 - sigma| ^ n * dist x y := by
  rw [dist_relaxModule_iterate_real]
  rw [abs_pow]

/-- Distance to the target after `n` real same-target relaxation steps. -/
theorem dist_relaxModule_iterate_target_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) (x : E) (n : Nat) :
    dist ((fun z : E => relaxModule target sigma z)^[n] x) target =
      |(1 - sigma) ^ n| * dist x target := by
  rw [relaxModule_iterate_eq_single_pow_rate]
  rw [dist_relaxModule_target_real]
  have h :
      (1 : ℝ) - (1 - (1 - sigma) ^ n) = (1 - sigma) ^ n := by
    ring
  rw [h]

/-- A bundled certificate for the real finite-iterate metric scaling slice. -/
structure RealFiniteIterateMetricCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  pairwise :
    ∀ target : E, ∀ sigma : ℝ, ∀ x y : E, ∀ n : Nat,
      dist ((fun z : E => relaxModule target sigma z)^[n] x)
          ((fun z : E => relaxModule target sigma z)^[n] y) =
        |(1 - sigma) ^ n| * dist x y
  target_distance :
    ∀ target : E, ∀ sigma : ℝ, ∀ x : E, ∀ n : Nat,
      dist ((fun z : E => relaxModule target sigma z)^[n] x) target =
        |(1 - sigma) ^ n| * dist x target

/-- The real normed-vector carrier supplies the finite-iterate metric
certificate. -/
theorem realFiniteIterateMetricCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    RealFiniteIterateMetricCertificate E where
  pairwise := dist_relaxModule_iterate_real
  target_distance := dist_relaxModule_iterate_target_real

/-! ## Complex normed-vector finite-iterate metric laws -/

/-- In a complex normed vector space, `n` fixed-rate same-target relaxation
steps scale pairwise distances by `‖(1 - sigma)^n‖`. -/
theorem dist_relaxModule_iterate_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) (x y : E) (n : Nat) :
    dist ((fun z : E => relaxModule target sigma z)^[n] x)
        ((fun z : E => relaxModule target sigma z)^[n] y) =
      ‖((1 : ℂ) - sigma) ^ n‖ * dist x y := by
  rw [relaxModule_iterate_eq_single_pow_rate]
  rw [relaxModule_iterate_eq_single_pow_rate]
  rw [dist_relaxModule_complex]
  have h :
      (1 : ℂ) - (1 - ((1 : ℂ) - sigma) ^ n) =
        ((1 : ℂ) - sigma) ^ n := by
    ring
  rw [h]

/-- The same complex finite-iterate distance factor, written as
`‖1-sigma‖^n`. -/
theorem dist_relaxModule_iterate_complex_norm_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) (x y : E) (n : Nat) :
    dist ((fun z : E => relaxModule target sigma z)^[n] x)
        ((fun z : E => relaxModule target sigma z)^[n] y) =
      ‖(1 : ℂ) - sigma‖ ^ n * dist x y := by
  rw [dist_relaxModule_iterate_complex]
  rw [norm_pow]

/-- Distance to the target after `n` complex same-target relaxation steps. -/
theorem dist_relaxModule_iterate_target_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) (x : E) (n : Nat) :
    dist ((fun z : E => relaxModule target sigma z)^[n] x) target =
      ‖((1 : ℂ) - sigma) ^ n‖ * dist x target := by
  rw [relaxModule_iterate_eq_single_pow_rate]
  rw [dist_relaxModule_target_complex]
  have h :
      (1 : ℂ) - (1 - ((1 : ℂ) - sigma) ^ n) =
        ((1 : ℂ) - sigma) ^ n := by
    ring
  rw [h]

/-- A bundled certificate for the complex finite-iterate metric scaling slice.
-/
structure ComplexFiniteIterateMetricCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop where
  pairwise :
    ∀ target : E, ∀ sigma : ℂ, ∀ x y : E, ∀ n : Nat,
      dist ((fun z : E => relaxModule target sigma z)^[n] x)
          ((fun z : E => relaxModule target sigma z)^[n] y) =
        ‖((1 : ℂ) - sigma) ^ n‖ * dist x y
  target_distance :
    ∀ target : E, ∀ sigma : ℂ, ∀ x : E, ∀ n : Nat,
      dist ((fun z : E => relaxModule target sigma z)^[n] x) target =
        ‖((1 : ℂ) - sigma) ^ n‖ * dist x target

/-- The complex normed-vector carrier supplies the finite-iterate metric
certificate. -/
theorem complexFiniteIterateMetricCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ComplexFiniteIterateMetricCertificate E where
  pairwise := dist_relaxModule_iterate_complex
  target_distance := dist_relaxModule_iterate_target_complex


end AffineRelaxation
end SaturationMonoid

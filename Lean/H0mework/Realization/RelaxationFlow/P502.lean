import H0mework.Realization.RelaxationFlow.P293
import H0mework.Realization.RelaxationFlow.P501

/-!
# Proposition 502: fixed-total-time subdivision is exact

P292/P293 prove that a fixed sampled step has total time `n * step`.
This file records the complementary subdivision form used by the unified
formula track:

```lean
step = T / n
```

for `0 < n`.  Then `n` sampled steps are not an approximation and not a new
energy source; they are exactly the same affine relaxation as the continuous
flow at total time `T`.

This is the formal version of the safe part of the slogan
`sigma -> 0, n -> infinity, sigma*n = const`: refining the step size preserves
the fixed total flow.  Complete relaxation requires sending the total time
itself to infinity, not merely subdividing a finite total time.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Residual and effective-rate subdivision laws -/

/-- THEOREM 0: multiplying the subdivision step `T/n` by `n` recovers the
fixed total time `T`, provided `0 < n`. -/
theorem nat_mul_total_div
    (T : ℝ) {n : Nat} (hn : 0 < n) :
    (n : ℝ) * (T / (n : ℝ)) = T := by
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn_ne]

/-- THEOREM 1: multiplying the subdivision step `T/n` by `n` gives the same
continuous residual at total time `T`. -/
theorem realDecayResidual_nat_mul_total_div
    (lambda T : ℝ) {n : Nat} (hn : 0 < n) :
    realDecayResidual lambda ((n : ℝ) * (T / (n : ℝ))) =
      realDecayResidual lambda T := by
  unfold realDecayResidual
  rw [nat_mul_total_div T hn]

/-- THEOREM 2: the residual power of `n` equal subdivisions of total time `T`
is exactly the continuous residual at `T`. -/
theorem residual_power_of_subdivided_realDecayRate_eq_total
    (lambda T : ℝ) {n : Nat} (hn : 0 < n) :
    ((1 : ℝ) - realDecayRate lambda (T / (n : ℝ))) ^ n =
      realDecayResidual lambda T := by
  rw [residual_power_of_realDecayRate_eq_realDecayResidual]
  exact realDecayResidual_nat_mul_total_div lambda T hn

/-- THEOREM 3: the effective noisy-OR rate of `n` equal subdivisions is exactly
the continuous-envelope rate at total time `T`. -/
theorem effective_rate_of_subdivided_realDecayRate_eq_total
    (lambda T : ℝ) {n : Nat} (hn : 0 < n) :
    1 - ((1 : ℝ) - realDecayRate lambda (T / (n : ℝ))) ^ n =
      realDecayRate lambda T := by
  rw [residual_power_of_subdivided_realDecayRate_eq_total lambda T hn]
  unfold realDecayRate
  rfl

/-! ## Fixed-target affine subdivision laws -/

/-- THEOREM 4: `n` equal subdivisions of a fixed total time are exactly the
continuous fixed-target flow at total time `T`. -/
theorem relaxModule_iterate_subdivided_realDecayRate_eq_total_flow
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda T : ℝ) {n : Nat} (hn : 0 < n) (x : E) :
    (fun y : E =>
      relaxModule target (realDecayRate lambda (T / (n : ℝ))) y)^[n] x =
      realDecayRelaxFlow target lambda T x := by
  rw [relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow]
  congr 1
  exact nat_mul_total_div T hn

/-- THEOREM 5: the single effective fixed-target step of `n` equal
subdivisions is the continuous fixed-target flow at total time `T`. -/
theorem relaxModule_effective_subdivided_realDecayRate_eq_total_flow
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda T : ℝ) {n : Nat} (hn : 0 < n) (x : E) :
    relaxModule
        target
        (1 - ((1 : ℝ) - realDecayRate lambda (T / (n : ℝ))) ^ n)
        x =
      realDecayRelaxFlow target lambda T x := by
  rw [effective_rate_of_subdivided_realDecayRate_eq_total lambda T hn]
  rfl

/-! ## Metric consequences -/

/-- THEOREM 6: equal subdivisions of a fixed total time contract distances by
the same continuous residual at `T`. -/
theorem dist_relaxModule_iterate_subdivided_realDecayRate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda T : ℝ) {n : Nat} (hn : 0 < n) (x y : E) :
    dist
        ((fun z : E =>
          relaxModule target (realDecayRate lambda (T / (n : ℝ))) z)^[n] x)
        ((fun z : E =>
          relaxModule target (realDecayRate lambda (T / (n : ℝ))) z)^[n] y)
      =
      realDecayResidual lambda T * dist x y := by
  rw [dist_relaxModule_iterate_realDecayRate]
  rw [realDecayResidual_nat_mul_total_div lambda T hn]

/-- THEOREM 7: equal subdivisions of a fixed total time scale target distance
by the same continuous residual at `T`. -/
theorem dist_relaxModule_iterate_subdivided_realDecayRate_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda T : ℝ) {n : Nat} (hn : 0 < n) (x : E) :
    dist
        ((fun z : E =>
          relaxModule target (realDecayRate lambda (T / (n : ℝ))) z)^[n] x)
        target
      =
      realDecayResidual lambda T * dist x target := by
  rw [dist_relaxModule_iterate_realDecayRate_target]
  rw [realDecayResidual_nat_mul_total_div lambda T hn]

/-! ## Bundled receipt -/

/-- A compact receipt for fixed-total-time subdivision invariance. -/
structure FixedTotalTimeSubdivisionBridgeCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  residual :
    ∀ lambda T : ℝ, ∀ n : Nat, 0 < n ->
      ((1 : ℝ) - realDecayRate lambda (T / (n : ℝ))) ^ n =
        realDecayResidual lambda T
  effective_rate :
    ∀ lambda T : ℝ, ∀ n : Nat, 0 < n ->
      1 - ((1 : ℝ) - realDecayRate lambda (T / (n : ℝ))) ^ n =
        realDecayRate lambda T
  iterate_flow :
    ∀ target : E, ∀ lambda T : ℝ, ∀ n : Nat, 0 < n -> ∀ x : E,
      (fun y : E =>
        relaxModule target (realDecayRate lambda (T / (n : ℝ))) y)^[n] x =
        realDecayRelaxFlow target lambda T x
  effective_flow :
    ∀ target : E, ∀ lambda T : ℝ, ∀ n : Nat, 0 < n -> ∀ x : E,
      relaxModule
          target
          (1 - ((1 : ℝ) - realDecayRate lambda (T / (n : ℝ))) ^ n)
          x =
        realDecayRelaxFlow target lambda T x
  distance :
    ∀ target : E, ∀ lambda T : ℝ, ∀ n : Nat, 0 < n -> ∀ x y : E,
      dist
          ((fun z : E =>
            relaxModule target (realDecayRate lambda (T / (n : ℝ))) z)^[n] x)
          ((fun z : E =>
            relaxModule target (realDecayRate lambda (T / (n : ℝ))) z)^[n] y)
        =
        realDecayResidual lambda T * dist x y
  target_distance :
    ∀ target : E, ∀ lambda T : ℝ, ∀ n : Nat, 0 < n -> ∀ x : E,
      dist
          ((fun z : E =>
            relaxModule target (realDecayRate lambda (T / (n : ℝ))) z)^[n] x)
          target
        =
        realDecayResidual lambda T * dist x target

/-- THEOREM 8: every real normed-vector carrier supplies the subdivision
bridge. -/
theorem fixedTotalTimeSubdivisionBridgeCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    FixedTotalTimeSubdivisionBridgeCertificate E where
  residual := fun lambda T _n hn =>
    residual_power_of_subdivided_realDecayRate_eq_total lambda T hn
  effective_rate := fun lambda T _n hn =>
    effective_rate_of_subdivided_realDecayRate_eq_total lambda T hn
  iterate_flow := fun target lambda T _n hn x =>
    relaxModule_iterate_subdivided_realDecayRate_eq_total_flow
      target lambda T hn x
  effective_flow := fun target lambda T _n hn x =>
    relaxModule_effective_subdivided_realDecayRate_eq_total_flow
      target lambda T hn x
  distance := fun target lambda T _n hn x y =>
    dist_relaxModule_iterate_subdivided_realDecayRate
      target lambda T hn x y
  target_distance := fun target lambda T _n hn x =>
    dist_relaxModule_iterate_subdivided_realDecayRate_target
      target lambda T hn x

end

end AffineRelaxation
end SaturationMonoid

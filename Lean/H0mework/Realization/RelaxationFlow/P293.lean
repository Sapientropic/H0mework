import H0mework.Realization.RelaxationFlow.P292

/-!
# Proposition 293: sampled finite relaxation is the fixed-target flow

P292 proves the scalar residual identity

`(1 - (1 - exp(-lambda * step)))^n = exp(-lambda * (n * step))`.

This file lifts that identity from the zero-target scalar slice to the full
fixed-target affine relaxation law over arbitrary real modules, and to real
normed-vector carriers for the metric laws.

Boundary: this is still a fixed-target affine-relaxation theorem.  It does not
choose the physical clock, derive `lambda`, solve an RG equation, or identify a
Hamiltonian generator.  It proves that once the one-step rate is sampled from
the continuous envelope, finite iteration and continuous flow are literally the
same affine map at sampled time.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Fixed-target discrete/continuous bridge -/

/-- THEOREM 1: the residual to a fixed target after `n` sampled-rate steps is
exactly the continuous residual at total sampled time. -/
theorem target_sub_relaxModule_iterate_realDecayRate_eq_continuous_residual
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda step : ℝ) (x : E) (n : Nat) :
    target -
        (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
      realDecayResidual lambda ((n : ℝ) * step) • (target - x) := by
  rw [target_sub_relaxModule_iterate]
  rw [residual_power_of_realDecayRate_eq_realDecayResidual]

/-- THEOREM 2: `n` fixed-target sampled-rate steps are exactly the
continuous-time fixed-target flow at total sampled time. -/
theorem relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda step : ℝ) (x : E) (n : Nat) :
    (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
      realDecayRelaxFlow target lambda ((n : ℝ) * step) x := by
  rw [relaxModule_iterate_eq_closed]
  rw [realDecayRelaxFlow_eq_closed]
  rw [residual_power_of_realDecayRate_eq_realDecayResidual]

/-- THEOREM 3: the single effective fixed-target step for `n` sampled steps is
the continuous-time fixed-target flow at total sampled time. -/
theorem relaxModule_effective_realDecayRate_eq_realDecayRelaxFlow
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda step : ℝ) (x : E) (n : Nat) :
    relaxModule
        target
        (1 - ((1 : ℝ) - realDecayRate lambda step) ^ n)
        x =
      realDecayRelaxFlow target lambda ((n : ℝ) * step) x := by
  rw [effective_rate_of_realDecayRate_pow_eq_realDecayRate_nat_mul]
  rfl

/-- THEOREM 4: finite sampled-rate iteration collapses to one fixed-target
continuous-envelope step at total sampled time. -/
theorem relaxModule_iterate_realDecayRate_eq_single_total_time
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda step : ℝ) (x : E) (n : Nat) :
    (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
      relaxModule target (realDecayRate lambda ((n : ℝ) * step)) x := by
  rw [relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow]
  rfl

/-! ## Metric consequences on real normed-vector carriers -/

/-- THEOREM 5: two sampled-rate finite trajectories contract by the continuous
residual at total sampled time. -/
theorem dist_relaxModule_iterate_realDecayRate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda step : ℝ) (x y : E) (n : Nat) :
    dist
        ((fun z : E => relaxModule target (realDecayRate lambda step) z)^[n] x)
        ((fun z : E => relaxModule target (realDecayRate lambda step) z)^[n] y)
      =
      realDecayResidual lambda ((n : ℝ) * step) * dist x y := by
  rw [relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow]
  rw [relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow]
  rw [dist_realDecayRelaxFlow]

/-- THEOREM 6: distance to the target after sampled-rate finite iteration is
the continuous-envelope distance at total sampled time. -/
theorem dist_relaxModule_iterate_realDecayRate_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda step : ℝ) (x : E) (n : Nat) :
    dist
        ((fun z : E => relaxModule target (realDecayRate lambda step) z)^[n] x)
        target
      =
      realDecayResidual lambda ((n : ℝ) * step) * dist x target := by
  rw [relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow]
  rw [dist_realDecayRelaxFlow_target]

/-! ## Certificate -/

/-- A bundled certificate that the discrete finite same-target law and the
continuous fixed-target relaxation flow are the same sampled affine law. -/
structure DiscreteContinuousFixedTargetBridgeCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  target_residual :
    ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : Nat,
      target -
          (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
        realDecayResidual lambda ((n : ℝ) * step) • (target - x)
  iterate_flow :
    ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : Nat,
      (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
        realDecayRelaxFlow target lambda ((n : ℝ) * step) x
  effective_flow :
    ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : Nat,
      relaxModule
          target
          (1 - ((1 : ℝ) - realDecayRate lambda step) ^ n)
          x =
        realDecayRelaxFlow target lambda ((n : ℝ) * step) x
  single_total_time :
    ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : Nat,
      (fun y : E => relaxModule target (realDecayRate lambda step) y)^[n] x =
        relaxModule target (realDecayRate lambda ((n : ℝ) * step)) x
  distance :
    ∀ target : E, ∀ lambda step : ℝ, ∀ x y : E, ∀ n : Nat,
      dist
          ((fun z : E =>
            relaxModule target (realDecayRate lambda step) z)^[n] x)
          ((fun z : E =>
            relaxModule target (realDecayRate lambda step) z)^[n] y)
        =
        realDecayResidual lambda ((n : ℝ) * step) * dist x y
  target_distance :
    ∀ target : E, ∀ lambda step : ℝ, ∀ x : E, ∀ n : Nat,
      dist
          ((fun z : E =>
            relaxModule target (realDecayRate lambda step) z)^[n] x)
          target
        =
        realDecayResidual lambda ((n : ℝ) * step) * dist x target

/-- THEOREM 7: every real normed-vector carrier supplies the fixed-target
discrete/continuous sampled-flow bridge. -/
theorem discreteContinuousFixedTargetBridgeCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DiscreteContinuousFixedTargetBridgeCertificate E where
  target_residual :=
    target_sub_relaxModule_iterate_realDecayRate_eq_continuous_residual
  iterate_flow := relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow
  effective_flow := relaxModule_effective_realDecayRate_eq_realDecayRelaxFlow
  single_total_time := relaxModule_iterate_realDecayRate_eq_single_total_time
  distance := dist_relaxModule_iterate_realDecayRate
  target_distance := dist_relaxModule_iterate_realDecayRate_target

end

end AffineRelaxation
end SaturationMonoid

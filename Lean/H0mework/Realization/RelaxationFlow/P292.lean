import H0mework.Realization.RelaxationFlow.P245
import H0mework.Physics.YukawaSources.P275

/-!
# Proposition 292: finite depth as sampled continuous relaxation

P243/P275 give the Standard-Model-facing finite-depth residual shape

`A * (1 - sigma)^n`.

P245 gives the fixed-target continuous envelope

`sigma(t) = 1 - exp(-lambda * t)`.

This file proves the bridge between them.  If the one-step rate is sampled from
the continuous envelope at step size `dt`,

`sigma_step = 1 - exp(-lambda * dt)`,

then the `n`-step residual power is exactly the continuous residual at total
time `n * dt`:

`(1 - sigma_step)^n = exp(-lambda * (n * dt))`.

Boundary: this proves the algebraic sampling bridge.  It does not choose a
physical step size, derive `lambda`, solve Standard Model RG equations, or
identify the correct scale map for real Yukawa data.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Discrete powers of the continuous residual -/

/-- THEOREM 1: the exponential residual sampled at a fixed step has exact
geometric powers. -/
theorem realDecayResidual_nat_mul
    (lambda step : ℝ) (n : Nat) :
    realDecayResidual lambda ((n : ℝ) * step) =
      (realDecayResidual lambda step) ^ n := by
  induction n with
  | zero =>
      simp [realDecayResidual]
  | succ n ih =>
      calc
        realDecayResidual lambda (((n + 1 : Nat) : ℝ) * step)
            = realDecayResidual lambda (((n : ℝ) * step) + step) := by
                congr 1
                norm_num
                ring
        _ = realDecayResidual lambda ((n : ℝ) * step) *
              realDecayResidual lambda step := by
                rw [realDecayResidual_add]
        _ = (realDecayResidual lambda step) ^ n *
              realDecayResidual lambda step := by
                rw [ih]
        _ = (realDecayResidual lambda step) ^ (n + 1) := by
                rw [pow_succ]

/-- THEOREM 2: the residual power of a sampled one-step rate equals the
continuous residual at the total sampled time. -/
theorem residual_power_of_realDecayRate_eq_realDecayResidual
    (lambda step : ℝ) (n : Nat) :
    ((1 : ℝ) - realDecayRate lambda step) ^ n =
      realDecayResidual lambda ((n : ℝ) * step) := by
  have hbase :
      (1 : ℝ) - realDecayRate lambda step =
        realDecayResidual lambda step := by
    unfold realDecayRate
    ring
  rw [hbase, realDecayResidual_nat_mul]

/-- THEOREM 3: the noisy-OR effective rate of `n` sampled steps is the
continuous-envelope rate at total time `n * step`. -/
theorem effective_rate_of_realDecayRate_pow_eq_realDecayRate_nat_mul
    (lambda step : ℝ) (n : Nat) :
    1 - ((1 : ℝ) - realDecayRate lambda step) ^ n =
      realDecayRate lambda ((n : ℝ) * step) := by
  rw [residual_power_of_realDecayRate_eq_realDecayResidual]
  unfold realDecayRate
  rfl

/-- THEOREM 4: `n` zero-target steps at the sampled one-step rate equal the
closed continuous residual at total sampled time. -/
theorem zeroTarget_relaxModule_iterate_realDecayRate_eq_continuous_residual
    (amplitude lambda step : ℝ) (n : Nat) :
    (fun x : ℝ =>
      relaxModule (0 : ℝ) (realDecayRate lambda step) x)^[n] amplitude =
      amplitude * realDecayResidual lambda ((n : ℝ) * step) := by
  rw [StandardModelConstraint.zeroTarget_relaxModule_iterate_eq_residual_power]
  rw [residual_power_of_realDecayRate_eq_realDecayResidual]

/-- THEOREM 5: the single effective zero-target step for `n` sampled steps is
the same as the continuous-envelope zero-target step at total sampled time. -/
theorem zeroTarget_effective_relaxModule_realDecayRate_eq_total_time
    (amplitude lambda step : ℝ) (n : Nat) :
    relaxModule
        (0 : ℝ)
        (1 - ((1 : ℝ) - realDecayRate lambda step) ^ n)
        amplitude =
      relaxModule
        (0 : ℝ)
        (realDecayRate lambda ((n : ℝ) * step))
        amplitude := by
  rw [effective_rate_of_realDecayRate_pow_eq_realDecayRate_nat_mul]

/-- A bundled bridge: sampled finite-depth relaxation and continuous-time
relaxation are the same residual law. -/
structure DiscreteContinuousRelaxationBridgeCertificate : Prop where
  residual_power :
    ∀ lambda step : ℝ, ∀ n : Nat,
      ((1 : ℝ) - realDecayRate lambda step) ^ n =
        realDecayResidual lambda ((n : ℝ) * step)
  effective_rate :
    ∀ lambda step : ℝ, ∀ n : Nat,
      1 - ((1 : ℝ) - realDecayRate lambda step) ^ n =
        realDecayRate lambda ((n : ℝ) * step)
  zero_target_iterate :
    ∀ amplitude lambda step : ℝ, ∀ n : Nat,
      (fun x : ℝ =>
        relaxModule (0 : ℝ) (realDecayRate lambda step) x)^[n] amplitude =
        amplitude * realDecayResidual lambda ((n : ℝ) * step)
  zero_target_effective :
    ∀ amplitude lambda step : ℝ, ∀ n : Nat,
      relaxModule
          (0 : ℝ)
          (1 - ((1 : ℝ) - realDecayRate lambda step) ^ n)
          amplitude =
        relaxModule
          (0 : ℝ)
          (realDecayRate lambda ((n : ℝ) * step))
          amplitude

/-- THEOREM 6: the sampled finite-depth/continuous-envelope bridge is
available for real scalar zero-target relaxation. -/
theorem discreteContinuousRelaxationBridgeCertificate :
    DiscreteContinuousRelaxationBridgeCertificate where
  residual_power := residual_power_of_realDecayRate_eq_realDecayResidual
  effective_rate := effective_rate_of_realDecayRate_pow_eq_realDecayRate_nat_mul
  zero_target_iterate :=
    zeroTarget_relaxModule_iterate_realDecayRate_eq_continuous_residual
  zero_target_effective :=
    zeroTarget_effective_relaxModule_realDecayRate_eq_total_time

end

end AffineRelaxation
end SaturationMonoid

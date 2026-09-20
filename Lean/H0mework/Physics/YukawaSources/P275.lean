/-
  Proposition 275: Yukawa residual powers are unified relaxation iterates.

  P273/P274 pin the Standard-Model-facing Yukawa form

      Y_y = A_y * (1 - sigma(scale_y))^n_y.

  P243 proves the unified equation's finite-iterate law.  This file connects
  the two: the Yukawa residual-power shape is exactly the zero-target instance
  of repeated unified relaxation

      X -> X + sigma * (0 - X),

  starting from amplitude `A_y`.  Equivalently, the same value is one
  zero-target relaxation at the effective noisy-OR rate

      1 - (1 - sigma)^n.

  Boundary: this still does not derive amplitudes, scales, exponents, or the
  running-sigma certificate.  It proves that, once P274 supplies them, the
  Yukawa formula is not a separate ansatz but an instance of the already
  certified unified relaxation spine.
-/

import H0mework.Realization.Residual.P243
import H0mework.Physics.CouplingSources.P274

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Scalar zero-target relaxation form -/

/-- THEOREM 1: scalar zero-target finite relaxation from amplitude `A` is
exactly `A * (1 - sigma)^n`. -/
theorem zeroTarget_relaxModule_iterate_eq_residual_power
    {K : Type*} [Field K] (amplitude sigma : K) (n : Nat) :
    (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
        amplitude =
      amplitude * ((1 - sigma) ^ n) := by
  rw [AffineRelaxation.relaxModule_iterate_eq_closed]
  ring

/-- THEOREM 2: the same scalar zero-target finite relaxation is one
relaxation at the effective noisy-OR rate `1 - (1 - sigma)^n`. -/
theorem zeroTarget_relaxModule_effective_rate_eq_residual_power
    {K : Type*} [Field K] (amplitude sigma : K) (n : Nat) :
    AffineRelaxation.relaxModule
        (0 : K) (1 - (1 - sigma) ^ n) amplitude =
      amplitude * ((1 - sigma) ^ n) := by
  rw [← AffineRelaxation.relaxModule_iterate_eq_single_pow_rate
    (target := (0 : K)) (sigma := sigma) (x := amplitude) (n := n)]
  exact zeroTarget_relaxModule_iterate_eq_residual_power amplitude sigma n

/-! ## Standard Model Yukawa bridge -/

namespace RunningSigmaStandardModelCertificate

variable {Seed Scale Index A K CKMCarrier : Type*}
variable [AddCommGroup A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 3: generated Yukawa slots are zero-target unified-relaxation
finite iterates from their amplitudes, with the running sigma read at the
slot's declared scale. -/
theorem generated_yukawa_eq_zeroTarget_relaxation_iterate
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) (y : YukawaParameter) :
    C.pinned.base.generated seed (yukawaSlot y) =
      (fun x : K =>
        AffineRelaxation.relaxModule
          (0 : K) (C.sigma (C.yukawaScale seed y)) x)^[
            C.pinned.yukawaExponent seed y]
          (C.pinned.yukawaAmplitude y) := by
  rw [zeroTarget_relaxModule_iterate_eq_residual_power]
  exact C.generated_yukawa_residual_power_running_sigma seed y

/-- THEOREM 4: equivalently, generated Yukawa slots are one zero-target
unified relaxation at the effective rate `1 - (1 - sigma)^n`. -/
theorem generated_yukawa_eq_zeroTarget_effective_relaxation
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) (y : YukawaParameter) :
    C.pinned.base.generated seed (yukawaSlot y) =
      AffineRelaxation.relaxModule
        (0 : K)
        (1 - (1 - C.sigma (C.yukawaScale seed y)) ^
          C.pinned.yukawaExponent seed y)
        (C.pinned.yukawaAmplitude y) := by
  rw [zeroTarget_relaxModule_effective_rate_eq_residual_power]
  exact C.generated_yukawa_residual_power_running_sigma seed y

/-- THEOREM 5: any accepted constraint solution has Yukawa slots that arise
from zero-target unified-relaxation finite iterates for some structural seed. -/
theorem solution_yukawa_eq_zeroTarget_relaxation_iterate_exists_seed
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (p : ParameterVector K) (hp : C.pinned.base.constraints p) :
    ∃ seed,
      C.pinned.base.generated seed = p ∧
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            (fun x : K =>
              AffineRelaxation.relaxModule
                (0 : K) (C.sigma (C.yukawaScale seed y)) x)^[
                  C.pinned.yukawaExponent seed y]
                (C.pinned.yukawaAmplitude y) := by
  rcases C.pinned.base.complete p hp with ⟨seed, hseed⟩
  refine ⟨seed, hseed, ?_⟩
  intro y
  rw [← hseed]
  exact C.generated_yukawa_eq_zeroTarget_relaxation_iterate seed y

/-- THEOREM 6: any accepted constraint solution also has the equivalent
single-step effective-rate zero-target relaxation presentation. -/
theorem solution_yukawa_eq_zeroTarget_effective_relaxation_exists_seed
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (p : ParameterVector K) (hp : C.pinned.base.constraints p) :
    ∃ seed,
      C.pinned.base.generated seed = p ∧
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            AffineRelaxation.relaxModule
              (0 : K)
              (1 - (1 - C.sigma (C.yukawaScale seed y)) ^
                C.pinned.yukawaExponent seed y)
              (C.pinned.yukawaAmplitude y) := by
  rcases C.pinned.base.complete p hp with ⟨seed, hseed⟩
  refine ⟨seed, hseed, ?_⟩
  intro y
  rw [← hseed]
  exact C.generated_yukawa_eq_zeroTarget_effective_relaxation seed y

end RunningSigmaStandardModelCertificate

end StandardModelConstraint
end SaturationMonoid

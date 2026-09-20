/-
  Proposition 467: the single physical relaxation target is zero.

  The previous Standard-Model-facing files use several surface coordinates:

  * Yukawa values are residual powers `A * (1 - sigma)^n`;
  * dimensionless residual quantities use `1 * (1 - sigma)^n`;
  * `theta_QCD` is pinned to zero;
  * salience/rate bumps move toward `1`.

  This file records the coordinate unification.  The primitive relaxation target
  is `0`.  A rate moving toward `1` is just the complementary residual/keep
  coordinate moving toward `0`:

      1 - bumpSatField h sigma = relaxModule 0 sigma (1 - h).

  Boundary: this proves the zero-target algebraic normal form.  It does not
  derive the physical normalization constants (for example a Planck unit choice
  or a Yukawa amplitude lock); those remain carrier/physics certificates in the
  surrounding Standard Model layer.
-/

import H0mework.Physics.SourceContracts.P466
import H0mework.Physics.YukawaSources.P275

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Zero-target scalar spine -/

/-- THEOREM 1: one scalar zero-target relaxation is multiplication by the
residual/keep factor `1 - sigma`. -/
theorem zeroTarget_relaxModule_eq_keep_mul
    {K : Type*} [Field K] (initial sigma : K) :
    AffineRelaxation.relaxModule (0 : K) sigma initial =
      initial * (1 - sigma) := by
  unfold AffineRelaxation.relaxModule
  ring

/-- THEOREM 2: the closed residual-power form is exactly an `n`-fold
zero-target relaxation. -/
theorem residual_power_eq_zeroTarget_relaxModule_iterate
    {K : Type*} [Field K] (initial sigma : K) (n : Nat) :
    initial * ((1 - sigma) ^ n) =
      (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
        initial := by
  exact (zeroTarget_relaxModule_iterate_eq_residual_power initial sigma n).symm

/-- THEOREM 3: a dimensionless residual reference also has the same
zero-target relaxation form. -/
theorem dimensionless_reference_residual_power_eq_zeroTarget_iterate
    {K : Type*} [Field K] (sigma : K) (n : Nat) :
    (1 : K) * ((1 - sigma) ^ n) =
      (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
        (1 : K) := by
  exact residual_power_eq_zeroTarget_relaxModule_iterate (1 : K) sigma n

/-- THEOREM 4: a Planck-scale/VEV-shaped residual expression is not a second
target; algebraically it is just zero-target relaxation from the chosen unit
carrier `M`. -/
theorem carrier_scale_residual_power_eq_zeroTarget_iterate
    {K : Type*} [Field K] (M sigma : K) (n : Nat) :
    M * ((1 - sigma) ^ n) =
      (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
        M := by
  exact residual_power_eq_zeroTarget_relaxModule_iterate M sigma n

/-- THEOREM 5: the cosmological-constant-shaped exponent `1600` is the same
zero-target residual-power normal form from the dimensionless reference. -/
theorem lambda1600_residual_power_eq_zeroTarget_iterate
    {K : Type*} [Field K] (sigma : K) :
    (1 : K) * ((1 - sigma) ^ (1600 : Nat)) =
      (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[
        (1600 : Nat)] (1 : K) := by
  exact dimensionless_reference_residual_power_eq_zeroTarget_iterate
    sigma (1600 : Nat)

/-! ## Rate-as-complement, not a second target -/

/-- THEOREM 6: rate bumps target `1` only in the rate coordinate.  In the
complementary keep/headroom coordinate, the same update is exactly a
zero-target relaxation. -/
theorem complement_bumpSatField_eq_zeroTarget_relaxModule_keep
    {K : Type*} [Field K] (h sigma : K) :
    (1 : K) - bumpSatField h sigma =
      AffineRelaxation.relaxModule (0 : K) sigma ((1 : K) - h) := by
  unfold bumpSatField AffineRelaxation.relaxModule
  ring

/-- THEOREM 7: equivalently, the apparent `Target=1` rate form is recovered by
taking the complement of a zero-target keep relaxation. -/
theorem bumpSatField_eq_one_sub_zeroTarget_keep
    {K : Type*} [Field K] (h sigma : K) :
    bumpSatField h sigma =
      (1 : K) -
        AffineRelaxation.relaxModule (0 : K) sigma ((1 : K) - h) := by
  rw [← complement_bumpSatField_eq_zeroTarget_relaxModule_keep h sigma]
  ring

/-- THEOREM 8: zero itself is already at the unique relaxation target. -/
theorem zeroTarget_relaxModule_zero_initial
    {K : Type*} [Field K] (sigma : K) :
    AffineRelaxation.relaxModule (0 : K) sigma (0 : K) = 0 := by
  exact AffineRelaxation.relaxModule_target_absorbing (target := (0 : K)) sigma

/-! ## Standard-Model-facing zero pins -/

namespace RunningSigmaStandardModelCertificate

variable {Seed Scale Index A K CKMCarrier : Type*}
variable [AddCommGroup A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 9: `theta_QCD = 0` is not another relaxation target.  It is already
the zero-target absorbing state for any rate supplied in the scalar carrier. -/
theorem generated_thetaQCD_eq_zeroTarget_absorbing
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) (sigma : K) :
    C.pinned.base.generated seed StandardModelParameter.qcd_theta =
      AffineRelaxation.relaxModule (0 : K) sigma (0 : K) := by
  rw [C.generated_thetaQCD_zero seed,
    zeroTarget_relaxModule_zero_initial sigma]

/-- THEOREM 10: generated Yukawa slots are included in the same single-target
receipt: they are zero-target residual-power iterates. -/
theorem generated_yukawa_singleTarget_zero
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) (y : YukawaParameter) :
    C.pinned.base.generated seed (yukawaSlot y) =
      (fun x : K =>
        AffineRelaxation.relaxModule
          (0 : K) (C.sigma (C.yukawaScale seed y)) x)^[
            C.pinned.yukawaExponent seed y]
          (C.pinned.yukawaAmplitude y) :=
  C.generated_yukawa_eq_zeroTarget_relaxation_iterate seed y

end RunningSigmaStandardModelCertificate

/-! ## Bundled receipt -/

/-- A small reusable receipt for the "one Target only" claim.  Every field is a
proved theorem, not a new assumption. -/
structure SingleZeroTargetRelaxationReceipt
    (K : Type*) [Field K] : Prop where
  scalar_one_step :
    ∀ initial sigma : K,
      AffineRelaxation.relaxModule (0 : K) sigma initial =
        initial * (1 - sigma)
  residual_iterate :
    ∀ initial sigma : K, ∀ n : Nat,
      initial * ((1 - sigma) ^ n) =
        (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[n]
          initial
  rate_is_complement_zero_target :
    ∀ h sigma : K,
      (1 : K) - bumpSatField h sigma =
        AffineRelaxation.relaxModule (0 : K) sigma ((1 : K) - h)
  zero_absorbing :
    ∀ sigma : K,
      AffineRelaxation.relaxModule (0 : K) sigma (0 : K) = 0
  lambda1600_shape :
    ∀ sigma : K,
      (1 : K) * ((1 - sigma) ^ (1600 : Nat)) =
        (fun x : K => AffineRelaxation.relaxModule (0 : K) sigma x)^[
          (1600 : Nat)] (1 : K)

/-- THEOREM 11: the scalar saturation/relaxation algebra has a single
zero-target receipt. -/
theorem singleZeroTargetRelaxationReceipt
    (K : Type*) [Field K] :
    SingleZeroTargetRelaxationReceipt K where
  scalar_one_step := zeroTarget_relaxModule_eq_keep_mul
  residual_iterate := residual_power_eq_zeroTarget_relaxModule_iterate
  rate_is_complement_zero_target :=
    complement_bumpSatField_eq_zeroTarget_relaxModule_keep
  zero_absorbing := zeroTarget_relaxModule_zero_initial
  lambda1600_shape := lambda1600_residual_power_eq_zeroTarget_iterate

end StandardModelConstraint
end SaturationMonoid

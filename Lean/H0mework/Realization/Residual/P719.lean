import H0mework.Realization.Residual.P243
import H0mework.Realization.Relaxation.P718

/-!
# Proposition 719: residual accounting uniquely induces the noisy-OR action

P718 proves that the target-general residual law forces the one-step update
`relaxModule`.

This file pushes that uniqueness through the whole same-target dynamics.  Any
update family `f target sigma x` satisfying the residual accounting law is not
merely pointwise equal to `relaxModule`; it is forced to carry the same
noisy-OR composition, commutativity, associativity, endpoints, absorbing target,
and finite-iterate collapse.  Thus the unified relaxation law is the unique
same-target action of the saturation/noisy-OR carrier.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Residual-accounted update families -/

/-- A target-general update family obeys residual accounting when the remaining
residual to the target is multiplied by the keep factor `1 - sigma`. -/
def TargetResidualLaw
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E) : Prop :=
  ∀ target : E, ∀ sigma : K, ∀ x : E,
    target - f target sigma x = (1 - sigma) • (target - x)

/-- THEOREM 1: the residual law forces the one-step update family to be
`relaxModule`. -/
theorem residualLaw_unique_step
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f) :
    ∀ target : E, ∀ sigma : K, ∀ x : E,
      f target sigma x = relaxModule target sigma x :=
  relaxModule_unique_of_target_residual_law f hres

/-! ## Forced noisy-OR action laws -/

/-- THEOREM 2: any residual-accounted update family composes by noisy-OR on
same-target steps. -/
theorem residualLaw_same_target_noisy_or
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target x : E) (sigma1 sigma2 : K) :
    f target sigma2 (f target sigma1 x) =
      f target (satOrField sigma1 sigma2) x := by
  have hf := residualLaw_unique_step f hres
  rw [hf target sigma1 x, hf target sigma2 (relaxModule target sigma1 x),
    hf target (satOrField sigma1 sigma2) x]
  exact relaxModule_compose target x sigma1 sigma2

/-- THEOREM 3: same-target residual-accounted steps commute. -/
theorem residualLaw_same_target_commutes
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target x : E) (sigma1 sigma2 : K) :
    f target sigma2 (f target sigma1 x) =
      f target sigma1 (f target sigma2 x) := by
  have hf := residualLaw_unique_step f hres
  rw [hf target sigma1 x, hf target sigma2 (relaxModule target sigma1 x),
    hf target sigma2 x, hf target sigma1 (relaxModule target sigma2 x)]
  exact relaxModule_compose_comm target x sigma1 sigma2

/-- THEOREM 4: same-target residual-accounted steps associate through the
noisy-OR rate law. -/
theorem residualLaw_same_target_associates
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target x : E) (sigma1 sigma2 sigma3 : K) :
    f target sigma3 (f target sigma2 (f target sigma1 x)) =
      f target (satOrField sigma1 (satOrField sigma2 sigma3)) x := by
  have hf := residualLaw_unique_step f hres
  rw [hf target sigma1 x, hf target sigma2 (relaxModule target sigma1 x),
    hf target sigma3 (relaxModule target sigma2 (relaxModule target sigma1 x)),
    hf target (satOrField sigma1 (satOrField sigma2 sigma3)) x]
  exact relaxModule_compose_assoc target x sigma1 sigma2 sigma3

/-! ## Forced endpoints and absorbing target -/

/-- THEOREM 5: rate `0` is forced to be no-op. -/
theorem residualLaw_zero_rate_noop
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target x : E) :
    f target (0 : K) x = x := by
  rw [residualLaw_unique_step f hres target 0 x]
  exact relaxModule_zero target x

/-- THEOREM 6: rate `1` is forced to hit the target directly. -/
theorem residualLaw_one_rate_hits_target
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target x : E) :
    f target (1 : K) x = target := by
  rw [residualLaw_unique_step f hres target 1 x]
  exact relaxModule_one target x

/-- THEOREM 7: the target is forced to be an absorbing state. -/
theorem residualLaw_target_absorbing
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target : E) (sigma : K) :
    f target sigma target = target := by
  rw [residualLaw_unique_step f hres target sigma target]
  exact relaxModule_target_absorbing target sigma

/-! ## Forced finite iteration law -/

/-- THEOREM 8: finite iterates of any residual-accounted same-target update
collapse to one update with the effective rate `1 - (1-sigma)^n`. -/
theorem residualLaw_iterate_eq_single_pow_rate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target : E) (sigma : K) (x : E) (n : Nat) :
    (fun y : E => f target sigma y)^[n] x =
      f target (1 - (1 - sigma) ^ n) x := by
  have hf := residualLaw_unique_step f hres
  have hfun :
      (fun y : E => f target sigma y) =
        (fun y : E => relaxModule target sigma y) := by
    funext y
    exact hf target sigma y
  rw [hfun, relaxModule_iterate_eq_single_pow_rate]
  exact (hf target (1 - (1 - sigma) ^ n) x).symm

/-- THEOREM 9: finite iterates of any residual-accounted same-target update
have geometric residual. -/
theorem target_sub_residualLaw_iterate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target : E) (sigma : K) (x : E) (n : Nat) :
    target - (fun y : E => f target sigma y)^[n] x =
      ((1 - sigma) ^ n) • (target - x) := by
  have hf := residualLaw_unique_step f hres
  have hfun :
      (fun y : E => f target sigma y) =
        (fun y : E => relaxModule target sigma y) := by
    funext y
    exact hf target sigma y
  rw [hfun]
  exact target_sub_relaxModule_iterate target sigma x n

/-! ## Certificate -/

/-- P719 certificate: residual accounting uniquely induces the whole
same-target noisy-OR action, not just the one-step formula. -/
structure ResidualAccountedNoisyOrActionUniquenessCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  one_step_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target : E, ∀ sigma : K, ∀ x : E,
        f target sigma x = relaxModule target sigma x
  same_target_noisy_or_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target x : E, ∀ sigma1 sigma2 : K,
        f target sigma2 (f target sigma1 x) =
          f target (satOrField sigma1 sigma2) x
  same_target_commutes_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target x : E, ∀ sigma1 sigma2 : K,
        f target sigma2 (f target sigma1 x) =
          f target sigma1 (f target sigma2 x)
  same_target_associates_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target x : E, ∀ sigma1 sigma2 sigma3 : K,
        f target sigma3 (f target sigma2 (f target sigma1 x)) =
          f target (satOrField sigma1 (satOrField sigma2 sigma3)) x
  zero_rate_noop_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target x : E,
        f target (0 : K) x = x
  one_rate_hits_target_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target x : E,
        f target (1 : K) x = target
  target_absorbing_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target : E, ∀ sigma : K,
        f target sigma target = target
  iterate_pow_rate_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target : E, ∀ sigma : K, ∀ x : E, ∀ n : Nat,
        (fun y : E => f target sigma y)^[n] x =
          f target (1 - (1 - sigma) ^ n) x
  iterate_residual_geometric :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target : E, ∀ sigma : K, ∀ x : E, ∀ n : Nat,
        target - (fun y : E => f target sigma y)^[n] x =
          ((1 - sigma) ^ n) • (target - x)

/-- THEOREM 10: residual accounting supplies the P719 unique noisy-OR action
certificate. -/
theorem residualAccountedNoisyOrActionUniquenessCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualAccountedNoisyOrActionUniquenessCertificate K E where
  one_step_unique := residualLaw_unique_step
  same_target_noisy_or_unique := residualLaw_same_target_noisy_or
  same_target_commutes_unique := residualLaw_same_target_commutes
  same_target_associates_unique := residualLaw_same_target_associates
  zero_rate_noop_unique := residualLaw_zero_rate_noop
  one_rate_hits_target_unique := residualLaw_one_rate_hits_target
  target_absorbing_unique := residualLaw_target_absorbing
  iterate_pow_rate_unique := residualLaw_iterate_eq_single_pow_rate
  iterate_residual_geometric := target_sub_residualLaw_iterate

end AffineRelaxation
end SaturationMonoid

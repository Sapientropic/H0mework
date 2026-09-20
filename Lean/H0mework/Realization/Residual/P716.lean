import H0mework.Realization.RelaxationFlow.P715

/-!
# Proposition 716: finite relaxation gain is exactly consumed headroom

P715 identifies the saturation face (`T = 1`) and the keep face (`T = 0`) of
the same affine relaxation flow.

This file proves the finite accounting law behind the "energy = information"
reading of that flow: the sum of all finite one-step gains on the target-one
face is exactly the headroom consumed; equivalently, the sum of all finite
one-step losses on the target-zero keep face is exactly the keep consumed.
The two accounts are the same equation in complementary coordinates.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra
open scoped BigOperators

/-! ## Generic finite telescoping -/

/-- THEOREM 1: forward finite differences telescope. -/
theorem sum_range_forward_differences
    (f : ℕ -> ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f (i + 1) - f i)) = f n - f 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- THEOREM 2: backward finite differences telescope. -/
theorem sum_range_backward_differences
    (f : ℕ -> ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-! ## Target-one gain accounting -/

/-- Target-one state after `n` fixed-rate saturation bumps. -/
def targetOneBumpState (h σ : ℝ) (n : ℕ) : ℝ :=
  (fun x : ℝ => bumpSatField x σ)^[n] h

/-- Target-zero keep state after `n` fixed-rate keep relaxations. -/
def targetZeroKeepState (x σ : ℝ) (n : ℕ) : ℝ :=
  (fun y : ℝ => relaxModule (0 : ℝ) σ y)^[n] x

/-- One target-one gain from state `h` at rate `σ`. -/
def targetOneStepGain (h σ : ℝ) : ℝ :=
  bumpSatField h σ - h

/-- One target-zero keep loss from state `x` at rate `σ`. -/
def targetZeroStepLoss (x σ : ℝ) : ℝ :=
  x - relaxModule (0 : ℝ) σ x

/-- THEOREM 3: a target-one bump gains exactly `σ` times current headroom. -/
theorem targetOneStepGain_eq_sigma_headroom
    (h σ : ℝ) :
    targetOneStepGain h σ = σ * (1 - h) := by
  unfold targetOneStepGain bumpSatField
  ring

/-- THEOREM 4: a target-zero keep step loses exactly `σ` times current keep. -/
theorem targetZeroStepLoss_eq_sigma_keep
    (x σ : ℝ) :
    targetZeroStepLoss x σ = σ * x := by
  unfold targetZeroStepLoss relaxModule
  ring

/-- THEOREM 5: after `n` target-one bumps, the final rate coordinate is the
initial coordinate plus the consumed headroom. -/
theorem targetOneBumpState_eq_initial_plus_consumed_headroom
    (h σ : ℝ) (n : ℕ) :
    targetOneBumpState h σ n =
      h + (1 - h) * (1 - (1 - σ) ^ n) := by
  unfold targetOneBumpState
  have hfun :
      (fun x : ℝ => bumpSatField x σ) =
        (fun x : ℝ => relaxModule (1 : ℝ) σ x) := by
    funext x
    exact (oneTarget_relaxModule_eq_bumpSatField x σ).symm
  rw [hfun]
  rw [relaxModule_iterate_eq_closed]
  ring

/-- THEOREM 6: the sum of all target-one gains over `n` fixed-rate bumps is
exactly the consumed headroom. -/
theorem targetOneGainSum_eq_consumed_headroom
    (h σ : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        targetOneStepGain (targetOneBumpState h σ i) σ)
      =
      (1 - h) * (1 - (1 - σ) ^ n) := by
  have hgain :
      (∑ i ∈ Finset.range n,
          targetOneStepGain (targetOneBumpState h σ i) σ)
        =
        (∑ i ∈ Finset.range n,
          (targetOneBumpState h σ (i + 1) -
            targetOneBumpState h σ i)) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold targetOneStepGain targetOneBumpState
    rw [Function.iterate_succ_apply']
  have htel :=
    sum_range_forward_differences (fun i => targetOneBumpState h σ i) n
  have hclosed :
      targetOneBumpState h σ n - targetOneBumpState h σ 0 =
        (1 - h) * (1 - (1 - σ) ^ n) := by
    rw [targetOneBumpState_eq_initial_plus_consumed_headroom]
    unfold targetOneBumpState
    simp
  calc
    (∑ i ∈ Finset.range n,
        targetOneStepGain (targetOneBumpState h σ i) σ)
        =
        (∑ i ∈ Finset.range n,
          (targetOneBumpState h σ (i + 1) -
            targetOneBumpState h σ i)) := hgain
    _ = targetOneBumpState h σ n - targetOneBumpState h σ 0 := htel
    _ = (1 - h) * (1 - (1 - σ) ^ n) := hclosed

/-! ## Target-zero loss accounting -/

/-- THEOREM 7: after `n` target-zero keep steps, the keep coordinate is scaled
by the geometric residual. -/
theorem targetZeroKeepState_eq_residual_mul
    (x σ : ℝ) (n : ℕ) :
    targetZeroKeepState x σ n = ((1 - σ) ^ n) * x := by
  unfold targetZeroKeepState
  exact zeroTarget_relaxModule_iterate_eq_keep_pow x σ n

/-- THEOREM 8: the sum of all target-zero keep losses over `n` fixed-rate steps
is exactly the consumed keep. -/
theorem targetZeroLossSum_eq_consumed_keep
    (x σ : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        targetZeroStepLoss (targetZeroKeepState x σ i) σ)
      =
      x * (1 - (1 - σ) ^ n) := by
  have hloss :
      (∑ i ∈ Finset.range n,
          targetZeroStepLoss (targetZeroKeepState x σ i) σ)
        =
        (∑ i ∈ Finset.range n,
          (targetZeroKeepState x σ i -
            targetZeroKeepState x σ (i + 1))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold targetZeroStepLoss targetZeroKeepState
    rw [Function.iterate_succ_apply']
  have htel :=
    sum_range_backward_differences (fun i => targetZeroKeepState x σ i) n
  have hclosed :
      targetZeroKeepState x σ 0 - targetZeroKeepState x σ n =
        x * (1 - (1 - σ) ^ n) := by
    unfold targetZeroKeepState
    simp
    rw [zeroTarget_relaxModule_iterate_eq_keep_pow]
    ring_nf
  calc
    (∑ i ∈ Finset.range n,
        targetZeroStepLoss (targetZeroKeepState x σ i) σ)
        =
        (∑ i ∈ Finset.range n,
          (targetZeroKeepState x σ i -
            targetZeroKeepState x σ (i + 1))) := hloss
    _ = targetZeroKeepState x σ 0 - targetZeroKeepState x σ n := htel
    _ = x * (1 - (1 - σ) ^ n) := hclosed

/-- THEOREM 9: target-one gain accounting and target-zero keep-loss accounting
are the same finite consumed-headroom law under `x = 1 - h`. -/
theorem targetOneGainSum_eq_targetZeroLossSum_of_complement
    (h σ : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        targetOneStepGain (targetOneBumpState h σ i) σ)
      =
      (∑ i ∈ Finset.range n,
        targetZeroStepLoss (targetZeroKeepState (1 - h) σ i) σ) := by
  rw [targetOneGainSum_eq_consumed_headroom]
  rw [targetZeroLossSum_eq_consumed_keep]

/-! ## Certificate -/

/-- P716 certificate: finite target-one gain and target-zero keep loss are one
conserved finite relaxation account. -/
structure FiniteRelaxationAccountingCertificate : Prop where
  forward_telescope :
    ∀ f : ℕ -> ℝ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (f (i + 1) - f i)) = f n - f 0
  backward_telescope :
    ∀ f : ℕ -> ℝ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n
  one_step_gain :
    ∀ h σ : ℝ,
      targetOneStepGain h σ = σ * (1 - h)
  one_step_loss :
    ∀ x σ : ℝ,
      targetZeroStepLoss x σ = σ * x
  target_one_state :
    ∀ h σ : ℝ, ∀ n : ℕ,
      targetOneBumpState h σ n =
        h + (1 - h) * (1 - (1 - σ) ^ n)
  target_one_gain_sum :
    ∀ h σ : ℝ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
          targetOneStepGain (targetOneBumpState h σ i) σ)
        =
        (1 - h) * (1 - (1 - σ) ^ n)
  target_zero_state :
    ∀ x σ : ℝ, ∀ n : ℕ,
      targetZeroKeepState x σ n = ((1 - σ) ^ n) * x
  target_zero_loss_sum :
    ∀ x σ : ℝ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
          targetZeroStepLoss (targetZeroKeepState x σ i) σ)
        =
        x * (1 - (1 - σ) ^ n)
  complement_accounts_same :
    ∀ h σ : ℝ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
          targetOneStepGain (targetOneBumpState h σ i) σ)
        =
        (∑ i ∈ Finset.range n,
          targetZeroStepLoss (targetZeroKeepState (1 - h) σ i) σ)

/-- THEOREM 10: the real scalar relaxation carrier supplies the finite
gain/loss accounting certificate. -/
theorem finiteRelaxationAccountingCertificate :
    FiniteRelaxationAccountingCertificate where
  forward_telescope := sum_range_forward_differences
  backward_telescope := sum_range_backward_differences
  one_step_gain := targetOneStepGain_eq_sigma_headroom
  one_step_loss := targetZeroStepLoss_eq_sigma_keep
  target_one_state := targetOneBumpState_eq_initial_plus_consumed_headroom
  target_one_gain_sum := targetOneGainSum_eq_consumed_headroom
  target_zero_state := targetZeroKeepState_eq_residual_mul
  target_zero_loss_sum := targetZeroLossSum_eq_consumed_keep
  complement_accounts_same :=
    targetOneGainSum_eq_targetZeroLossSum_of_complement

end AffineRelaxation
end SaturationMonoid

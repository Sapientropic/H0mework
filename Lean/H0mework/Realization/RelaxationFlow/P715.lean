import H0mework.Realization.Faces.P714
import H0mework.Realization.RelaxationFlow.P293

/-!
# Proposition 715: saturation projections sample the continuous envelope

P714 proves that the seven-symbol affine relaxation grammar projects to
saturation at target one and to keep/residual scaling at target zero.

P245/P293 prove the continuous-time real envelope sampled by
`realDecayRate lambda t = 1 - exp(-lambda*t)`.

This file welds those two facts together: the salience/rate face (`T = 1`) and
the keep/residual face (`T = 0`) are exactly the sampled continuous relaxation
flow read through the same two target projections.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## Continuous target-one projection -/

/-- THEOREM 1: the continuous target-one flow is exactly a saturation bump by
the induced exponential rate. -/
theorem oneTarget_realDecayRelaxFlow_eq_bumpSatField
    (h lambda t : ℝ) :
    realDecayRelaxFlow (1 : ℝ) lambda t h =
      bumpSatField h (realDecayRate lambda t) := by
  unfold realDecayRelaxFlow
  exact oneTarget_relaxModule_eq_bumpSatField h (realDecayRate lambda t)

/-- THEOREM 2: composing a rate with the continuous exponential rate is
target-one continuous flow on the rate coordinate. -/
theorem satOrField_realDecayRate_eq_oneTarget_flow_on_rate
    (ρ lambda t : ℝ) :
    satOrField ρ (realDecayRate lambda t) =
      realDecayRelaxFlow (1 : ℝ) lambda t ρ := by
  unfold realDecayRelaxFlow
  exact satOrField_eq_oneTarget_relaxModule ρ (realDecayRate lambda t)

/-- THEOREM 3: target-one continuous residual is headroom times the exponential
keep factor. -/
theorem oneTarget_realDecayRelaxFlow_residual_mul
    (h lambda t : ℝ) :
    1 - realDecayRelaxFlow (1 : ℝ) lambda t h =
      (1 - h) * realDecayResidual lambda t := by
  unfold realDecayRelaxFlow
  rw [oneTarget_relaxModule_residual_mul]
  unfold realDecayRate
  ring

/-! ## Continuous target-zero projection -/

/-- THEOREM 4: the continuous target-zero flow is exactly keep scaling by the
exponential residual. -/
theorem zeroTarget_realDecayRelaxFlow_eq_residual_mul
    (x lambda t : ℝ) :
    realDecayRelaxFlow (0 : ℝ) lambda t x =
      realDecayResidual lambda t * x := by
  unfold realDecayRelaxFlow
  rw [zeroTarget_relaxModule_eq_keep_mul]
  unfold realDecayRate
  ring

/-! ## Sampled finite iteration through both projections -/

/-- THEOREM 5: finite iteration of target-one saturation bumps sampled from the
continuous envelope is exactly the target-one continuous flow at total sampled
time. -/
theorem oneTarget_bumpSatField_iterate_realDecayRate_eq_total_time
    (h lambda step : ℝ) (n : ℕ) :
    (fun x : ℝ => bumpSatField x (realDecayRate lambda step))^[n] h =
      realDecayRelaxFlow (1 : ℝ) lambda ((n : ℝ) * step) h := by
  have hfun :
      (fun x : ℝ => bumpSatField x (realDecayRate lambda step)) =
        (fun x : ℝ => relaxModule (1 : ℝ) (realDecayRate lambda step) x) := by
    funext x
    exact (oneTarget_relaxModule_eq_bumpSatField
      x (realDecayRate lambda step)).symm
  rw [hfun]
  exact relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow
    (1 : ℝ) lambda step h n

/-- THEOREM 6: finite iteration of target-zero sampled keep scaling is exactly
the target-zero continuous flow at total sampled time. -/
theorem zeroTarget_relaxModule_iterate_realDecayRate_eq_total_time
    (x lambda step : ℝ) (n : ℕ) :
    (fun y : ℝ => relaxModule (0 : ℝ) (realDecayRate lambda step) y)^[n] x =
      realDecayRelaxFlow (0 : ℝ) lambda ((n : ℝ) * step) x := by
  exact relaxModule_iterate_realDecayRate_eq_realDecayRelaxFlow
    (0 : ℝ) lambda step x n

/-- THEOREM 7: the target-zero sampled finite iterate is the continuous
exponential residual at total sampled time times the initial keep coordinate. -/
theorem zeroTarget_relaxModule_iterate_realDecayRate_eq_residual_mul
    (x lambda step : ℝ) (n : ℕ) :
    (fun y : ℝ => relaxModule (0 : ℝ) (realDecayRate lambda step) y)^[n] x =
      realDecayResidual lambda ((n : ℝ) * step) * x := by
  rw [zeroTarget_relaxModule_iterate_realDecayRate_eq_total_time]
  exact zeroTarget_realDecayRelaxFlow_eq_residual_mul
    x lambda ((n : ℝ) * step)

/-! ## Certificate -/

/-- P715 certificate: the target-one saturation face and target-zero keep face
of the seven-symbol grammar are both sampled by the same continuous exponential
relaxation envelope. -/
structure SevenSymbolContinuousProjectionCertificate : Prop where
  target_one_flow_is_bump :
    ∀ h lambda t : ℝ,
      realDecayRelaxFlow (1 : ℝ) lambda t h =
        bumpSatField h (realDecayRate lambda t)
  rate_flow_is_target_one :
    ∀ ρ lambda t : ℝ,
      satOrField ρ (realDecayRate lambda t) =
        realDecayRelaxFlow (1 : ℝ) lambda t ρ
  target_one_flow_residual :
    ∀ h lambda t : ℝ,
      1 - realDecayRelaxFlow (1 : ℝ) lambda t h =
        (1 - h) * realDecayResidual lambda t
  target_zero_flow_is_keep :
    ∀ x lambda t : ℝ,
      realDecayRelaxFlow (0 : ℝ) lambda t x =
        realDecayResidual lambda t * x
  target_one_sampled_iterate :
    ∀ h lambda step : ℝ, ∀ n : ℕ,
      (fun x : ℝ => bumpSatField x (realDecayRate lambda step))^[n] h =
        realDecayRelaxFlow (1 : ℝ) lambda ((n : ℝ) * step) h
  target_zero_sampled_iterate :
    ∀ x lambda step : ℝ, ∀ n : ℕ,
      (fun y : ℝ => relaxModule (0 : ℝ) (realDecayRate lambda step) y)^[n] x =
        realDecayRelaxFlow (0 : ℝ) lambda ((n : ℝ) * step) x
  target_zero_sampled_residual :
    ∀ x lambda step : ℝ, ∀ n : ℕ,
      (fun y : ℝ => relaxModule (0 : ℝ) (realDecayRate lambda step) y)^[n] x =
        realDecayResidual lambda ((n : ℝ) * step) * x
  fixed_target_bridge :
    DiscreteContinuousFixedTargetBridgeCertificate ℝ

/-- THEOREM 8: the real scalar carrier supplies the full P715 continuous
projection certificate. -/
theorem sevenSymbolContinuousProjectionCertificate :
    SevenSymbolContinuousProjectionCertificate where
  target_one_flow_is_bump := oneTarget_realDecayRelaxFlow_eq_bumpSatField
  rate_flow_is_target_one := satOrField_realDecayRate_eq_oneTarget_flow_on_rate
  target_one_flow_residual := oneTarget_realDecayRelaxFlow_residual_mul
  target_zero_flow_is_keep := zeroTarget_realDecayRelaxFlow_eq_residual_mul
  target_one_sampled_iterate :=
    oneTarget_bumpSatField_iterate_realDecayRate_eq_total_time
  target_zero_sampled_iterate :=
    zeroTarget_relaxModule_iterate_realDecayRate_eq_total_time
  target_zero_sampled_residual :=
    zeroTarget_relaxModule_iterate_realDecayRate_eq_residual_mul
  fixed_target_bridge := discreteContinuousFixedTargetBridgeCertificate

end AffineRelaxation
end SaturationMonoid

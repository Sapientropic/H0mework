import H0mework.Realization.RelaxationAlgebra.P724

/-!
# Proposition 725: affine endpoint laws force the final chart spine

P724 proves that target-chart complement-linearity plus target-one rate readout
forces the whole relaxation spine.

This file removes that remaining hypothesis on the real scalar carrier.  The
weaker-looking target/rate affine endpoint laws from P718 already force the
P724 chart law:

`target - f target sigma x = (1-sigma) * (target-x)`.

So the final chain is no longer

`assume chart-complement-linear -> relaxTo`.

It is

`target/rate affine + endpoint laws -> chart-complement-linear
 -> bumpSat/relaxTo/noisy-OR/energy`.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra
open EnergyLedgerProjection

/-! ## Affine endpoint laws force the P724 hypotheses -/

/-- THEOREM 1: the scalar target/rate affine endpoint laws force P724's
target-chart complement-linear hypothesis, with keep factor `1-sigma`. -/
theorem targetRateAffineEndpoint_forces_chartComplementLinear
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target) :
    IsTargetChartComplementLinearUpdate f := by
  exact ⟨fun sigma : ℝ => 1 - sigma, by
    intro target sigma x
    exact target_residual_law_of_target_rate_affine_endpoint_laws
      f hlin hzero hone target sigma x⟩

/-- THEOREM 2: the same endpoint laws force target-one empty-state rate
readout, the second P724 hypothesis. -/
theorem targetRateAffineEndpoint_forces_rateReadout
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target) :
    ∀ sigma : ℝ, f 1 sigma 0 = sigma := by
  intro sigma
  rw [relaxTo_unique_of_target_rate_affine_endpoint_laws f hlin hzero hone]
  unfold relaxTo
  ring

/-! ## The final spine inherited from P724 -/

/-- THEOREM 3: target/rate affine endpoint laws force the full target-general
update to be `relaxTo` through the P724 chart spine. -/
theorem targetRateAffineEndpoint_forces_relaxTo_via_chartSpine
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target) :
    ∀ target sigma x : ℝ, f target sigma x = relaxTo target sigma x :=
  relaxTo_unique_of_targetChartComplementLinear_rateReadout
    f
    (targetRateAffineEndpoint_forces_chartComplementLinear f hlin hzero hone)
    (targetRateAffineEndpoint_forces_rateReadout f hlin hzero hone)

/-- THEOREM 4: target/rate affine endpoint laws force same-target noisy-OR
composition. -/
theorem targetRateAffineEndpoint_forces_sameTarget_noisyOr
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target)
    (target x sigma1 sigma2 : ℝ) :
    f target sigma2 (f target sigma1 x) =
      f target (satOrField sigma1 sigma2) x :=
  targetChart_forced_same_target_noisy_or
    f
    (targetRateAffineEndpoint_forces_chartComplementLinear f hlin hzero hone)
    (targetRateAffineEndpoint_forces_rateReadout f hlin hzero hone)
    target x sigma1 sigma2

/-- THEOREM 5: target/rate affine endpoint laws force same-target
commutativity. -/
theorem targetRateAffineEndpoint_forces_sameTarget_commutes
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target)
    (target x sigma1 sigma2 : ℝ) :
    f target sigma2 (f target sigma1 x) =
      f target sigma1 (f target sigma2 x) :=
  targetChart_forced_same_target_commutes
    f
    (targetRateAffineEndpoint_forces_chartComplementLinear f hlin hzero hone)
    (targetRateAffineEndpoint_forces_rateReadout f hlin hzero hone)
    target x sigma1 sigma2

/-- THEOREM 6: target/rate affine endpoint laws force scalar residual-energy
scaling by `(1-sigma)^2`. -/
theorem targetRateAffineEndpoint_forces_scalarEnergy_step
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target)
    (target sigma x : ℝ) :
    scalarTargetResidualEnergy target (f target sigma x) =
      (1 - sigma) ^ 2 * scalarTargetResidualEnergy target x :=
  scalarTargetResidualEnergy_targetChart_step_eq
    f
    (targetRateAffineEndpoint_forces_chartComplementLinear f hlin hzero hone)
    (targetRateAffineEndpoint_forces_rateReadout f hlin hzero hone)
    target sigma x

/-! ## Certificate -/

/-- P725 certificate: the P724 final chart spine is forced by the more primitive
scalar target/rate affine endpoint laws. -/
structure AffineEndpointForcedChartSpineCertificate : Prop where
  affine_endpoint_chart_complement_linear :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      IsTargetChartComplementLinearUpdate f
  affine_endpoint_rate_readout :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ sigma : ℝ, f 1 sigma 0 = sigma
  affine_endpoint_target_general_unique :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ target sigma x : ℝ, f target sigma x = relaxTo target sigma x
  affine_endpoint_same_target_noisy_or :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ target x sigma1 sigma2 : ℝ,
        f target sigma2 (f target sigma1 x) =
          f target (satOrField sigma1 sigma2) x
  affine_endpoint_same_target_commutes :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ target x sigma1 sigma2 : ℝ,
        f target sigma2 (f target sigma1 x) =
          f target sigma1 (f target sigma2 x)
  affine_endpoint_scalar_energy_step :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ target sigma x : ℝ,
        scalarTargetResidualEnergy target (f target sigma x) =
          (1 - sigma) ^ 2 * scalarTargetResidualEnergy target x
  inherited_target_chart_spine :
    TargetChartForcedUnifiedSpineCertificate (K := ℝ)
  inherited_hamiltonian_sat_projection :
    TargetChartForcedHamiltonianSATProjectionCertificate

/-- THEOREM 7: the real scalar affine endpoint surface supplies the final
chart-spine certificate. -/
theorem affineEndpointForcedChartSpineCertificate :
    AffineEndpointForcedChartSpineCertificate where
  affine_endpoint_chart_complement_linear :=
    targetRateAffineEndpoint_forces_chartComplementLinear
  affine_endpoint_rate_readout :=
    targetRateAffineEndpoint_forces_rateReadout
  affine_endpoint_target_general_unique :=
    targetRateAffineEndpoint_forces_relaxTo_via_chartSpine
  affine_endpoint_same_target_noisy_or :=
    targetRateAffineEndpoint_forces_sameTarget_noisyOr
  affine_endpoint_same_target_commutes :=
    targetRateAffineEndpoint_forces_sameTarget_commutes
  affine_endpoint_scalar_energy_step :=
    targetRateAffineEndpoint_forces_scalarEnergy_step
  inherited_target_chart_spine :=
    targetChartForcedUnifiedSpineCertificate
  inherited_hamiltonian_sat_projection :=
    targetChartForcedHamiltonianSATProjectionCertificate

end AffineRelaxation
end SaturationMonoid

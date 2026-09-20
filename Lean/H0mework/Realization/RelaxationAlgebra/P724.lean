import H0mework.Realization.RelaxationAlgebra.P723

/-!
# Proposition 724: target-chart complement linearity forces the whole spine

P723 proves the target-one final uniqueness theorem:

`1 - f h sigma = keep sigma * (1-h)` plus `f 0 sigma = sigma`
forces `f = bumpSatField`.

This file lifts that result without changing coordinates by hand.  A
target-general update is chart-complement-linear when every target chart
transports the residual to the target by the same keep factor:

`target - f target sigma x = keep sigma * (target-x)`.

If the target-one empty state reads out the rate, `f 1 sigma 0 = sigma`, then
the target-one chart is exactly P723, so the keep factor is forced to
`1-sigma`.  The full target-general update is therefore forced to be

`relaxTo target sigma x = x + sigma * (target-x)`.

This is the single algebraic throat:

`complement-linear headroom -> bumpSat -> target-general relaxation
 -> noisy-OR action -> residual energy ledger -> Hamiltonian/SAT energy`.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra
open EnergyLedgerProjection

universe u v

variable {K : Type u} [Field K]

/-! ## Target-chart complement linearity -/

/-- A scalar target-general update is target-chart complement-linear when the
residual to every target is transported by a rate-dependent keep factor. -/
def IsTargetChartComplementLinearUpdate (f : K -> K -> K -> K) : Prop :=
  ∃ keep : K -> K, ∀ target sigma x : K,
    target - f target sigma x = keep sigma * (target - x)

/-- THEOREM 1: target-chart complement-linearity restricts at `target=1` to
P723's target-one complement-linear form. -/
theorem targetChart_targetOne_is_complementLinear
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f) :
    IsComplementLinearTargetOneUpdate (fun h sigma : K => f 1 sigma h) := by
  rcases hchart with ⟨keep, hkeep⟩
  exact ⟨keep, by
    intro h sigma
    exact hkeep 1 sigma h⟩

/-- THEOREM 2: target-chart complement-linearity plus target-one empty-state
rate readout forces the keep factor to be `1-sigma`. -/
theorem targetChart_keepFactor_forced
    (f : K -> K -> K -> K) (keep : K -> K)
    (hkeep : ∀ target sigma x : K,
      target - f target sigma x = keep sigma * (target - x))
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma) :
    ∀ sigma : K, keep sigma = 1 - sigma :=
  complementLinear_keepFactor_forced
    (fun h sigma : K => f 1 sigma h)
    keep
    (by
      intro h sigma
      exact hkeep 1 sigma h)
    hrate

/-- THEOREM 3: the target-one chart itself is forced to be `bumpSatField`. -/
theorem targetChart_targetOne_unique_bumpSat
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma) :
    ∀ h sigma : K, f 1 sigma h = bumpSatField h sigma :=
  bumpSat_unique_of_complementLinear_rateReadout
    (fun h sigma : K => f 1 sigma h)
    (targetChart_targetOne_is_complementLinear f hchart)
    hrate

/-- THEOREM 4: the full target residual law is forced in every target chart. -/
theorem targetResidualLaw_of_targetChartComplementLinear_rateReadout
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma) :
    ∀ target sigma x : K,
      target - f target sigma x = (1 - sigma) * (target - x) := by
  rcases hchart with ⟨keep, hkeep⟩
  intro target sigma x
  rw [hkeep target sigma x,
    targetChart_keepFactor_forced f keep hkeep hrate sigma]

/-- THEOREM 5: target-chart complement-linearity plus target-one rate readout
forces the target-general affine relaxation formula. -/
theorem relaxTo_unique_of_targetChartComplementLinear_rateReadout
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma) :
    ∀ target sigma x : K, f target sigma x = relaxTo target sigma x := by
  intro target sigma x
  have hres :=
    targetResidualLaw_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma x
  calc
    f target sigma x = target - (target - f target sigma x) := by ring
    _ = target - ((1 - sigma) * (target - x)) := by rw [hres]
    _ = relaxTo target sigma x := by
      unfold relaxTo
      ring

/-! ## Forced same-target action from the chart law -/

/-- THEOREM 6: same-target chart-forced updates compose by noisy-OR. -/
theorem targetChart_forced_same_target_noisy_or
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma)
    (target x sigma1 sigma2 : K) :
    f target sigma2 (f target sigma1 x) =
      f target (satOrField sigma1 sigma2) x := by
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma1 x]
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma2
      (relaxTo target sigma1 x)]
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target (satOrField sigma1 sigma2) x]
  exact relaxTo_compose target x sigma1 sigma2

/-- THEOREM 7: same-target chart-forced updates commute. -/
theorem targetChart_forced_same_target_commutes
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma)
    (target x sigma1 sigma2 : K) :
    f target sigma2 (f target sigma1 x) =
      f target sigma1 (f target sigma2 x) := by
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma1 x]
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma2
      (relaxTo target sigma1 x)]
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma2 x]
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma1
      (relaxTo target sigma2 x)]
  exact relaxTo_compose_comm target x sigma1 sigma2

/-- THEOREM 8: rate `0` is forced to be the identity in every target chart. -/
theorem targetChart_forced_zero_rate_noop
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma)
    (target x : K) :
    f target 0 x = x := by
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target 0 x]
  exact relaxTo_zero target x

/-- THEOREM 9: rate `1` is forced to hit the target in every target chart. -/
theorem targetChart_forced_one_rate_hits_target
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma)
    (target x : K) :
    f target 1 x = target := by
  rw [relaxTo_unique_of_targetChartComplementLinear_rateReadout
      f hchart hrate target 1 x]
  exact relaxTo_one target x

/-! ## Forced scalar energy ledger -/

/-- Scalar squared target-residual energy. -/
def scalarTargetResidualEnergy (target x : K) : K :=
  (target - x) ^ 2

/-- THEOREM 10: chart-forced scalar residual energy scales by the square of
the keep factor. -/
theorem scalarTargetResidualEnergy_targetChart_step_eq
    (f : K -> K -> K -> K)
    (hchart : IsTargetChartComplementLinearUpdate f)
    (hrate : ∀ sigma : K, f 1 sigma 0 = sigma)
    (target sigma x : K) :
    scalarTargetResidualEnergy target (f target sigma x) =
      (1 - sigma) ^ 2 * scalarTargetResidualEnergy target x := by
  dsimp [scalarTargetResidualEnergy]
  rw [targetResidualLaw_of_targetChartComplementLinear_rateReadout
      f hchart hrate target sigma x]
  ring

/-! ## Certificate -/

/-- P724 certificate: P723's complement-linear target-one uniqueness forces
the target-general affine relaxation law, its noisy-OR action face, and the
scalar residual-energy ledger.  The finite Hamiltonian/SAT energy face is then
the already-certified zero-target residual ledger from P722. -/
structure TargetChartForcedUnifiedSpineCertificate : Prop where
  target_one_chart_is_p723 :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      IsComplementLinearTargetOneUpdate (fun h sigma : K => f 1 sigma h)
  keep_factor_forced :
    ∀ (f : K -> K -> K -> K) (keep : K -> K),
      (∀ target sigma x : K,
        target - f target sigma x = keep sigma * (target - x)) ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ sigma : K, keep sigma = 1 - sigma
  target_one_unique :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ h sigma : K, f 1 sigma h = bumpSatField h sigma
  target_residual_law_forced :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target sigma x : K,
        target - f target sigma x = (1 - sigma) * (target - x)
  target_general_unique :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target sigma x : K, f target sigma x = relaxTo target sigma x
  same_target_noisy_or_forced :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target x sigma1 sigma2 : K,
        f target sigma2 (f target sigma1 x) =
          f target (satOrField sigma1 sigma2) x
  same_target_commutes_forced :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target x sigma1 sigma2 : K,
        f target sigma2 (f target sigma1 x) =
          f target sigma1 (f target sigma2 x)
  zero_rate_noop_forced :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target x : K, f target 0 x = x
  one_rate_hits_target_forced :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target x : K, f target 1 x = target
  scalar_energy_step_forced :
    ∀ f : K -> K -> K -> K,
      IsTargetChartComplementLinearUpdate f ->
      (∀ sigma : K, f 1 sigma 0 = sigma) ->
      ∀ target sigma x : K,
        scalarTargetResidualEnergy target (f target sigma x) =
          (1 - sigma) ^ 2 * scalarTargetResidualEnergy target x

/-- THEOREM 11: every field supplies the target-chart forced unified spine. -/
theorem targetChartForcedUnifiedSpineCertificate :
    TargetChartForcedUnifiedSpineCertificate (K := K) where
  target_one_chart_is_p723 := targetChart_targetOne_is_complementLinear
  keep_factor_forced := targetChart_keepFactor_forced
  target_one_unique := targetChart_targetOne_unique_bumpSat
  target_residual_law_forced :=
    targetResidualLaw_of_targetChartComplementLinear_rateReadout
  target_general_unique :=
    relaxTo_unique_of_targetChartComplementLinear_rateReadout
  same_target_noisy_or_forced := targetChart_forced_same_target_noisy_or
  same_target_commutes_forced := targetChart_forced_same_target_commutes
  zero_rate_noop_forced := targetChart_forced_zero_rate_noop
  one_rate_hits_target_forced := targetChart_forced_one_rate_hits_target
  scalar_energy_step_forced := scalarTargetResidualEnergy_targetChart_step_eq

end AffineRelaxation

/-! ## Real energy/Hamiltonian-SAT projection of the same forced spine -/

namespace EnergyLedgerProjection

open AffineRelaxation
open ComplexityProjection

/-- P724 real projection certificate: the chart-forced scalar spine plus the
P722 zero-target Hamiltonian/SAT energy bridge. -/
structure TargetChartForcedHamiltonianSATProjectionCertificate : Prop where
  chart_forced_real_spine :
    TargetChartForcedUnifiedSpineCertificate (K := ℝ)
  forced_energy_ledger :
    HamiltonianSATEnergyFromResidualLedgerCertificate.{0, 0}

/-- THEOREM 12: the real target-chart forced spine projects to the certified
Hamiltonian/SAT zero-target energy ledger. -/
theorem targetChartForcedHamiltonianSATProjectionCertificate :
    TargetChartForcedHamiltonianSATProjectionCertificate where
  chart_forced_real_spine := targetChartForcedUnifiedSpineCertificate
  forced_energy_ledger := residualLedgerHamiltonianSATEnergyCertificate

end EnergyLedgerProjection
end SaturationMonoid

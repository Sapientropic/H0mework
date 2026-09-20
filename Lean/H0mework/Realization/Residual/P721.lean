import H0mework.Realization.Residual.P720

/-!
# Proposition 721: residual accounting uniquely induces the energy ledger

P719 proves that residual accounting forces the same-target noisy-OR action.
P720 proves that the same residual accounting forces the cross-target
commutator and target-transport geometry.

This file pushes the same spine into the energy word.  On any finite real
field, define energy as squared target residual

`E(target,x) = sum_i (target_i - x_i)^2`.

Then every residual-accounted update family, without any further runtime
choice, multiplies this energy by `(1-sigma)^2`, makes it nonincreasing on
`0 <= sigma <= 1`, strictly dissipates it on `0 < sigma < 1` whenever energy is
positive, and gives an exact work ledger

`initial energy = post energy + dissipated work`.

Thus the finite energy face is not an extra producer: it is the quadratic
residual readout forced by the same equation that already forced `relaxModule`,
noisy-OR composition, and cross-target obstruction.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open scoped BigOperators

set_option linter.checkUnivs false

/-! ## Canonical residual-square energy -/

/-- Squared target-residual energy over a finite real coordinate field. -/
def targetResidualEnergy {I : Type*} [Fintype I]
    (target x : I -> ℝ) : ℝ :=
  ∑ i, (target i - x i) ^ 2

/-- Work dissipated by one residual-accounted step with rate `sigma`. -/
def targetResidualWork {I : Type*} [Fintype I]
    (target x : I -> ℝ) (sigma : ℝ) : ℝ :=
  (1 - (1 - sigma) ^ 2) * targetResidualEnergy target x

/-- Work dissipated by `n` residual-accounted same-target steps. -/
def targetResidualIterateWork {I : Type*} [Fintype I]
    (target x : I -> ℝ) (sigma : ℝ) (n : ℕ) : ℝ :=
  (1 - ((1 - sigma) ^ 2) ^ n) * targetResidualEnergy target x

/-! ## One-step forced energy law -/

/-- THEOREM 1: squared target-residual energy is nonnegative. -/
theorem targetResidualEnergy_nonneg {I : Type*} [Fintype I]
    (target x : I -> ℝ) :
    0 <= targetResidualEnergy target x := by
  classical
  dsimp [targetResidualEnergy]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (target i - x i))

/-- THEOREM 2: any residual-accounted update family multiplies finite
target-residual energy exactly by `(1-sigma)^2`. -/
theorem targetResidualEnergy_residualLaw_step_eq
    {I : Type*} [Fintype I]
    (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ))
    (hres : TargetResidualLaw f)
    (target x : I -> ℝ) (sigma : ℝ) :
    targetResidualEnergy target (f target sigma x) =
      (1 - sigma) ^ 2 * targetResidualEnergy target x := by
  classical
  dsimp [targetResidualEnergy]
  rw [Finset.mul_sum]
  congr 1
  ext i
  have hi :
      target i - f target sigma x i =
        (1 - sigma) * (target i - x i) := by
    simpa using congrFun (hres target sigma x) i
  rw [hi]
  ring

/-- THEOREM 3: on `0 <= sigma <= 1`, residual-accounted finite energy cannot
increase. -/
theorem targetResidualEnergy_residualLaw_step_nonincreasing
    {I : Type*} [Fintype I]
    (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ))
    (hres : TargetResidualLaw f)
    (target x : I -> ℝ) (sigma : ℝ)
    (h0 : 0 <= sigma) (h1 : sigma <= 1) :
    targetResidualEnergy target (f target sigma x) <=
      targetResidualEnergy target x := by
  rw [targetResidualEnergy_residualLaw_step_eq f hres target x sigma]
  have hE : 0 <= targetResidualEnergy target x :=
    targetResidualEnergy_nonneg target x
  have hfactor : (1 - sigma) ^ 2 <= 1 := by
    nlinarith [sq_nonneg sigma, sq_nonneg (1 - sigma), h0, h1]
  exact mul_le_of_le_one_left hE hfactor

/-- THEOREM 4: on `0 < sigma < 1`, every positive residual energy strictly
dissipates. -/
theorem targetResidualEnergy_residualLaw_step_strict
    {I : Type*} [Fintype I]
    (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ))
    (hres : TargetResidualLaw f)
    (target x : I -> ℝ) (sigma : ℝ)
    (h0 : 0 < sigma) (h1 : sigma < 1)
    (hE : 0 < targetResidualEnergy target x) :
    targetResidualEnergy target (f target sigma x) <
      targetResidualEnergy target x := by
  rw [targetResidualEnergy_residualLaw_step_eq f hres target x sigma]
  have hfactor : (1 - sigma) ^ 2 < 1 := by
    nlinarith [sq_nonneg sigma, sq_nonneg (1 - sigma), h0, h1]
  exact mul_lt_of_lt_one_left hE hfactor

/-- THEOREM 5: one residual-accounted update has an exact energy/work
accounting law. -/
theorem targetResidualEnergy_step_plus_work_eq_initial
    {I : Type*} [Fintype I]
    (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ))
    (hres : TargetResidualLaw f)
    (target x : I -> ℝ) (sigma : ℝ) :
    targetResidualEnergy target (f target sigma x) +
        targetResidualWork target x sigma =
      targetResidualEnergy target x := by
  rw [targetResidualEnergy_residualLaw_step_eq f hres target x sigma]
  dsimp [targetResidualWork]
  ring

/-! ## Finite iteration forced energy law -/

/-- THEOREM 6: finite iterates of any residual-accounted same-target update
multiply finite target-residual energy by `((1-sigma)^2)^n`. -/
theorem targetResidualEnergy_residualLaw_iterate_eq
    {I : Type*} [Fintype I]
    (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ))
    (hres : TargetResidualLaw f)
    (target x : I -> ℝ) (sigma : ℝ) (n : ℕ) :
    targetResidualEnergy target ((fun y => f target sigma y)^[n] x) =
      ((1 - sigma) ^ 2) ^ n * targetResidualEnergy target x := by
  classical
  dsimp [targetResidualEnergy]
  rw [Finset.mul_sum]
  congr 1
  ext i
  have hi :
      target i - ((fun y => f target sigma y)^[n] x) i =
        ((1 - sigma) ^ n) * (target i - x i) := by
    simpa using congrFun
      (target_sub_residualLaw_iterate f hres target sigma x n) i
  have hpow :
      ((1 - sigma) ^ n) ^ 2 = ((1 - sigma) ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  rw [hi]
  rw [← hpow]
  ring

/-- THEOREM 7: finite residual-accounted iteration has an exact energy/work
ledger. -/
theorem targetResidualEnergy_iterate_plus_work_eq_initial
    {I : Type*} [Fintype I]
    (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ))
    (hres : TargetResidualLaw f)
    (target x : I -> ℝ) (sigma : ℝ) (n : ℕ) :
    targetResidualEnergy target ((fun y => f target sigma y)^[n] x) +
        targetResidualIterateWork target x sigma n =
      targetResidualEnergy target x := by
  rw [targetResidualEnergy_residualLaw_iterate_eq f hres target x sigma n]
  dsimp [targetResidualIterateWork]
  ring

/-! ## Certificate -/

/-- P721 certificate: residual accounting uniquely induces the finite
residual-square energy ledger. -/
structure ResidualAccountedEnergyLedgerCertificate : Prop where
  residual_energy_nonneg :
    ∀ {I : Type*} [Fintype I] (target x : I -> ℝ),
      0 <= targetResidualEnergy target x
  one_step_energy_eq :
    ∀ {I : Type*} [Fintype I]
      (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ)),
      TargetResidualLaw f ->
      ∀ target x : I -> ℝ, ∀ sigma : ℝ,
        targetResidualEnergy target (f target sigma x) =
          (1 - sigma) ^ 2 * targetResidualEnergy target x
  one_step_energy_nonincreasing :
    ∀ {I : Type*} [Fintype I]
      (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ)),
      TargetResidualLaw f ->
      ∀ target x : I -> ℝ, ∀ sigma : ℝ,
        0 <= sigma -> sigma <= 1 ->
          targetResidualEnergy target (f target sigma x) <=
            targetResidualEnergy target x
  one_step_energy_strict :
    ∀ {I : Type*} [Fintype I]
      (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ)),
      TargetResidualLaw f ->
      ∀ target x : I -> ℝ, ∀ sigma : ℝ,
        0 < sigma -> sigma < 1 ->
        0 < targetResidualEnergy target x ->
          targetResidualEnergy target (f target sigma x) <
            targetResidualEnergy target x
  one_step_work_ledger :
    ∀ {I : Type*} [Fintype I]
      (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ)),
      TargetResidualLaw f ->
      ∀ target x : I -> ℝ, ∀ sigma : ℝ,
        targetResidualEnergy target (f target sigma x) +
            targetResidualWork target x sigma =
          targetResidualEnergy target x
  iterate_energy_eq :
    ∀ {I : Type*} [Fintype I]
      (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ)),
      TargetResidualLaw f ->
      ∀ target x : I -> ℝ, ∀ sigma : ℝ, ∀ n : ℕ,
        targetResidualEnergy target ((fun y => f target sigma y)^[n] x) =
          ((1 - sigma) ^ 2) ^ n * targetResidualEnergy target x
  iterate_work_ledger :
    ∀ {I : Type*} [Fintype I]
      (f : (I -> ℝ) -> ℝ -> (I -> ℝ) -> (I -> ℝ)),
      TargetResidualLaw f ->
      ∀ target x : I -> ℝ, ∀ sigma : ℝ, ∀ n : ℕ,
        targetResidualEnergy target ((fun y => f target sigma y)^[n] x) +
            targetResidualIterateWork target x sigma n =
          targetResidualEnergy target x

/-- THEOREM 8: residual accounting supplies the forced energy-ledger
certificate. -/
theorem residualAccountedEnergyLedgerCertificate :
    ResidualAccountedEnergyLedgerCertificate where
  residual_energy_nonneg := by
    intro I _ target x
    exact targetResidualEnergy_nonneg target x
  one_step_energy_eq := by
    intro I _ f hres target x sigma
    exact targetResidualEnergy_residualLaw_step_eq f hres target x sigma
  one_step_energy_nonincreasing := by
    intro I _ f hres target x sigma h0 h1
    exact targetResidualEnergy_residualLaw_step_nonincreasing
      f hres target x sigma h0 h1
  one_step_energy_strict := by
    intro I _ f hres target x sigma h0 h1 hE
    exact targetResidualEnergy_residualLaw_step_strict
      f hres target x sigma h0 h1 hE
  one_step_work_ledger := by
    intro I _ f hres target x sigma
    exact targetResidualEnergy_step_plus_work_eq_initial f hres target x sigma
  iterate_energy_eq := by
    intro I _ f hres target x sigma n
    exact targetResidualEnergy_residualLaw_iterate_eq f hres target x sigma n
  iterate_work_ledger := by
    intro I _ f hres target x sigma n
    exact targetResidualEnergy_iterate_plus_work_eq_initial f hres target x sigma n

end AffineRelaxation
end SaturationMonoid

import H0mework.Computation.SelfReduction.P703
import H0mework.Realization.Residual.P721

/-!
# Proposition 722: Hamiltonian/SAT energy is the zero-target residual ledger

P721 proves that residual accounting forces a finite squared-residual energy
ledger on any real coordinate field.

P703 proves that the Hamiltonian-facing energy readout and SAT Lyapunov energy
readout on the finite phase-flow carrier are the same residual-square function.

This file welds those two faces.  The P703 shared energy is not merely another
copy of a squared-residual expression: it is exactly the target-zero
specialization of P721's forced residual-accounted energy ledger.  The P696/P703
one-step dissipation law is therefore inherited from the same target-general
equation that forced `relaxModule`, noisy-OR composition, cross-target
obstruction, and the work ledger.
-/

noncomputable section

namespace SaturationMonoid

namespace EnergyLedgerProjection

open scoped BigOperators
open AffineRelaxation
open ComplexityProjection

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v

/-! ## P696 as the zero-target face of P721 -/

/-- THEOREM 1: P696's finite residual energy is P721's target-residual energy
at target `0`. -/
theorem zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy
    {Clause : Type u} [Fintype Clause]
    (residual : Clause -> ℝ) :
    targetResidualEnergy (fun _ : Clause => 0) residual =
      phaseResidualEnergy residual := by
  classical
  dsimp [targetResidualEnergy, phaseResidualEnergy]
  congr 1
  ext c
  ring

/-- THEOREM 2: P696's residual relaxation step is exactly `relaxModule` toward
target `0` on the residual coordinate field. -/
theorem phaseResidualRelaxStep_eq_zeroTarget_relaxModule
    {Clause : Type u}
    (sigma : ℝ) (residual : Clause -> ℝ) :
    phaseResidualRelaxStep sigma residual =
      relaxModule (fun _ : Clause => 0) sigma residual := by
  funext c
  dsimp [phaseResidualRelaxStep, relaxModule]
  ring

/-- THEOREM 3: `relaxModule` on real coordinate fields satisfies the P719/P721
target residual law. -/
theorem relaxModule_function_targetResidualLaw
    {I : Type u} :
    TargetResidualLaw (K := ℝ) (E := I -> ℝ)
      (fun target sigma (x : I -> ℝ) => relaxModule target sigma x) := by
  intro target sigma x
  exact target_sub_relaxModule target sigma x

/-- THEOREM 4: P696's one-step residual energy law is an immediate
target-zero specialization of P721. -/
theorem phaseResidualEnergy_relax_eq_from_p721
    {Clause : Type u} [Fintype Clause]
    (sigma : ℝ) (residual : Clause -> ℝ) :
    phaseResidualEnergy (phaseResidualRelaxStep sigma residual) =
      (1 - sigma) ^ 2 * phaseResidualEnergy residual := by
  have hledger :=
    targetResidualEnergy_residualLaw_step_eq
      (fun target sigma (x : Clause -> ℝ) => relaxModule target sigma x)
      (relaxModule_function_targetResidualLaw (I := Clause))
      (fun _ : Clause => 0) residual sigma
  rw [← phaseResidualRelaxStep_eq_zeroTarget_relaxModule sigma residual] at hledger
  simpa [zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy]
    using hledger

/-- THEOREM 5: P696's finite-iterate residual energy law is an immediate
target-zero specialization of P721. -/
theorem phaseResidualEnergy_relax_iterate_eq_from_p721
    {Clause : Type u} [Fintype Clause]
    (sigma : ℝ) (n : ℕ) (residual : Clause -> ℝ) :
    phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) =
      ((1 - sigma) ^ 2) ^ n * phaseResidualEnergy residual := by
  classical
  have hfun :
      (fun y : Clause -> ℝ =>
          relaxModule (fun _ : Clause => 0) sigma y)^[n] residual =
        phaseResidualRelaxIterate sigma n residual := by
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih]
        exact (phaseResidualRelaxStep_eq_zeroTarget_relaxModule
          sigma (phaseResidualRelaxIterate sigma n residual)).symm
  have hledger :=
    targetResidualEnergy_residualLaw_iterate_eq
      (fun target sigma (x : Clause -> ℝ) => relaxModule target sigma x)
      (relaxModule_function_targetResidualLaw (I := Clause))
      (fun _ : Clause => 0) residual sigma n
  rw [hfun] at hledger
  simpa [zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy]
    using hledger

/-! ## P703 shared energy as the same zero-target ledger -/

/-- THEOREM 6: the Hamiltonian-facing readout is P721's target-zero residual
energy readout on the obstruction field. -/
theorem hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout S =
      targetResidualEnergy (fun _ : Clause => 0) S.obstruction := by
  rw [hamiltonianEnergyReadout]
  exact (zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy
    S.obstruction).symm

/-- THEOREM 7: the SAT-facing readout is the same P721 target-zero residual
energy readout. -/
theorem satEnergyReadout_eq_zeroTargetResidualEnergy
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    satEnergyReadout S =
      targetResidualEnergy (fun _ : Clause => 0) S.obstruction := by
  rw [satEnergyReadout, SATPhaseFlowState.energy]
  exact (zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy
    S.obstruction).symm

/-- THEOREM 8: the P703 Hamiltonian-energy one-step law is inherited from the
P721 target-zero energy ledger. -/
theorem hamiltonianEnergyReadout_dissipationStep_eq_from_p721
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout
        (phaseFlowDissipationStep sigma dt direction S) =
      (1 - sigma) ^ 2 * hamiltonianEnergyReadout S := by
  rw [hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy
      (phaseFlowDissipationStep sigma dt direction S),
    hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy S]
  dsimp [phaseFlowDissipationStep]
  simpa [zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy]
    using phaseResidualEnergy_relax_eq_from_p721 sigma S.obstruction

/-- THEOREM 9: the P703 Hamiltonian-energy finite-iterate law is inherited
from the P721 target-zero energy ledger. -/
theorem hamiltonianEnergyReadout_dissipationIterate_eq_from_p721
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout
        (phaseFlowDissipationIterate sigma dt direction n S) =
      ((1 - sigma) ^ 2) ^ n * hamiltonianEnergyReadout S := by
  rw [hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy
      (phaseFlowDissipationIterate sigma dt direction n S),
    hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy S]
  have hobstruction :
      (phaseFlowDissipationIterate sigma dt direction n S).obstruction =
        phaseResidualRelaxIterate sigma n S.obstruction := by
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        simp only [phaseFlowDissipationIterate, phaseResidualRelaxIterate]
        change
          phaseResidualRelaxStep sigma
              (phaseFlowDissipationIterate sigma dt direction n S).obstruction =
            phaseResidualRelaxStep sigma
              (phaseResidualRelaxIterate sigma n S.obstruction)
        rw [ih]
  rw [hobstruction]
  simpa [zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy]
    using phaseResidualEnergy_relax_iterate_eq_from_p721
      sigma n S.obstruction

/-! ## Certificate -/

/-- P722 certificate: P696/P703 shared energy is exactly P721's zero-target
residual-accounted energy ledger. -/
structure HamiltonianSATEnergyFromResidualLedgerCertificate : Prop where
  phase_energy_is_zero_target_ledger :
    ∀ {Clause : Type u} [Fintype Clause]
      (residual : Clause -> ℝ),
      targetResidualEnergy (fun _ : Clause => 0) residual =
        phaseResidualEnergy residual
  phase_relax_is_zero_target_relaxModule :
    ∀ {Clause : Type u}
      (sigma : ℝ) (residual : Clause -> ℝ),
      phaseResidualRelaxStep sigma residual =
        relaxModule (fun _ : Clause => 0) sigma residual
  phase_step_energy_from_p721 :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (residual : Clause -> ℝ),
      phaseResidualEnergy (phaseResidualRelaxStep sigma residual) =
        (1 - sigma) ^ 2 * phaseResidualEnergy residual
  phase_iterate_energy_from_p721 :
    ∀ {Clause : Type u} [Fintype Clause]
      (sigma : ℝ) (n : ℕ) (residual : Clause -> ℝ),
      phaseResidualEnergy (phaseResidualRelaxIterate sigma n residual) =
        ((1 - sigma) ^ 2) ^ n * phaseResidualEnergy residual
  hamiltonian_energy_is_zero_target_ledger :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout S =
        targetResidualEnergy (fun _ : Clause => 0) S.obstruction
  sat_energy_is_zero_target_ledger :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      satEnergyReadout S =
        targetResidualEnergy (fun _ : Clause => 0) S.obstruction
  hamiltonian_step_energy_from_p721 :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout
          (phaseFlowDissipationStep sigma dt direction S) =
        (1 - sigma) ^ 2 * hamiltonianEnergyReadout S
  hamiltonian_iterate_energy_from_p721 :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (n : ℕ)
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout
          (phaseFlowDissipationIterate sigma dt direction n S) =
        ((1 - sigma) ^ 2) ^ n * hamiltonianEnergyReadout S

/-- THEOREM 10: the Hamiltonian/SAT energy readout is supplied by the P721
zero-target residual ledger. -/
theorem residualLedgerHamiltonianSATEnergyCertificate :
    HamiltonianSATEnergyFromResidualLedgerCertificate where
  phase_energy_is_zero_target_ledger := by
    intro Clause _ residual
    exact zeroTarget_targetResidualEnergy_eq_phaseResidualEnergy residual
  phase_relax_is_zero_target_relaxModule := by
    intro Clause sigma residual
    exact phaseResidualRelaxStep_eq_zeroTarget_relaxModule sigma residual
  phase_step_energy_from_p721 := by
    intro Clause _ sigma residual
    exact phaseResidualEnergy_relax_eq_from_p721 sigma residual
  phase_iterate_energy_from_p721 := by
    intro Clause _ sigma n residual
    exact phaseResidualEnergy_relax_iterate_eq_from_p721 sigma n residual
  hamiltonian_energy_is_zero_target_ledger := by
    intro Clause Var _ S
    exact hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy S
  sat_energy_is_zero_target_ledger := by
    intro Clause Var _ S
    exact satEnergyReadout_eq_zeroTargetResidualEnergy S
  hamiltonian_step_energy_from_p721 := by
    intro Clause Var _ sigma dt direction S
    exact hamiltonianEnergyReadout_dissipationStep_eq_from_p721
      sigma dt direction S
  hamiltonian_iterate_energy_from_p721 := by
    intro Clause Var _ sigma dt direction n S
    exact hamiltonianEnergyReadout_dissipationIterate_eq_from_p721
      sigma dt direction n S

end EnergyLedgerProjection
end SaturationMonoid

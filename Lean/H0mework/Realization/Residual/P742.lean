import H0mework.Computation.Phase.P722
import H0mework.Realization.RelaxationAlgebra.P741

/-!
# Proposition 742: six-face residual processes force one energy ledger

P741 proves that independently supplied structural updates on the six
grand-unification faces all factor through the same noisy-OR residual-process
monoid.  P721/P722 prove that residual accounting uniquely induces the finite
squared-residual energy ledger, and that the Hamiltonian/SAT energy readout is
the zero-target face of that ledger.

This file welds the two directions.  Once a face-local update is accepted by
the structural laws of P733/P741, its finite-coordinate action automatically
inherits the P721 energy ledger.  On the zero-target residual field this is
exactly the P722/P703 Hamiltonian/SAT energy readout.  Thus the words

`information / energy / matter / mathematics / consciousness / physics`

do not carry separate energy notions: their accepted same-target actions share
one residual-energy ledger, and cross-face composition dissipates energy through
the same noisy-OR rate.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open scoped BigOperators
open ComplexityProjection
open EnergyLedgerProjection

universe u v w

/-! ## Face-local vector action -/

/-- Coordinatewise action of a face-local structural update on a finite real
field. -/
def faceLocalVectorUpdate
    {Face : Type u} {I : Type v}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (target : I -> ℝ) (sigma : ℝ) (x : I -> ℝ) : I -> ℝ :=
  fun i => F.update face (target i) sigma (x i)

/-- THEOREM 1: the coordinatewise face-local action is exactly `relaxModule`
on the finite real field. -/
theorem faceLocalVectorUpdate_eq_relaxModule
    {Face : Type u} {I : Type v}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (target : I -> ℝ) (sigma : ℝ) (x : I -> ℝ) :
    faceLocalVectorUpdate F face target sigma x =
      relaxModule target sigma x := by
  funext i
  dsimp [faceLocalVectorUpdate]
  rw [faceLocal_update_eq_relaxTo F face]
  dsimp [relaxTo, relaxModule]

/-- THEOREM 2: every coordinatewise face-local action satisfies the target
residual law. -/
theorem faceLocalVectorUpdate_targetResidualLaw
    {Face : Type u} {I : Type v}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face) :
    TargetResidualLaw (K := ℝ) (E := I -> ℝ)
      (fun target sigma x => faceLocalVectorUpdate F face target sigma x) := by
  intro target sigma x
  change target - faceLocalVectorUpdate F face target sigma x =
    (1 - sigma) • (target - x)
  rw [faceLocalVectorUpdate_eq_relaxModule F face target sigma x]
  exact target_sub_relaxModule target sigma x

/-! ## Forced finite energy ledger for every face -/

/-- THEOREM 3: one accepted face-local update multiplies target-residual energy
by `(1-sigma)^2`. -/
theorem faceLocal_targetResidualEnergy_step_eq
    {Face : Type u} {I : Type v} [Fintype I]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (target x : I -> ℝ) (sigma : ℝ) :
    targetResidualEnergy target (faceLocalVectorUpdate F face target sigma x) =
      (1 - sigma) ^ 2 * targetResidualEnergy target x := by
  exact
    targetResidualEnergy_residualLaw_step_eq
      (fun target sigma (x : I -> ℝ) =>
        faceLocalVectorUpdate F face target sigma x)
      (faceLocalVectorUpdate_targetResidualLaw F face)
      target x sigma

/-- THEOREM 4: one accepted face-local update has the forced work ledger. -/
theorem faceLocal_targetResidualEnergy_step_plus_work_eq_initial
    {Face : Type u} {I : Type v} [Fintype I]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (target x : I -> ℝ) (sigma : ℝ) :
    targetResidualEnergy target (faceLocalVectorUpdate F face target sigma x) +
        targetResidualWork target x sigma =
      targetResidualEnergy target x := by
  exact
    targetResidualEnergy_step_plus_work_eq_initial
      (fun target sigma (x : I -> ℝ) =>
        faceLocalVectorUpdate F face target sigma x)
      (faceLocalVectorUpdate_targetResidualLaw F face)
      target x sigma

/-- THEOREM 5: cross-face same-target composition dissipates the same energy
as one step at the noisy-OR rate. -/
theorem faceLocal_crossFace_targetResidualEnergy_eq
    {Face : Type u} {I : Type v} [Fintype I]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₂ face₁ face₃ : Face)
    (target x : I -> ℝ) (sigma1 sigma2 : ℝ) :
    targetResidualEnergy target
        (faceLocalVectorUpdate F face₂ target sigma2
          (faceLocalVectorUpdate F face₁ target sigma1 x)) =
      (1 - satOrField sigma1 sigma2) ^ 2 *
        targetResidualEnergy target x := by
  have hcompose :
      faceLocalVectorUpdate F face₂ target sigma2
          (faceLocalVectorUpdate F face₁ target sigma1 x) =
        faceLocalVectorUpdate F face₃ target
          (satOrField sigma1 sigma2) x := by
    funext i
    exact faceLocal_crossFace_sameTarget_compose
      F face₂ face₁ face₃ (target i) (x i) sigma1 sigma2
  rw [hcompose]
  exact faceLocal_targetResidualEnergy_step_eq
    F face₃ target x (satOrField sigma1 sigma2)

/-- THEOREM 6: cross-face same-target composition has the forced noisy-OR work
ledger. -/
theorem faceLocal_crossFace_energy_plus_work_eq_initial
    {Face : Type u} {I : Type v} [Fintype I]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₂ face₁ face₃ : Face)
    (target x : I -> ℝ) (sigma1 sigma2 : ℝ) :
    targetResidualEnergy target
        (faceLocalVectorUpdate F face₂ target sigma2
          (faceLocalVectorUpdate F face₁ target sigma1 x)) +
        targetResidualWork target x (satOrField sigma1 sigma2) =
      targetResidualEnergy target x := by
  have hcompose :
      faceLocalVectorUpdate F face₂ target sigma2
          (faceLocalVectorUpdate F face₁ target sigma1 x) =
        faceLocalVectorUpdate F face₃ target
          (satOrField sigma1 sigma2) x := by
    funext i
    exact faceLocal_crossFace_sameTarget_compose
      F face₂ face₁ face₃ (target i) (x i) sigma1 sigma2
  rw [hcompose]
  exact faceLocal_targetResidualEnergy_step_plus_work_eq_initial
    F face₃ target x (satOrField sigma1 sigma2)

/-! ## Hamiltonian/SAT zero-target face -/

/-- The zero-target residual step induced by a face-local structural update. -/
def faceLocalPhaseResidualStep
    {Face : Type u} {Clause : Type v}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (sigma : ℝ) (residual : Clause -> ℝ) : Clause -> ℝ :=
  faceLocalVectorUpdate F face (fun _ : Clause => 0) sigma residual

/-- THEOREM 7: the zero-target face-local residual step is exactly the
certified SAT/Hamiltonian residual relaxation step. -/
theorem faceLocalPhaseResidualStep_eq_phaseResidualRelaxStep
    {Face : Type u} {Clause : Type v}
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (sigma : ℝ) (residual : Clause -> ℝ) :
    faceLocalPhaseResidualStep F face sigma residual =
      phaseResidualRelaxStep sigma residual := by
  rw [faceLocalPhaseResidualStep]
  rw [faceLocalVectorUpdate_eq_relaxModule F face
    (fun _ : Clause => 0) sigma residual]
  exact (phaseResidualRelaxStep_eq_zeroTarget_relaxModule
    sigma residual).symm

/-- THEOREM 8: every accepted face-local zero-target residual step dissipates
the Hamiltonian/SAT residual energy by `(1-sigma)^2`. -/
theorem faceLocalPhaseResidualEnergy_step_eq
    {Face : Type u} {Clause : Type v} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (sigma : ℝ) (residual : Clause -> ℝ) :
    phaseResidualEnergy
        (faceLocalPhaseResidualStep F face sigma residual) =
      (1 - sigma) ^ 2 * phaseResidualEnergy residual := by
  rw [faceLocalPhaseResidualStep_eq_phaseResidualRelaxStep]
  exact phaseResidualEnergy_relax_eq_from_p721 sigma residual

/-- The Hamiltonian/SAT carrier step obtained by using a face-local structural
update only on the obstruction residuals. -/
def faceLocalHamiltonianSATResidualStep
    {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (sigma : ℝ)
    (S : SATPhaseFlowState Clause Var) :
    SATPhaseFlowState Clause Var where
  theta := S.theta
  obstruction := faceLocalPhaseResidualStep F face sigma S.obstruction

/-- THEOREM 9: a face-local residual step on the Hamiltonian/SAT shared carrier
dissipates the shared readout by `(1-sigma)^2`. -/
theorem faceLocalHamiltonianSAT_energy_step_eq
    {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (sigma : ℝ)
    (S : SATPhaseFlowState Clause Var) :
    hamiltonianEnergyReadout
        (faceLocalHamiltonianSATResidualStep F face sigma S) =
      (1 - sigma) ^ 2 * hamiltonianEnergyReadout S := by
  dsimp [hamiltonianEnergyReadout,
    faceLocalHamiltonianSATResidualStep]
  exact faceLocalPhaseResidualEnergy_step_eq F face sigma S.obstruction

/-- THEOREM 10: two cross-face Hamiltonian/SAT residual steps dissipate exactly
as one step at the noisy-OR rate. -/
theorem faceLocalHamiltonianSAT_crossFace_energy_eq
    {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₂ face₁ face₃ : Face)
    (sigma1 sigma2 : ℝ)
    (S : SATPhaseFlowState Clause Var) :
    hamiltonianEnergyReadout
        (faceLocalHamiltonianSATResidualStep F face₂ sigma2
          (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)) =
      (1 - satOrField sigma1 sigma2) ^ 2 *
        hamiltonianEnergyReadout S := by
  have hobs :
      (faceLocalHamiltonianSATResidualStep F face₂ sigma2
          (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)).obstruction =
        faceLocalVectorUpdate F face₃ (fun _ : Clause => 0)
          (satOrField sigma1 sigma2) S.obstruction := by
    funext c
    exact faceLocal_crossFace_sameTarget_compose
      F face₂ face₁ face₃ 0 (S.obstruction c) sigma1 sigma2
  dsimp [hamiltonianEnergyReadout]
  rw [hobs]
  exact faceLocalPhaseResidualEnergy_step_eq
    F face₃ (satOrField sigma1 sigma2) S.obstruction

/-! ## Packaged certificate -/

/-- P742 certificate: six-face accepted structural updates inherit one forced
finite residual-energy ledger, whose zero-target face is the Hamiltonian/SAT
energy ledger. -/
structure SixFaceResidualProcessEnergyLedgerCertificate : Prop where
  six_face_process_monoid :
    SixFaceStructuralUpdateProcessMonoidCertificate.{u}
  residual_energy_ledger :
    ResidualAccountedEnergyLedgerCertificate.{v, v, v, v, v, v, v}
  hamiltonian_sat_energy_from_ledger :
    EnergyLedgerProjection.HamiltonianSATEnergyFromResidualLedgerCertificate.{v, w}
  face_vector_is_relaxModule :
    ∀ {Face : Type u} {I : Type v}
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face : Face)
      (target : I -> ℝ) (sigma : ℝ) (x : I -> ℝ),
        faceLocalVectorUpdate F face target sigma x =
          relaxModule target sigma x
  face_energy_step :
    ∀ {Face : Type u} {I : Type v} [Fintype I]
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face : Face)
      (target x : I -> ℝ) (sigma : ℝ),
        targetResidualEnergy target
            (faceLocalVectorUpdate F face target sigma x) =
          (1 - sigma) ^ 2 * targetResidualEnergy target x
  cross_face_energy_step :
    ∀ {Face : Type u} {I : Type v} [Fintype I]
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face₂ face₁ _face₃ : Face)
      (target x : I -> ℝ) (sigma1 sigma2 : ℝ),
        targetResidualEnergy target
            (faceLocalVectorUpdate F face₂ target sigma2
              (faceLocalVectorUpdate F face₁ target sigma1 x)) =
          (1 - satOrField sigma1 sigma2) ^ 2 *
            targetResidualEnergy target x
  cross_face_work_ledger :
    ∀ {Face : Type u} {I : Type v} [Fintype I]
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face₂ face₁ _face₃ : Face)
      (target x : I -> ℝ) (sigma1 sigma2 : ℝ),
        targetResidualEnergy target
            (faceLocalVectorUpdate F face₂ target sigma2
              (faceLocalVectorUpdate F face₁ target sigma1 x)) +
            targetResidualWork target x (satOrField sigma1 sigma2) =
          targetResidualEnergy target x
  face_phase_residual_is_certified_relax :
    ∀ {Face : Type u} {Clause : Type v}
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face : Face)
      (sigma : ℝ) (residual : Clause -> ℝ),
        faceLocalPhaseResidualStep F face sigma residual =
          phaseResidualRelaxStep sigma residual
  face_hamiltonian_sat_energy_step :
    ∀ {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face : Face)
      (sigma : ℝ)
      (S : SATPhaseFlowState Clause Var),
        hamiltonianEnergyReadout
            (faceLocalHamiltonianSATResidualStep F face sigma S) =
          (1 - sigma) ^ 2 * hamiltonianEnergyReadout S
  cross_face_hamiltonian_sat_energy_step :
    ∀ {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
      (F : FaceLocalStructuralUpdateObserverFamily Face)
      (face₂ face₁ _face₃ : Face)
      (sigma1 sigma2 : ℝ)
      (S : SATPhaseFlowState Clause Var),
        hamiltonianEnergyReadout
            (faceLocalHamiltonianSATResidualStep F face₂ sigma2
              (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)) =
          (1 - satOrField sigma1 sigma2) ^ 2 *
            hamiltonianEnergyReadout S

/-- THEOREM 11: six-face residual processes force the shared energy ledger. -/
theorem sixFaceResidualProcessEnergyLedgerCertificate :
    SixFaceResidualProcessEnergyLedgerCertificate where
  six_face_process_monoid := sixFaceStructuralUpdateProcessMonoidCertificate
  residual_energy_ledger := residualAccountedEnergyLedgerCertificate
  hamiltonian_sat_energy_from_ledger :=
    EnergyLedgerProjection.residualLedgerHamiltonianSATEnergyCertificate
  face_vector_is_relaxModule := by
    intro Face I F face target sigma x
    exact faceLocalVectorUpdate_eq_relaxModule F face target sigma x
  face_energy_step := by
    intro Face I _ F face target x sigma
    exact faceLocal_targetResidualEnergy_step_eq F face target x sigma
  cross_face_energy_step := by
    intro Face I _ F face₂ face₁ face₃ target x sigma1 sigma2
    exact faceLocal_crossFace_targetResidualEnergy_eq
      F face₂ face₁ face₃ target x sigma1 sigma2
  cross_face_work_ledger := by
    intro Face I _ F face₂ face₁ face₃ target x sigma1 sigma2
    exact faceLocal_crossFace_energy_plus_work_eq_initial
      F face₂ face₁ face₃ target x sigma1 sigma2
  face_phase_residual_is_certified_relax := by
    intro Face Clause F face sigma residual
    exact faceLocalPhaseResidualStep_eq_phaseResidualRelaxStep
      F face sigma residual
  face_hamiltonian_sat_energy_step := by
    intro Face Clause Var _ F face sigma S
    exact faceLocalHamiltonianSAT_energy_step_eq F face sigma S
  cross_face_hamiltonian_sat_energy_step := by
    intro Face Clause Var _ F face₂ face₁ face₃ sigma1 sigma2 S
    exact faceLocalHamiltonianSAT_crossFace_energy_eq
      F face₂ face₁ face₃ sigma1 sigma2 S

end AffineRelaxation
end SaturationMonoid

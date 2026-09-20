import H0mework.Realization.Residual.P742

/-!
# Proposition 743: the residual split is the first formula

P741/P742 show that accepted six-face processes share one noisy-OR action and
one squared-residual energy ledger.  This file pushes one layer lower.

The primitive equation is not first the affine display

`x ↦ x + sigma • (target - x)`,

nor first the transport display

`r ↦ (1-sigma) • r`.

It is the conserved split of one residual into what remains and what has become
trace:

`r = (1-sigma) • r + sigma • r`.

Everything else is a reading of that split:

* residual transport is the keep side;
* affine relaxation is the trace side in state coordinates;
* noisy-OR is the composition law of repeated keep/trace splits;
* Hamiltonian/SAT energy is the squared zero-target reading of the same split.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open scoped BigOperators
open ComplexityProjection

universe u v w

/-! ## The primitive keep/trace split -/

/-- The part of a residual kept after a rate-`sigma` process. -/
def residualKeep
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) : E :=
  (1 - sigma) • r

/-- The part of a residual spent into trace by a rate-`sigma` process. -/
def residualTrace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) : E :=
  sigma • r

/-- THEOREM 1: first formula, orientation `keep + trace = residual`. -/
theorem residualKeep_add_residualTrace_eq
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    residualKeep sigma r + residualTrace sigma r = r := by
  dsimp [residualKeep, residualTrace]
  rw [← add_smul]
  simp

/-- THEOREM 2: first formula, orientation `residual = keep + trace`. -/
theorem residual_eq_keep_add_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    r = residualKeep sigma r + residualTrace sigma r :=
  (residualKeep_add_residualTrace_eq sigma r).symm

/-! ## Transport and affine readings -/

/-- THEOREM 3: residual transport is the keep reading of the split. -/
theorem residualTransport_is_keep
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    target - relaxModule target sigma x =
      residualKeep sigma (target - x) := by
  rw [target_sub_relaxModule]
  rfl

/-- THEOREM 4: affine motion is the trace reading of the split. -/
theorem affineDelta_is_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    relaxModule target sigma x - x =
      residualTrace sigma (target - x) := by
  dsimp [relaxModule, residualTrace]
  module

/-- THEOREM 5: the affine update is state plus trace. -/
theorem relaxModule_eq_state_plus_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    relaxModule target sigma x =
      x + residualTrace sigma (target - x) := by
  rfl

/-- THEOREM 6: the state display is target minus the kept residual. -/
theorem relaxModule_eq_target_sub_keep
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    relaxModule target sigma x =
      target - residualKeep sigma (target - x) := by
  dsimp [relaxModule, residualKeep]
  module

/-! ## Composition reading -/

/-- THEOREM 7: repeated keeps compose by the noisy-OR rate. -/
theorem residualKeep_compose
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma1 sigma2 : K) (r : E) :
    residualKeep sigma2 (residualKeep sigma1 r) =
      residualKeep (satOrField sigma1 sigma2) r := by
  dsimp [residualKeep, satOrField]
  module

/-- THEOREM 8: the trace spent across two steps is the trace spent by the
single noisy-OR composite rate. -/
theorem residualTrace_twoStep_eq_satOr_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma1 sigma2 : K) (r : E) :
    residualTrace sigma1 r +
        residualTrace sigma2 (residualKeep sigma1 r) =
      residualTrace (satOrField sigma1 sigma2) r := by
  dsimp [residualTrace, residualKeep, satOrField]
  module

/-- THEOREM 9: two-step keep plus two-step trace still exhausts the original
residual. -/
theorem residual_twoStep_split_conserved
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma1 sigma2 : K) (r : E) :
    residualKeep sigma2 (residualKeep sigma1 r) +
        (residualTrace sigma1 r +
          residualTrace sigma2 (residualKeep sigma1 r)) =
      r := by
  rw [residualKeep_compose, residualTrace_twoStep_eq_satOr_trace]
  exact residualKeep_add_residualTrace_eq (satOrField sigma1 sigma2) r

/-! ## Energy reading -/

/-- THEOREM 10: the finite energy/work ledger is the squared reading of the
one-step residual split. -/
theorem residualSplit_targetResidualEnergy_ledger
    {I : Type u} [Fintype I]
    (target x : I -> ℝ) (sigma : ℝ) :
    targetResidualEnergy target (relaxModule target sigma x) +
        targetResidualWork target x sigma =
      targetResidualEnergy target x := by
  exact
    targetResidualEnergy_step_plus_work_eq_initial
      (fun target sigma (x : I -> ℝ) => relaxModule target sigma x)
      (fun target sigma x => target_sub_relaxModule target sigma x)
      target x sigma

/-- Work readout for the Hamiltonian/SAT zero-target face. -/
def hamiltonianSATResidualWork
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : SATPhaseFlowState Clause Var) (sigma : ℝ) : ℝ :=
  (1 - (1 - sigma) ^ 2) * hamiltonianEnergyReadout S

/-- THEOREM 11: the Hamiltonian/SAT face has the same keep/spent energy split. -/
theorem faceLocalHamiltonianSAT_energy_split_ledger
    {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face : Face)
    (sigma : ℝ)
    (S : SATPhaseFlowState Clause Var) :
    hamiltonianEnergyReadout
        (faceLocalHamiltonianSATResidualStep F face sigma S) +
        hamiltonianSATResidualWork S sigma =
      hamiltonianEnergyReadout S := by
  rw [faceLocalHamiltonianSAT_energy_step_eq F face sigma S]
  dsimp [hamiltonianSATResidualWork]
  ring

/-- THEOREM 12: two cross-face Hamiltonian/SAT residual steps have the same
noisy-OR keep/spent energy split. -/
theorem faceLocalHamiltonianSAT_crossFace_energy_split_ledger
    {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause]
    (F : FaceLocalStructuralUpdateObserverFamily Face)
    (face₂ face₁ face₃ : Face)
    (sigma1 sigma2 : ℝ)
    (S : SATPhaseFlowState Clause Var) :
    hamiltonianEnergyReadout
        (faceLocalHamiltonianSATResidualStep F face₂ sigma2
          (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)) +
        hamiltonianSATResidualWork S (satOrField sigma1 sigma2) =
      hamiltonianEnergyReadout S := by
  rw [faceLocalHamiltonianSAT_crossFace_energy_eq
    F face₂ face₁ face₃ sigma1 sigma2 S]
  dsimp [hamiltonianSATResidualWork]
  ring

/-! ## Packaged certificate -/

/-- P743 certificate: the residual split is the first formula, and the
transport, affine, composition, and Hamiltonian/SAT energy displays are its
readings. -/
structure ResidualSplitFirstFormulaCertificate : Prop where
  residual_split_conserved :
    ∀ {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E],
      ∀ sigma : K, ∀ r : E,
        r = residualKeep sigma r + residualTrace sigma r
  residual_transport_reading :
    ∀ {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E],
      ∀ target : E, ∀ sigma : K, ∀ x : E,
        target - relaxModule target sigma x =
          residualKeep sigma (target - x)
  affine_trace_reading :
    ∀ {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E],
      ∀ target : E, ∀ sigma : K, ∀ x : E,
        relaxModule target sigma x - x =
          residualTrace sigma (target - x)
  same_target_composition_reading :
    ∀ {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E],
      ∀ sigma1 sigma2 : K, ∀ r : E,
        residualKeep sigma2 (residualKeep sigma1 r) =
          residualKeep (satOrField sigma1 sigma2) r
  two_step_trace_reading :
    ∀ {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E],
      ∀ sigma1 sigma2 : K, ∀ r : E,
        residualTrace sigma1 r +
            residualTrace sigma2 (residualKeep sigma1 r) =
          residualTrace (satOrField sigma1 sigma2) r
  finite_energy_split_reading :
    ∀ {I : Type u} [Fintype I],
      ∀ target x : I -> ℝ, ∀ sigma : ℝ,
        targetResidualEnergy target (relaxModule target sigma x) +
            targetResidualWork target x sigma =
          targetResidualEnergy target x
  hamiltonian_sat_energy_split_reading :
    ∀ {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause],
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face : Face, ∀ sigma : ℝ,
          ∀ S : SATPhaseFlowState Clause Var,
            hamiltonianEnergyReadout
                (faceLocalHamiltonianSATResidualStep F face sigma S) +
                hamiltonianSATResidualWork S sigma =
              hamiltonianEnergyReadout S
  hamiltonian_sat_cross_face_energy_split_reading :
    ∀ {Face : Type u} {Clause : Type v} {Var : Type w} [Fintype Clause],
      ∀ F : FaceLocalStructuralUpdateObserverFamily Face,
        ∀ face₂ face₁ _face₃ : Face, ∀ sigma1 sigma2 : ℝ,
          ∀ S : SATPhaseFlowState Clause Var,
            hamiltonianEnergyReadout
                (faceLocalHamiltonianSATResidualStep F face₂ sigma2
                  (faceLocalHamiltonianSATResidualStep F face₁ sigma1 S)) +
                hamiltonianSATResidualWork S (satOrField sigma1 sigma2) =
              hamiltonianEnergyReadout S
  six_face_energy_ledger :
    SixFaceResidualProcessEnergyLedgerCertificate.{u, v, w}

/-- THEOREM 13: the first-formula residual split certificate. -/
theorem residualSplitFirstFormulaCertificate :
    ResidualSplitFirstFormulaCertificate where
  residual_split_conserved := by
    intro K E _ _ _ sigma r
    exact residual_eq_keep_add_trace sigma r
  residual_transport_reading := by
    intro K E _ _ _ target sigma x
    exact residualTransport_is_keep target sigma x
  affine_trace_reading := by
    intro K E _ _ _ target sigma x
    exact affineDelta_is_trace target sigma x
  same_target_composition_reading := by
    intro K E _ _ _ sigma1 sigma2 r
    exact residualKeep_compose sigma1 sigma2 r
  two_step_trace_reading := by
    intro K E _ _ _ sigma1 sigma2 r
    exact residualTrace_twoStep_eq_satOr_trace sigma1 sigma2 r
  finite_energy_split_reading := by
    intro I _ target x sigma
    exact residualSplit_targetResidualEnergy_ledger target x sigma
  hamiltonian_sat_energy_split_reading := by
    intro Face Clause Var _ F face sigma S
    exact faceLocalHamiltonianSAT_energy_split_ledger F face sigma S
  hamiltonian_sat_cross_face_energy_split_reading := by
    intro Face Clause Var _ F face₂ face₁ face₃ sigma1 sigma2 S
    exact faceLocalHamiltonianSAT_crossFace_energy_split_ledger
      F face₂ face₁ face₃ sigma1 sigma2 S
  six_face_energy_ledger :=
    sixFaceResidualProcessEnergyLedgerCertificate

end AffineRelaxation
end SaturationMonoid

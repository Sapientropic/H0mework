import H0mework.Chemistry.LAlanineThermalDynamics.SharedFrameCovariance

/-! # The finite controller couples to source energy differences, without spectral enumeration -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Source

open Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def controllerHamiltonian : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 2]

def lowering : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 1

theorem lowering_energy_gap : controllerHamiltonian * lowering - lowering * controllerHamiltonian =
    (-2 : ℂ) • lowering := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerHamiltonian, lowering, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.single_apply]

def bare (H : SystemMatrix ι) : Matrix ((ι × ι) × Fin 2) ((ι × ι) × Fin 2) ℂ :=
  Matrix.kronecker (pairHamiltonian H) 1 + Matrix.kronecker 1 controllerHamiltonian

def transfer (H : SystemMatrix ι) : Matrix ((ι × ι) × Fin 2) ((ι × ι) × Fin 2) ℂ :=
  Matrix.kronecker (raising H) lowering

def interaction (H : SystemMatrix ι) : Matrix ((ι × ι) × Fin 2) ((ι × ι) × Fin 2) ℂ :=
  transfer H + (transfer H)ᴴ

theorem bare_commutes_transfer (H : SystemMatrix ι) : Commute (bare H) (transfer H) := by
  have expansion : bare H * transfer H - transfer H * bare H =
      Matrix.kronecker (pairHamiltonian H * raising H - raising H * pairHamiltonian H) lowering +
      Matrix.kronecker (raising H) (controllerHamiltonian * lowering - lowering * controllerHamiltonian) := by
    simp only [bare, transfer, add_mul, mul_add, Matrix.kronecker,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  rw [raising_energy_gap, lowering_energy_gap] at expansion
  have zero : bare H * transfer H - transfer H * bare H = 0 := by
    rw [expansion]
    simp only [Matrix.kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul]
    module
  exact sub_eq_zero.mp zero

omit [Fintype ι] in
theorem pairHamiltonian_hermitian (H : SystemMatrix ι) (hH : H.IsHermitian) :
    (pairHamiltonian H).IsHermitian := pairH_hermitian H hH 1

omit [Fintype ι] in
theorem bare_hermitian (H : SystemMatrix ι) (hH : H.IsHermitian) : (bare H).IsHermitian := by
  change (bare H)ᴴ = bare H
  simp only [bare, Matrix.conjTranspose_add, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    (pairHamiltonian_hermitian H hH).eq, Matrix.conjTranspose_one]
  have controller : controllerHamiltonianᴴ = controllerHamiltonian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [controllerHamiltonian]
  rw [controller]

theorem bare_commutes_interaction (H : SystemMatrix ι) (hH : H.IsHermitian) :
    Commute (bare H) (interaction H) := by
  have transferCommutes := bare_commutes_transfer H
  have adjointCommutes := transferCommutes.star_star
  change Commute (bare H)ᴴ (transfer H)ᴴ at adjointCommutes
  rw [(bare_hermitian H hH).eq] at adjointCommutes
  exact transferCommutes.add_right adjointCommutes

theorem interaction_hermitian (H : SystemMatrix ι) : (interaction H).IsHermitian := by
  change (interaction H)ᴴ = interaction H
  simp [interaction, add_comm]

theorem interaction_nonzero (H : SystemMatrix ι) (nonzero : raising H ≠ 0) : interaction H ≠ 0 := by
  intro zero
  apply nonzero
  ext i j
  have entry := congrArg (fun A => A (i, 0) (j, 1)) zero
  simpa [interaction, transfer, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, lowering, Matrix.single_apply] using entry

def controllerFrame (U : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup ((ι × ι) × Fin 2) ℂ :=
  ⟨Matrix.kronecker (Quantum.localUnitary U U : JointMatrix ι) (1 : Matrix (Fin 2) (Fin 2) ℂ),
    Matrix.kronecker_mem_unitary (Quantum.localUnitary U U).property (one_mem _)⟩

theorem shared_conjugation_transfer (U : Matrix.unitaryGroup ι ℂ) (H : SystemMatrix ι) :
    Unitary.conjStarAlgAut ℂ _ (controllerFrame U) (transfer H) = transfer (Quantum.conjugation U H) := by
  rw [Unitary.conjStarAlgAut_apply]
  change Matrix.kronecker (Quantum.localUnitary U U : JointMatrix ι) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.kronecker (raising H) lowering *
      (Matrix.kronecker (Quantum.localUnitary U U : JointMatrix ι) (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = _
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  change Matrix.kronecker (Quantum.localConjugation U U (raising H)) lowering = _
  rw [shared_conjugation_raising]
  rfl

theorem shared_conjugation_interaction (U : Matrix.unitaryGroup ι ℂ) (H : SystemMatrix ι) :
    Unitary.conjStarAlgAut ℂ _ (controllerFrame U) (interaction H) = interaction (Quantum.conjugation U H) := by
  dsimp only [interaction]
  rw [map_add]
  have adjoint := map_star
    (Unitary.conjStarAlgAut ℂ (Matrix ((ι × ι) × Fin 2) ((ι × ι) × Fin 2) ℂ) (controllerFrame U))
    (transfer H)
  have same := shared_conjugation_transfer U H
  exact congrArg₂ (fun A B : Matrix ((ι × ι) × Fin 2) ((ι × ι) × Fin 2) ℂ => A + B)
    same (adjoint.trans (congrArg star same))

end

end LAlanine40K2025.Thermal.Powered.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

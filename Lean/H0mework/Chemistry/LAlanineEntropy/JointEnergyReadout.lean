import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation
import Mathlib.Data.Matrix.Basis

/-! # Bare pair energy and both reduced energy reads share one arbitrary joint state -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem tensor_energy_read (H A B : SystemMatrix ι) :
    (jointHamiltonian H * Matrix.kronecker A B).trace =
      (H * systemReduce (Matrix.kronecker A B)).trace +
        (H * bathReduce (Matrix.kronecker A B)).trace := by
  simp only [jointHamiltonian, Matrix.add_mul, Matrix.trace_add,
    systemReduce_tensor, bathReduce_tensor, mul_smul_comm, Matrix.trace_smul]
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, Matrix.trace_kronecker, Matrix.trace_kronecker]
  simp only [smul_eq_mul]
  ring

theorem jointEnergy_eq_reduced (H : SystemMatrix ι) (joint : JointMatrix ι) :
    (jointHamiltonian H * joint).trace =
      (H * systemReduce joint).trace + (H * bathReduce joint).trace := by
  rw [Matrix.matrix_eq_sum_single joint]
  simp only [Matrix.mul_sum, Matrix.trace_sum, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨j, b⟩ _
  have tensor : Matrix.single (i, a) (j, b) (joint (i, a) (j, b)) =
      Matrix.kronecker (Matrix.single i j (joint (i, a) (j, b))) (Matrix.single a b 1) :=
    (Matrix.single_kronecker_single i j a b (joint (i, a) (j, b)) (1 : ℂ)).trans
      (by rw [mul_one]) |>.symm
  rw [tensor]
  exact tensor_energy_read H _ _

theorem jointEnergy_real_eq_reduced (H : SystemMatrix ι) (joint : JointMatrix ι) :
    energy (jointHamiltonian H) joint = energy H (systemReduce joint) + energy H (bathReduce joint) := by
  unfold energy
  rw [jointEnergy_eq_reduced, Complex.add_re]

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

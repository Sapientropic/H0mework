import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock.Source

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock
open Thermal.Collision Propagation.Interface
noncomputable section

private theorem energy_comm {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) : energy A B=energy B A := by
  unfold energy
  rw [Matrix.trace_mul_comm]

private theorem energy_star_left {ι : Type*} [Fintype ι]
    (A rho : Matrix ι ι ℂ) (hermitian : rho.IsHermitian) : energy (star A) rho=energy A rho := by
  have adjoint : energy (star A) rho=(star (A*rho)).trace.re := by
    rw [star_mul,hermitian.isSelfAdjoint.star_eq]
    exact energy_comm _ _
  rw [adjoint]
  change (A*rho).conjTranspose.trace.re=(A*rho).trace.re
  rw [Matrix.trace_conjTranspose]
  rfl

private theorem energy_sym_left {ι : Type*} [Fintype ι]
    (A rho : Matrix ι ι ℂ) (hermitian : rho.IsHermitian) :
    energy ((1/2 : ℝ) • (A+star A)) rho=energy A rho := by
  have linear : energy ((1/2 : ℝ) • (A+star A)) rho=
      (energy A rho+energy (star A) rho)/2 := by
    simp [energy,Matrix.add_mul,Matrix.trace_add,Matrix.trace_smul]
    ring
  rw [linear,energy_star_left A rho hermitian]
  ring

private theorem energy_sym_right {ι : Type*} [Fintype ι]
    (F A : Matrix ι ι ℂ) (hermitian : F.IsHermitian) :
    energy F ((1/2 : ℝ) • (A+star A))=energy F A := by
  rw [energy_comm,energy_sym_left A F hermitian,energy_comm A F]

theorem source_pairing (rho : Matrix Basis Basis ℂ) (hermitian : rho.IsHermitian) :
    energy hamiltonian rho=energy fock (sourceLift rho) := by
  rw [hamiltonian,energy_sym_left rawPullback rho hermitian,
    sourceLift,energy_sym_right fock (frame*rho*frame) fock_hermitian]
  unfold energy rawPullback
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm frame]
  simp only [Matrix.mul_assoc]

def registeredHamiltonian : Matrix Basis Basis ℂ := star frame*fock*frame
def registeredLift (rho : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ := frame*rho*star frame
def frameResidual : Matrix Basis Basis ℂ := registeredHamiltonian-hamiltonian

theorem registered_hermitian : registeredHamiltonian.IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul frame fock_hermitian

theorem registered_pairing (rho : Matrix Basis Basis ℂ) :
    energy registeredHamiltonian rho=energy fock (registeredLift rho) := by
  unfold energy registeredHamiltonian registeredLift
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (star frame)]
  simp only [Matrix.mul_assoc]

theorem full_frame_residual (rho : Matrix Basis Basis ℂ) (hermitian : rho.IsHermitian) :
    energy frameResidual rho=energy fock (registeredLift rho)-energy fock (sourceLift rho) := by
  unfold frameResidual
  have linear : energy (registeredHamiltonian-hamiltonian) rho=
      energy registeredHamiltonian rho-energy hamiltonian rho := by
    simp only [energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]
  rw [linear,registered_pairing,source_pairing rho hermitian]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock

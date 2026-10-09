import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.InstrumentContinuation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Propagation.Interface Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] originalToCalculated Preparation.sourceEnergyFrame actualUnitary A E

theorem original_intertwining : transformedOriginal*(originalToCalculated : Matrix Basis Basis ℂ) =
    (originalToCalculated : Matrix Basis Basis ℂ)*Thermal.Source.energyHamiltonian := by
  rw [← same_source_Hamiltonian,Quantum.conjugation_apply]
  simp only [Matrix.mul_assoc,Unitary.coe_star_mul_self,Matrix.mul_one]

theorem actual_intertwining_error :
    ‖E*(originalToCalculated : Matrix Basis Basis ℂ)-
      (originalToCalculated : Matrix Basis Basis ℂ)*Thermal.Source.energyHamiltonian‖ ≤ (21/10^12 : ℝ) := by
  rw [← original_intertwining,← Matrix.sub_mul]
  rw [CStarRing.norm_mul_coe_unitary,norm_sub_rev]
  exact actual_source_diagonal_error

def originalTop : Basis := Spectrum.firstIndex

def originalTopProjector : Matrix Basis Basis ℂ := Spectrum.basisPure originalTop

theorem original_top_hamiltonian : Thermal.Source.energyHamiltonian*originalTopProjector =
    (Preparation.sourceEnergies originalTop : ℂ) • originalTopProjector := by
  ext i j
  simp only [Thermal.Source.energyHamiltonian,originalTopProjector,Spectrum.basisPure,
    Matrix.diagonal_mul_diagonal,Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul]
  split_ifs <;> subst_vars <;> simp

theorem original_projected_intertwining :
    (E-(Preparation.sourceEnergies originalTop : ℂ) • 1)*
      (originalToCalculated : Matrix Basis Basis ℂ)*originalTopProjector =
    (E*(originalToCalculated : Matrix Basis Basis ℂ)-
      (originalToCalculated : Matrix Basis Basis ℂ)*Thermal.Source.energyHamiltonian)*originalTopProjector := by
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc,original_top_hamiltonian,
    Matrix.mul_smul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

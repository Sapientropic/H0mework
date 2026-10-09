import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Body

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Source.donor installedPCFrame installedLoadFrame BodyKernel.bodyFree
  loadTotalHamiltonian originalCalculatedOutput Spectral.Projection.excitedIndex

def actualDonor : Matrix PairController PairController ℂ := Quantum.conjugation installedPCFrame Source.donor

def actualHamiltonian : LoadedJoint := Quantum.conjugation installedLoadFrame loadTotalHamiltonian

def actualFree : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  installedLoadFrame*BodyKernel.bodyFree*star installedLoadFrame

def actualOutput : LoadedJoint := Quantum.conjugation actualFree
  (bodyInverse actualDonor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) actualHamiltonian)

theorem original_inverse_with_donor :
    BasisInverse.bodyInverse Spectral.Projection.excitedIndex (Real.cos BasisInverse.actualAngle)
      (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian =
    bodyInverse Source.donor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian := by
  rw [Spectral.Projection.actual_donor,basis_body_inverse]

theorem actual_body_inverse : Quantum.conjugation installedLoadFrame
    (BasisInverse.bodyInverse Spectral.Projection.excitedIndex (Real.cos BasisInverse.actualAngle)
      (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian) =
    bodyInverse actualDonor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) actualHamiltonian := by
  rw [original_inverse_with_donor]
  unfold actualDonor actualHamiltonian installedLoadFrame
  rw [body_inverse_covariant]

private theorem frame_after_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    Quantum.conjugation U (Quantum.conjugation V O) =
      Quantum.conjugation (U*V*star U) (Quantum.conjugation U O) := by
  rw [Environment.conjugation_comp,Environment.conjugation_comp]
  have same : U*V*star U*U = U*V := by simp only [mul_assoc,Unitary.star_mul_self,mul_one]
  rw [same]

theorem original_calculated_inverse : originalCalculatedOutput = actualOutput := by
  unfold originalCalculatedOutput BasisInverse.actualOutput
  rw [frame_after_action installedLoadFrame BodyKernel.bodyFree,actual_body_inverse]
  rfl

theorem actual_donor_distance : ‖actualDonor-Donor.calculatedDonor‖ ≤ (1/10^9 : ℝ) := Donor.actual_donor_error

theorem actual_hamiltonian_distance : ‖actualHamiltonian-numericLoadHamiltonian‖ ≤ (126/10^12 : ℝ) :=
  original_load_Hamiltonian_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.WholeCovariance

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def numericEnvironmentRead : Matrix (Fin 2) (Fin 2) ℂ :=
  (numericDonorEnergy : ℂ) • 1+Powered.Dynamics.controllerHamiltonian 2
def numericProjector : LoadedJoint := Matrix.kronecker Donor.calculatedDonor (1 : Matrix (Fin 2) (Fin 2) ℂ)

def numericCoreInverse : LoadedJoint :=
  ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ •
    (numericLoadHamiltonian-(Real.sin BasisInverse.actualAngle : ℂ)^2 •
      Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead)+
    plusCoefficient • (numericProjector*loadInteraction)+minusCoefficient • (loadInteraction*numericProjector)

theorem original_environment_error : ‖sourceEnvironmentRead-numericEnvironmentRead‖ ≤ (44/10^12 : ℝ) := by
  have delta : sourceEnvironmentRead-numericEnvironmentRead = ((donorEnergy-numericDonorEnergy : ℝ) : ℂ) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold sourceEnvironmentRead numericEnvironmentRead
    push_cast
    module
  rw [delta,norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact donor_energy_error

theorem original_projector_error : ‖actualProjector-numericProjector‖ ≤ (1/10^9 : ℝ) := by
  have delta : actualProjector-numericProjector =
    Matrix.kronecker (actualDonor-Donor.calculatedDonor) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [actualProjector,numericProjector,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [delta]
  exact (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := Fin 2)) _).trans actual_donor_distance

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Spectral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Cancellation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Powered.Producer.poweredTotalHamiltonian Source.donor actualDonor installedPCFrame

theorem original_donor_right_eigen : Powered.Producer.poweredTotalHamiltonian*Source.donor =
    (donorEnergy : ℂ) • Source.donor := by
  have h := spectral_pure_eigen Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian (Spectrum.firstIndex (ι := PairController))
  have donor : Spectrum.spectralPure Powered.Producer.poweredTotalHamiltonian
      Powered.Producer.poweredTotalHamiltonian_hermitian (Spectrum.firstIndex (ι := PairController)) = Source.donor := by
    unfold Source.donor
    rfl
  rw [donor] at h
  rw [← donorEigenvalue] at h
  rw [Spectral.Projection.actual_donor_eigenvalue] at h
  exact h

theorem original_donor_left_eigen : Source.donor*Powered.Producer.poweredTotalHamiltonian =
    (donorEnergy : ℂ) • Source.donor := by
  have h := congrArg star original_donor_right_eigen
  simpa only [star_mul,show star Source.donor=Source.donor from Source.donor_positive.isHermitian.eq,
    show star Powered.Producer.poweredTotalHamiltonian=Powered.Producer.poweredTotalHamiltonian from Powered.Producer.poweredTotalHamiltonian_hermitian.eq,
    star_smul,Complex.star_def,Complex.conj_ofReal] using h

def originalFreeHamiltonian : LoadedJoint := Powered.Dynamics.bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2

theorem free_slice (e f : Fin 2) : BodyKernel.slice originalFreeHamiltonian e f =
    (if e=f then 1 else 0 : ℂ) • Powered.Producer.poweredTotalHamiltonian+
      Powered.Dynamics.controllerHamiltonian 2 e f • (1 : Matrix PairController PairController ℂ) := by
  ext i j
  simp only [BodyKernel.slice,Matrix.submatrix_apply,originalFreeHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  ring

theorem free_slice_right (e f : Fin 2) : BodyKernel.slice originalFreeHamiltonian e f*Source.donor =
    ((donorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f) • Source.donor := by
  rw [free_slice,Matrix.add_mul,Matrix.smul_mul,Matrix.smul_mul,Matrix.one_mul,original_donor_right_eigen]
  simp only [smul_smul,← add_smul]
  congr 1
  ring

theorem free_slice_left (e f : Fin 2) : Source.donor*BodyKernel.slice originalFreeHamiltonian e f =
    ((donorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f) • Source.donor := by
  rw [free_slice,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,Matrix.mul_one,original_donor_left_eigen]
  simp only [smul_smul,← add_smul]
  congr 1
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

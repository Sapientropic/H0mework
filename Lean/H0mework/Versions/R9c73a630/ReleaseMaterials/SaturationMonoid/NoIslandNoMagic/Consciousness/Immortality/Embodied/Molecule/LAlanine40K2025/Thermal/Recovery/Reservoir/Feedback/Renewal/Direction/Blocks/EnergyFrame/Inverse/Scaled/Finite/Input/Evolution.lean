import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Gram

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem single_add (H : Matrix ι ι ℂ) (hermitian : H.IsHermitian) (s t : ℝ) :
    singleUnitary H hermitian s * singleUnitary H hermitian t=singleUnitary H hermitian (s+t) := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  apply Subtype.ext
  change NormedSpace.exp (s • (-Complex.I • H))*NormedSpace.exp (t • (-Complex.I • H))=
    NormedSpace.exp ((s+t) • (-Complex.I • H))
  rw [add_smul,NormedSpace.exp_add_of_commute ((Commute.refl (-Complex.I • H)).smul_left s |>.smul_right t)]

theorem single_covariance (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ)
    (hermitian : H.IsHermitian) (targetHermitian : (Quantum.conjugation U H).IsHermitian) (time : ℝ) :
    U * singleUnitary H hermitian time * star U=
      singleUnitary (Quantum.conjugation U H) targetHermitian time := by
  apply Subtype.ext
  exact flow_conjugation U H time

theorem single_commuting_state (H rho : Matrix ι ι ℂ) (hermitian : H.IsHermitian)
    (commutes : Commute H rho) (time : ℝ) :
    Quantum.conjugation (singleUnitary H hermitian time) rho=rho := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  have flowCommutes : Commute (hamiltonianFlow H time) rho :=
    (commutes.smul_left (-Complex.I) |>.smul_left time).exp_left
  change Commute (singleUnitary H hermitian time : Matrix ι ι ℂ) rho at flowCommutes
  rw [Quantum.conjugation_apply,flowCommutes.eq,mul_assoc]
  have unitary := (Unitary.mem_iff.mp (singleUnitary H hermitian time).property).2
  change (singleUnitary H hermitian time : Matrix ι ι ℂ)*star (singleUnitary H hermitian time : Matrix ι ι ℂ)=1 at unitary
  rw [unitary,mul_one]

theorem electronic_unitary_read (time : ℝ) : Recovery.PreparationEnergy.electronicUnitary time=
    singleUnitary (activeMatrix electronicSource) (Propagation.Dynamics.activeMatrix_hermitian electronicSource) time := by
  apply Subtype.ext
  let equiv := Propagation.Dynamics.matrixOperatorEquiv
  let : NormedAlgebra ℚ Propagation.Dynamics.ElectronicOperator := .restrictScalars ℚ ℂ _
  change equiv.symm (NormedSpace.exp _) = NormedSpace.exp (time • (-Complex.I • activeMatrix electronicSource))
  rw [NormedSpace.map_exp equiv.symm equiv.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous]
  congr 1
  simp only [map_smul,Propagation.Dynamics.hamiltonian,equiv,StarAlgEquiv.symm_apply_apply]
  ext i j
  simp [Matrix.smul_apply,smul_eq_mul,Complex.real_smul]

theorem original_bath_active_stationary (time : ℝ) :
    Quantum.conjugation (singleUnitary Thermal.Source.energyHamiltonian Thermal.Source.energyHamiltonian_hermitian time)
      Thermal.Source.bathCurrent=Thermal.Source.bathCurrent :=
  single_commuting_state _ _ _ Thermal.Source.bath_commutes_with_energy time

theorem evolved_bath_field_only : evolvedBath=
    Quantum.conjugation (singleUnitary Work.Drive.fieldOffHamiltonian Work.Drive.fieldOffHamiltonian_hermitian (Propagation.Producer.nativeClockStep : ℝ))
      Thermal.Source.bathCurrent := by
  rw [evolvedBath,singleWord,← Environment.conjugation_comp,original_bath_active_stationary]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

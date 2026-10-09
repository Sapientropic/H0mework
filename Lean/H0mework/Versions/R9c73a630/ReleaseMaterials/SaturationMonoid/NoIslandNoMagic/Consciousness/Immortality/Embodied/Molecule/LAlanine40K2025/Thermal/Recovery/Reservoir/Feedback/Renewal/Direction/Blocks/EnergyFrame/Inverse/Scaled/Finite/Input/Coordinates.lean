import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Gibbs
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Evolution

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Source Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] actualUnitary Preparation.sourceEnergyFrame baseSystem
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rebased_state (U V : Matrix.unitaryGroup ι ℂ) (rho : Matrix ι ι ℂ) :
    Quantum.conjugation U (Quantum.conjugation V rho)=
      Quantum.conjugation (U*V*star U) (Quantum.conjugation U rho) := by
  rw [Environment.conjugation_comp,Environment.conjugation_comp]
  congr 1
  simp only [mul_assoc,Unitary.star_mul_self,mul_one]

theorem single_state_covariance (U : Matrix.unitaryGroup ι ℂ) (H rho : Matrix ι ι ℂ)
    (hermitian : H.IsHermitian) (targetHermitian : (Quantum.conjugation U H).IsHermitian) (time : ℝ) :
    Quantum.conjugation U (Quantum.conjugation (singleUnitary H hermitian time) rho)=
      Quantum.conjugation (singleUnitary (Quantum.conjugation U H) targetHermitian time) (Quantum.conjugation U rho) := by
  rw [rebased_state,single_covariance U H hermitian targetHermitian time]

theorem transformed_hermitian : transformedOriginal.IsHermitian := by
  rw [← same_source_Hamiltonian,Quantum.conjugation_apply]
  exact Matrix.isHermitian_mul_mul_conjTranspose _ Thermal.Source.energyHamiltonian_hermitian

def calculatedFieldHamiltonian : SystemMatrix Basis := Quantum.conjugation originalToCalculated Work.Drive.fieldOffHamiltonian

theorem calculated_field_hermitian : calculatedFieldHamiltonian.IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ Work.Drive.fieldOffHamiltonian_hermitian

def calculatedBaseSystem : SystemMatrix Basis := Quantum.conjugation (star actualUnitary) baseSystem

def calculatedSystem : SystemMatrix Basis :=
  Quantum.conjugation (singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ))
    (Quantum.conjugation (singleUnitary transformedOriginal transformed_hermitian
      ((nativeClockStep : ℝ)+(Preparation.collisionCurrentTime : ℝ))) calculatedBaseSystem)

def calculatedBath : SystemMatrix Basis :=
  Quantum.conjugation (singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ))
    (normalizedExponential transformedOriginal)

private theorem frame_cancel (U V W : Matrix.unitaryGroup ι ℂ) : (star U*V)*(star V*W)=star U*W := by
  simp only [mul_assoc,← mul_assoc V (star V) W,Unitary.mul_star_self,one_mul]

theorem original_preparation_calculated : Quantum.conjugation originalToCalculated Thermal.Source.systemCurrent=
    Quantum.conjugation (singleUnitary transformedOriginal transformed_hermitian (Preparation.collisionCurrentTime : ℝ)) calculatedBaseSystem := by
  rw [prepared_system_from_original_gram,Environment.conjugation_comp]
  have word : originalToCalculated*(star Preparation.sourceEnergyFrame*Recovery.PreparationEnergy.electronicUnitary (Preparation.collisionCurrentTime : ℝ))=
      star actualUnitary*Recovery.PreparationEnergy.electronicUnitary (Preparation.collisionCurrentTime : ℝ) :=
    frame_cancel actualUnitary Preparation.sourceEnergyFrame _
  rw [word,← Environment.conjugation_comp,electronic_unitary_read]
  have hermitian : (Quantum.conjugation (star actualUnitary) (activeMatrix electronicSource)).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ (Propagation.Dynamics.activeMatrix_hermitian electronicSource)
  have paid := single_state_covariance (star actualUnitary) (activeMatrix electronicSource) baseSystem
    (Propagation.Dynamics.activeMatrix_hermitian electronicSource) hermitian (Preparation.collisionCurrentTime : ℝ)
  have same : Quantum.conjugation (star actualUnitary) (activeMatrix electronicSource)=transformedOriginal := by
    simp only [Quantum.conjugation_apply,Unitary.coe_star,star_star,transformedOriginal,A]
  simpa only [same,calculatedBaseSystem] using paid

theorem original_system_calculated : Quantum.conjugation originalToCalculated evolvedSystem=calculatedSystem := by
  rw [evolvedSystem,singleWord,← Environment.conjugation_comp]
  have activeHermitian : (Quantum.conjugation originalToCalculated Thermal.Source.energyHamiltonian).IsHermitian := by
    rw [same_source_Hamiltonian]; exact transformed_hermitian
  rw [single_state_covariance originalToCalculated _ _ _ calculated_field_hermitian,
    single_state_covariance originalToCalculated _ _ _ activeHermitian]
  simp only [same_source_Hamiltonian,original_preparation_calculated,Environment.conjugation_comp,single_add,calculatedSystem,calculatedFieldHamiltonian]

theorem original_bath_calculated : Quantum.conjugation originalToCalculated evolvedBath=calculatedBath := by
  rw [evolved_bath_field_only,single_state_covariance originalToCalculated _ _ _ calculated_field_hermitian,
    calculated_bath_exponential]
  rfl

theorem original_pair_calculated : Quantum.localConjugation originalToCalculated originalToCalculated
    Powered.Producer.sourceReceivedPair=jointNext calculatedSystem calculatedBath mergedCosine mergedSine := by
  rw [source_pair_two_single_matrices]
  have paid := shared_joint_next originalToCalculated evolvedSystem evolvedBath mergedCosine mergedSine
  simpa only [original_system_calculated,original_bath_calculated] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

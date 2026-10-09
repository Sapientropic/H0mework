import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Composition
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Shared

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface Propagation.Producer Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def singleWord : Matrix.unitaryGroup Basis ℂ :=
  singleUnitary Work.Drive.fieldOffHamiltonian Work.Drive.fieldOffHamiltonian_hermitian (nativeClockStep : ℝ) *
    singleUnitary Thermal.Source.energyHamiltonian Thermal.Source.energyHamiltonian_hermitian (nativeClockStep : ℝ)

def mergedCosine : ℝ := Real.cos (2*(nativeClockStep : ℝ))*Thermal.Source.exchangeCosine-
  Real.sin (2*(nativeClockStep : ℝ))*Thermal.Source.exchangeSine
def mergedSine : ℝ := Real.cos (2*(nativeClockStep : ℝ))*Thermal.Source.exchangeSine+
  Real.sin (2*(nativeClockStep : ℝ))*Thermal.Source.exchangeCosine

theorem original_pair_word_factors : pairWord=Quantum.localUnitary singleWord singleWord *
    (Exchange.exchangeUnitary (ι := Basis) (2*(nativeClockStep : ℝ))*collisionUnitary) := by
  rw [pairWord,Work.Drive.fieldCycleUnitary,pair_steps_product]
  simp only [Thermal.Source.pairCoupling,one_mul,← two_mul,mul_assoc,singleWord]

theorem merged_collision_matrix :
    (Exchange.exchangeUnitary (ι := Basis) (2*(nativeClockStep : ℝ))*collisionUnitary : JointMatrix Basis)=
      partialSwap mergedCosine mergedSine := by
  change partialSwap (Real.cos (2*(nativeClockStep : ℝ))) (Real.sin (2*(nativeClockStep : ℝ))) *
    partialSwap Thermal.Source.exchangeCosine Thermal.Source.exchangeSine=_
  rw [partial_swap_product]
  rfl

def evolvedSystem : SystemMatrix Basis := Quantum.conjugation singleWord Thermal.Source.systemCurrent
def evolvedBath : SystemMatrix Basis := Quantum.conjugation singleWord Thermal.Source.bathCurrent

private theorem collision_read {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup (ι × ι) ℂ) (rho tau : SystemMatrix ι) (c s : ℝ)
    (same : (U : JointMatrix ι)=partialSwap c s) :
    Quantum.conjugation U (Matrix.kronecker rho tau)=jointNext rho tau c s := by
  rw [Quantum.conjugation_apply,same]
  rfl

theorem source_pair_two_single_matrices : Powered.Producer.sourceReceivedPair=
    jointNext evolvedSystem evolvedBath mergedCosine mergedSine := by
  rw [source_pair_from_preparation,original_pair_word_factors,← Environment.conjugation_comp]
  have inner : Quantum.conjugation (Exchange.exchangeUnitary (ι := Basis) (2*(nativeClockStep : ℝ))*collisionUnitary) pairPreparation=
      jointNext Thermal.Source.systemCurrent Thermal.Source.bathCurrent mergedCosine mergedSine := by
    exact collision_read _ Thermal.Source.systemCurrent Thermal.Source.bathCurrent mergedCosine mergedSine merged_collision_matrix
  rw [inner]
  exact shared_joint_next singleWord Thermal.Source.systemCurrent Thermal.Source.bathCurrent mergedCosine mergedSine

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

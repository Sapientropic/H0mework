import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface Propagation.Producer Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def collisionUnitary : Matrix.unitaryGroup (Basis × Basis) ℂ :=
  ⟨partialSwap Thermal.Source.exchangeCosine Thermal.Source.exchangeSine,
    partialSwap_unitary _ _ Thermal.Source.exchange_normalized⟩

def pairWord : Matrix.unitaryGroup (Basis × Basis) ℂ :=
  Work.Drive.fieldCycleUnitary *
    Thermal.Dynamics.pairUnitary Thermal.Source.energyHamiltonian Thermal.Source.energyHamiltonian_hermitian
      Thermal.Source.pairCoupling (nativeClockStep : ℝ) * collisionUnitary

def pairPreparation : JointMatrix Basis := Matrix.kronecker Thermal.Source.systemCurrent Thermal.Source.bathCurrent

private theorem pair_advance_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : SystemMatrix ι) (hermitian : H.IsHermitian) (g t : ℝ) (rho : JointMatrix ι) :
    Thermal.Dynamics.pairAdvance H g t rho=Quantum.conjugation (Thermal.Dynamics.pairUnitary H hermitian g t) rho :=
  Thermal.Dynamics.pairAdvance_eq_unitary H hermitian g t rho

private theorem starAut_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) : Unitary.conjStarAlgAut ℂ _ U A=Quantum.conjugation U A := rfl

theorem source_pair_from_preparation : Powered.Producer.sourceReceivedPair=Quantum.conjugation pairWord pairPreparation := by
  rw [Powered.Producer.sourceReceivedPair_eq_fieldTarget,Work.Drive.sourceFieldCycleTarget,
    Work.Drive.fieldCycleAdvance_eq_conjugation,starAut_conjugation,Work.Drive.sourceFieldCycleCurrent,Thermal.Producer.rememberedJoint,
    Thermal.Source.timedPairAdvance,pair_advance_conjugation _ Thermal.Source.energyHamiltonian_hermitian]
  have collision : Thermal.Producer.generatedJoint=Quantum.conjugation collisionUnitary pairPreparation := by
    change jointNext Thermal.Source.systemCurrent Thermal.Source.bathCurrent Thermal.Source.exchangeCosine Thermal.Source.exchangeSine=_
    simp only [jointNext,Quantum.conjugation_apply,collisionUnitary,pairPreparation,Matrix.star_eq_conjTranspose]
  rw [collision]
  rw [Environment.conjugation_comp,Environment.conjugation_comp]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

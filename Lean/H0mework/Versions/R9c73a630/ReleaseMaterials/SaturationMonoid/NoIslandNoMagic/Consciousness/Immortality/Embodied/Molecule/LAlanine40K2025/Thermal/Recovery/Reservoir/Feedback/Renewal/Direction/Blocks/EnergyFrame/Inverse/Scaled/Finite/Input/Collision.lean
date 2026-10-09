import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.PairBudget

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Producer Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def mergedUnitary : Matrix.unitaryGroup (Basis × Basis) ℂ :=
  Exchange.exchangeUnitary (2*(nativeClockStep : ℝ))*collisionUnitary

theorem original_collision_read (rho tau : SystemMatrix Basis) :
    jointNext rho tau mergedCosine mergedSine=Quantum.conjugation mergedUnitary (Matrix.kronecker rho tau) := by
  rw [Quantum.conjugation_apply]
  have same : (mergedUnitary : JointMatrix Basis)=partialSwap mergedCosine mergedSine := merged_collision_matrix
  rw [same,Matrix.star_eq_conjTranspose]
  rfl

def finiteCollisionPair : JointMatrix Basis := Quantum.conjugation mergedUnitary (Matrix.kronecker finiteSystem finiteBath)

theorem source_collision_energy_error (O : JointMatrix Basis) :
    |energy O (Quantum.localConjugation originalToCalculated originalToCalculated Powered.Producer.sourceReceivedPair)-
      energy O finiteCollisionPair| ≤ (5/10^6 : ℝ)*‖O‖ := by
  rw [original_pair_calculated,original_collision_read,finiteCollisionPair]
  have read (rho : JointMatrix Basis) :
      energy O (Quantum.conjugation mergedUnitary rho)=energy (Quantum.conjugation (star mergedUnitary) O) rho := by
    exact energy_pullback O rho mergedUnitary
  rw [read,read]
  have paid := source_preparation_energy_error (Quantum.conjugation (star mergedUnitary) O)
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (star mergedUnitary)) O
  change ‖Quantum.conjugation (star mergedUnitary) O‖=‖O‖ at same
  rwa [same] at paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

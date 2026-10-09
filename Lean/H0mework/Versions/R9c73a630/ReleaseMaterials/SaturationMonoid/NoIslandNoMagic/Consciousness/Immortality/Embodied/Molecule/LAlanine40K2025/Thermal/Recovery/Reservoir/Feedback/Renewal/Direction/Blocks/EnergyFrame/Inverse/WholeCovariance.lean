import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Whole

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Powered.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] installedLoadFrame installedPCFrame actualDonor actualHamiltonian sourceProjector

def actualProjector : LoadedJoint := Matrix.kronecker actualDonor (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem actual_projector_covariance : Quantum.conjugation installedLoadFrame sourceProjector = actualProjector := by
  unfold sourceProjector actualProjector actualDonor installedLoadFrame
  rw [spectator_conjugation]

theorem actual_interaction_fixed : Quantum.conjugation installedLoadFrame loadInteraction=loadInteraction := by
  unfold installedLoadFrame installedPCFrame
  exact controller_environment_invariant originalToCalculated

theorem actual_environment_fixed : Quantum.conjugation installedLoadFrame
    (Matrix.kronecker (1 : Matrix PairController PairController ℂ) sourceEnvironmentRead) =
      Matrix.kronecker (1 : Matrix PairController PairController ℂ) sourceEnvironmentRead := by
  unfold installedLoadFrame
  rw [spectator_conjugation]
  have one : Quantum.conjugation installedPCFrame (1 : Matrix PairController PairController ℂ)=1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) installedPCFrame)
  rw [one]

def actualCoreInverse : LoadedJoint :=
  ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ •
    (actualHamiltonian-(Real.sin BasisInverse.actualAngle : ℂ)^2 •
      Matrix.kronecker (1 : Matrix PairController PairController ℂ) sourceEnvironmentRead)+
    plusCoefficient • (actualProjector*loadInteraction)+minusCoefficient • (loadInteraction*actualProjector)

theorem original_inverse_core_covariance : Quantum.conjugation installedLoadFrame
    (sourceFreeInverse+sourceInteractionInverse)=actualCoreInverse := by
  have split : originalFreeHamiltonian+loadInteraction=loadTotalHamiltonian := rfl
  have expression : sourceFreeInverse+sourceInteractionInverse =
      ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ •
        (loadTotalHamiltonian-(Real.sin BasisInverse.actualAngle : ℂ)^2 •
          Matrix.kronecker (1 : Matrix PairController PairController ℂ) sourceEnvironmentRead)+
        plusCoefficient • (sourceProjector*loadInteraction)+minusCoefficient • (loadInteraction*sourceProjector) := by
    rw [← split]
    unfold sourceFreeInverse sourceInteractionInverse
    module
  rw [expression]
  have product (A B : LoadedJoint) : Quantum.conjugation installedLoadFrame (A*B)=
      Quantum.conjugation installedLoadFrame A*Quantum.conjugation installedLoadFrame B :=
    map_mul (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) A B
  simp only [map_add,map_sub,map_smul,product,actual_projector_covariance,actual_environment_fixed,actual_interaction_fixed]
  unfold actualCoreInverse actualHamiltonian
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

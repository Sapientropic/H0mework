import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Merged

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface Propagation.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def baseSystem : SystemMatrix Basis := Preparation.normalizedGram (initialDensityMatrix electronicSource)

def systemWord : Matrix.unitaryGroup Basis ℂ := singleWord * star Preparation.sourceEnergyFrame *
  Recovery.PreparationEnergy.electronicUnitary (Preparation.collisionCurrentTime : ℝ)

theorem prepared_system_from_original_gram : Thermal.Source.systemCurrent=Quantum.conjugation
    (star Preparation.sourceEnergyFrame * Recovery.PreparationEnergy.electronicUnitary (Preparation.collisionCurrentTime : ℝ)) baseSystem := by
  change Preparation.energyCoordinates (Preparation.preparedDensity (Preparation.collisionCurrentTime : ℝ))=_
  rw [← Powered.Source.sourceCoordinates_as_conjugation]
  have prepared : Preparation.preparedDensity (Preparation.collisionCurrentTime : ℝ)=
      Quantum.conjugation (Recovery.PreparationEnergy.electronicUnitary (Preparation.collisionCurrentTime : ℝ)) baseSystem :=
    Recovery.PreparationEnergy.preparedDensity_actual _
  rw [prepared,Environment.conjugation_comp]

theorem evolved_system_from_original_gram : evolvedSystem=Quantum.conjugation systemWord baseSystem := by
  rw [evolvedSystem,prepared_system_from_original_gram,Environment.conjugation_comp]
  exact congrArg (fun U => Quantum.conjugation U baseSystem) (mul_assoc _ _ _).symm

theorem base_system_lawful : baseSystem.PosSemidef ∧ baseSystem.trace=1 :=
  ⟨Preparation.normalizedGram_posSemidef _,Preparation.normalizedGram_trace _
    Recovery.SourcePrimitive.sourceInitialDensity_nonzero⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

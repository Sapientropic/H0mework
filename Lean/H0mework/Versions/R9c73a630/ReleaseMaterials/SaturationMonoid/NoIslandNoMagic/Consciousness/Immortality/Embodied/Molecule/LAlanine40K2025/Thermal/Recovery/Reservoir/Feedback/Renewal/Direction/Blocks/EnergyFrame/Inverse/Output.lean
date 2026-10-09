import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.CoreError

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] actualFree actualCoreInverse numericCoreInverse originalCalculatedOutput installedLoadFrame BodyKernel.bodyFree

theorem original_calculated_output_core : originalCalculatedOutput=Quantum.conjugation actualFree actualCoreInverse := by
  rw [original_calculated_output,original_output_whole]
  have composition : Quantum.conjugation installedLoadFrame
      (Quantum.conjugation BodyKernel.bodyFree (sourceFreeInverse+sourceInteractionInverse)) =
    Quantum.conjugation actualFree (Quantum.conjugation installedLoadFrame (sourceFreeInverse+sourceInteractionInverse)) := by
    rw [Environment.conjugation_comp,Environment.conjugation_comp]
    have same : actualFree*installedLoadFrame=installedLoadFrame*BodyKernel.bodyFree := by
      unfold actualFree
      simp only [mul_assoc,Unitary.star_mul_self,mul_one]
    rw [same]
  rw [composition,original_inverse_core_covariance]

def calculatedOutputCore : LoadedJoint := Quantum.conjugation actualFree numericCoreInverse

theorem original_calculated_output_error : ‖originalCalculatedOutput-calculatedOutputCore‖ ≤ coreErrorBudget := by
  rw [original_calculated_output_core,calculatedOutputCore,← map_sub]
  have same : ‖Quantum.conjugation actualFree (actualCoreInverse-numericCoreInverse)‖ =
      ‖actualCoreInverse-numericCoreInverse‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint actualFree) _
  rw [same]
  exact actual_core_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

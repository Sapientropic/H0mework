import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Gain

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def sourcePointer : PointerJoint := approximatedPointer sourceRoot sourceComplement
def sourceNine : PointerJoint := approximatedNine sourceRoot sourceComplement
def sourceEleven : PointerJoint := approximatedEleven sourceRoot sourceComplement

theorem source_pointer_error : ‖(finitePointer : PointerJoint)-sourcePointer‖ ≤ (4/10^7 : ℝ) :=
  finite_approximated_pointer_error sourceRoot sourceComplement source_whole_roots_error.1 source_whole_roots_error.2

theorem source_original_PC_gain_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead sourceEleven)-Resource.pcEnergyOf (bodyRead sourceNine))| ≤ (71/10^7 : ℝ) :=
  original_approximated_PC_gain_error sourceRoot sourceComplement source_whole_roots_error.1 source_whole_roots_error.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

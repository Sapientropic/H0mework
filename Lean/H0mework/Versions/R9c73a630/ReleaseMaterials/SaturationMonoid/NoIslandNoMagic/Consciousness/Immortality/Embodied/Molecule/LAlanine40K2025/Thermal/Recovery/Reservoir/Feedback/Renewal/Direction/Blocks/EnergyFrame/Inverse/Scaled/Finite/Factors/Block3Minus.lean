import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block3
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block3Minus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(70975620381888528/10000000000000000),0,0,0;
     0,(70975620119583176/10000000000000000),0,0;
     0,(-1408934502178567/10000000000000000),(69538144871448224/10000000000000000),0;
     0,0,0,(69552416574547432/10000000000000000)]

def imagFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,0,0,0;
     0,0,0,0;
     0,0,0,0;
     0,0,0,0]

theorem checked : squareSum
    (residualReal real3 realFactor imagFactor (480362644764/10^10) (1/10^12) (-1))
    (residualImag imag3 realFactor imagFactor (-1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block3Minus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

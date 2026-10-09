import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block4
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block4Minus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(70736315106640792/10000000000000000),0,0,0;
     0,(70736314843448040/10000000000000000),0,0;
     0,(-263192748/10000000000000000),(69308197743801576/10000000000000000),0;
     0,0,0,(69308197477869864/10000000000000000)]

def imagFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,0,0,0;
     0,0,0,0;
     0,(609980152049/10000000000000000),0,0;
     0,0,0,0]

theorem checked : squareSum
    (residualReal real4 realFactor imagFactor (480362644764/10^10) (1/10^12) (-1))
    (residualImag imag4 realFactor imagFactor (-1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block4Minus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

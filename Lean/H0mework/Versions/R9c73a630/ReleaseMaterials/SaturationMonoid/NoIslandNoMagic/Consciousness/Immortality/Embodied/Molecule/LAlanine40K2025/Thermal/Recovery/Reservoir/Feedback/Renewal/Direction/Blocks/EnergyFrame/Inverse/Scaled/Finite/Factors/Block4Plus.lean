import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block4
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block4Plus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(67850030364133384/10000000000000000),0,0,0;
     0,(67850030638522136/10000000000000000),0,0;
     0,(274388750/10000000000000000),(69308200236403616/10000000000000000),0;
     0,0,0,(69308200507936952/10000000000000000)]

def imagFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,0,0,0;
     0,0,0,0;
     0,(-635928203385/10000000000000000),0,0;
     0,0,0,0]

theorem checked : squareSum
    (residualReal real4 realFactor imagFactor (480362644764/10^10) (1/10^12) (1))
    (residualImag imag4 realFactor imagFactor (1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block4Plus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

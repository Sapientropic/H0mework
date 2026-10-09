import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block2
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block2Plus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(15479629376094232/10000000000000000),0,0,0;
     0,(15479630578789978/10000000000000000),0,0;
     0,(6460102487007597/10000000000000000),(19947080023868096/10000000000000000),0;
     0,0,0,(20967092379626932/10000000000000000)]

def imagFactor : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,0,0,0;
     0,0,0,0;
     0,0,0,0;
     0,0,0,0]

theorem checked : squareSum
    (residualReal real2 realFactor imagFactor (480362644764/10^10) (1/10^12) (1))
    (residualImag imag2 realFactor imagFactor (1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block2Plus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

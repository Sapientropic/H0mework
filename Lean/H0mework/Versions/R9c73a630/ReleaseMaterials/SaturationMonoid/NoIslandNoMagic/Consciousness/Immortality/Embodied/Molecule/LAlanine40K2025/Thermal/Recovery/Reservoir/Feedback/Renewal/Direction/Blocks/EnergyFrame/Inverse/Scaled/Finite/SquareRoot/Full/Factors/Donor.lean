import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.DonorEffect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Factors.Donor
open RationalMatrix
noncomputable section

def realPlus : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(8320036230109166/10000000000000000),0,0,0;
     0,(8320036246865643/10000000000000000),(8277989/10000000000000000),0;
     0,(8277989/10000000000000000),(8408964228084079/10000000000000000),0;
     0,0,0,(8408964244444471/10000000000000000)]
def imagPlus : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,0,0,0;
     0,0,(19185214228/10000000000000000),0;
     0,(-19185214228/10000000000000000),0,0;
     0,0,0,0]

theorem checkedPlus : squareSum
    (effectReal real4 (1)-squareReal realPlus imagPlus)
    (effectImag imag4 (1)-squareImag realPlus imagPlus) ≤ ((2/10^7 : ℚ)*(2/10^7))^2 := by
  decide +kernel

def realMinus : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(8495157016060656/10000000000000000),0,0,0;
     0,(8495157000195800/10000000000000000),(-8023393/10000000000000000),0;
     0,(-8023393/10000000000000000),(8408964076862911/10000000000000000),0;
     0,0,0,(8408964060629817/10000000000000000)]
def imagMinus : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,0,0,0;
     0,0,(-18595156175/10000000000000000),0;
     0,(18595156175/10000000000000000),0,0;
     0,0,0,0]

theorem checkedMinus : squareSum
    (effectReal real4 (-1)-squareReal realMinus imagMinus)
    (effectImag imag4 (-1)-squareImag realMinus imagMinus) ≤ ((2/10^7 : ℚ)*(2/10^7))^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Factors.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

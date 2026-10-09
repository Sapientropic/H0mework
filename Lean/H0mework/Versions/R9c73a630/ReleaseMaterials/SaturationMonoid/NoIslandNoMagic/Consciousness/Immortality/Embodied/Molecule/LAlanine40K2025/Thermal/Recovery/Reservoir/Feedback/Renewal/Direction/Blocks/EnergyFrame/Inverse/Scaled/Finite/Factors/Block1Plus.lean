import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block1
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block1Plus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(66982612770403600/10000000000000000),0,0,0,0,0,0,0;
     0,(66982613048345664/10000000000000000),0,0,0,0,0,0;
     (-126571703929400/10000000000000000),(1492924737466178/10000000000000000),(68442863535082032/10000000000000000),0,0,0,0,0;
     0,(-126571703404195/10000000000000000),(2760872606952/10000000000000000),(68459144186630656/10000000000000000),0,0,0,0;
     (1492924743661018/10000000000000000),0,(-121110382810048/10000000000000000),(4884231936/10000000000000000),(66965863852673120/10000000000000000),0,0,0;
     0,(1492924737466178/10000000000000000),(-32564743153916/10000000000000000),(-121080267600384/10000000000000000),(-58885779986/10000000000000000),(66965856267321048/10000000000000000),0,0;
     (126571703929400/10000000000000000),0,(1461306778097762/10000000000000000),(-58932694849/10000000000000000),(126424424921353/10000000000000000),(1494008931798500/10000000000000000),(68427121303083488/10000000000000000),0;
     0,(126571703404195/10000000000000000),(-2760872606952/10000000000000000),(1460959367909426/10000000000000000),(-5099702790/10000000000000000),(126421811362118/10000000000000000),(-2700012611625/10000000000000000),(68443436724982784/10000000000000000)]

def imagFactor : Matrix (Fin 8) (Fin 8) ℚ :=
  !![0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0]

theorem checked : squareSum
    (residualReal real1 realFactor imagFactor (480362644764/10^10) (1/10^12) (1))
    (residualImag imag1 realFactor imagFactor (1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block1Plus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

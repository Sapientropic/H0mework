import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block0Plus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(11892152853535720/10000000000000000),0,0,0,0,0,0,0;
     0,(11892154419045696/10000000000000000),0,0,0,0,0,0;
     (-75864054761196/10000000000000000),(8408905272861791/10000000000000000),(16453202005964984/10000000000000000),0,0,0,0,0;
     0,(-75864044774281/10000000000000000),(38772608875269/10000000000000000),(18477447823169180/10000000000000000),0,0,0,0;
     (8408906379829154/10000000000000000),0,(-16060898123795/10000000000000000),(33701782145/10000000000000000),(8409122132157553/10000000000000000),0,0,0;
     0,(8408905272861791/10000000000000000),(-4297624733612798/10000000000000000),(-5283372857079/10000000000000000),(-8208173680558/10000000000000000),(7227999391211988/10000000000000000),0,0;
     (75864054761196/10000000000000000),0,(6078194099759334/10000000000000000),(-12754328668834/10000000000000000),(43033610595410/10000000000000000),(17449099856544530/10000000000000000),(504480699342/10000000000000000),0;
     0,(75864044774281/10000000000000000),(-38772608875269/10000000000000000),(5412395674206030/10000000000000000),(-95744869486/10000000000000000),(17462392838167/10000000000000000),(-609354819/10000000000000000),(17666967656602654/10000000000000000)]

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
    (residualReal real0 realFactor imagFactor (480362644764/10^10) (1/10^12) (1))
    (residualImag imag0 realFactor imagFactor (1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block0Plus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

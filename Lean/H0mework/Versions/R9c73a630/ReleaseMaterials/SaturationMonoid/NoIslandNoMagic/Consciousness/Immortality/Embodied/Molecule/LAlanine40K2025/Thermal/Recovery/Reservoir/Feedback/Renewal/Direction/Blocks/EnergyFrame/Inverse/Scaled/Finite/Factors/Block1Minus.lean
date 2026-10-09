import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Data.Block1
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalResidual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block1Minus
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def realFactor : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(71558245379061408/10000000000000000),0,0,0,0,0,0,0;
     0,(71558245118891736/10000000000000000),0,0,0,0,0,0;
     (118478358253233/10000000000000000),(-1397463001417282/10000000000000000),(70132842105309400/10000000000000000),0,0,0,0,0;
     0,(118478358683994/10000000000000000),(2360793000245/10000000000000000),(70146763302383192/10000000000000000),0,0,0,0;
     (-1397462996336421/10000000000000000),0,(123247144904518/10000000000000000),(-4147889130/10000000000000000),(71544492373942320/10000000000000000),0,0,0;
     0,(-1397463001417282/10000000000000000),(-27845767855775/10000000000000000),(123223622671738/10000000000000000),(47976055038/10000000000000000),(71544486735211048/10000000000000000),0,0;
     (-118478358253233/10000000000000000),0,(-1425665349886857/10000000000000000),(47980842169/10000000000000000),(-118359402497362/10000000000000000),(-1398286626201958/10000000000000000),(70118233780374448/10000000000000000),0;
     0,(-118478358683994/10000000000000000),(-2360793000245/10000000000000000),(-1425382335520860/10000000000000000),(3984215411/10000000000000000),(-118361286863002/10000000000000000),(-2407360162177/10000000000000000),(70132180001826072/10000000000000000)]

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
    (residualReal real1 realFactor imagFactor (480362644764/10^10) (1/10^12) (-1))
    (residualImag imag1 realFactor imagFactor (-1)) ≤ (1/10^12 : ℚ)^2 := by
  decide +kernel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block1Minus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

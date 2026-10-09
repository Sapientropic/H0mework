import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Inputs

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open RationalMatrix
noncomputable section

def expandedRational (x y u lambda : ℚ) : Matrix (Fin 8) (Fin 8) ℚ :=
  let a : ℚ := x+y-u*lambda
  let b : ℚ := x+y+2-u*(lambda+2)
  let c : ℚ := x+y+2-u*lambda
  let z : ℚ := x+y+4-u*(lambda+2)
  let d : ℚ := (x-y)/2
  !![a,0,d,0,1,0,-d,0;
     0,b,1,d,0,1,0,-d;
     d,1,c,0,d,0,1,0;
     0,d,0,z,0,d,0,1;
     1,0,d,0,a,0,-d,0;
     0,1,0,d,0,b,1,-d;
     -d,0,1,0,-d,1,c,0;
     0,-d,0,1,0,-d,0,z]

theorem expanded_cast (x y u lambda : ℚ) : cast (expandedRational x y u lambda) 0=
    expandedCore (x : ℝ) (y : ℝ) (u : ℝ) (lambda : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [RationalMatrix.cast,expandedRational,expandedCore]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

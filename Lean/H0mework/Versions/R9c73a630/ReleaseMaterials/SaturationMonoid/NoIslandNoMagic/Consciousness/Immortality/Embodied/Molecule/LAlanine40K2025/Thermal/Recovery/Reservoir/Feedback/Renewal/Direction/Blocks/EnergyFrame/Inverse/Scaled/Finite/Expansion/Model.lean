import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Constants

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def expandedCore (x y u lambda : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let a : ℂ := x+y-u*lambda
  let b : ℂ := x+y+2-u*(lambda+2)
  let c : ℂ := x+y+2-u*lambda
  let z : ℂ := x+y+4-u*(lambda+2)
  let d : ℂ := (x-y)/2
  !![a,0,d,0,1,0,-d,0;
     0,b,1,d,0,1,0,-d;
     d,1,c,0,d,0,1,0;
     0,d,0,z,0,d,0,1;
     1,0,d,0,a,0,-d,0;
     0,1,0,d,0,b,1,-d;
     -d,0,1,0,-d,1,c,0;
     0,-d,0,1,0,-d,0,z]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

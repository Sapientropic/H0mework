import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SparseStep
set_option autoImplicit false
namespace FlyCNS.C3Reference
structure Frame where
  jacobian : FlyCNS.C3Sparse.Matrix
  generalizedVelocity : Array Float
  coefficients : Array Float
  position : Array Float
  margin : Array Float

def generate (f : Frame) : Array Float × Array Float :=
  let velocity := FlyCNS.C3Sparse.multiply f.jacobian f.generalizedVelocity
  let reference := (List.range f.jacobian.rows).toArray.map fun i =>
    FlyCNS.C3Actuation.fused (-f.coefficients[4*i+1]!) velocity[i]!
      (((-f.coefficients[4*i]!)*f.coefficients[4*i+2]!)*(f.position[i]!-f.margin[i]!))
  (velocity,reference)
end FlyCNS.C3Reference

import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3FactorStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3AccelerationStep

/-! Original C7 constant-damping Euler velocity. The whole constructor
computes current forces/constraints internally before calling this leaf;
neither qacc nor a later velocity is supplied. Position is a following stage. -/

set_option autoImplicit false

namespace FlyCNS.C3Euler
open FlyCNS.C3Actuation

structure Material where
  timestep : Float
  damping : Array Float

structure Frame where
  matrix : Array Float
  rowStart : Array Nat
  rowCount : Array Nat
  columns : Array Nat
  smoothForce : Array Float
  constraintForce : Array Float
  velocity : Array Float
  time : Float

structure Result where
  dampedFactor : Array Float
  diagonalInverse : Array Float
  acceleration : Array Float
  velocity : Array Float
  time : Float

def advance (m : Material) (frame : Frame) : Result := Id.run do
  let mut matrix := frame.matrix
  for row in [:m.damping.size] do
    let diagonal := frame.rowStart[row]!+frame.rowCount[row]!-1
    matrix := matrix.set! diagonal (fused m.timestep m.damping[row]! matrix[diagonal]!)
  let decomposition := FlyCNS.C3Factor.factor ⟨matrix,frame.rowStart,frame.rowCount,frame.columns⟩
  let rhs := frame.smoothForce.mapIdx fun row value => value+frame.constraintForce[row]!
  let solveFrame : FlyCNS.C3Acceleration.Frame :=
    ⟨#[],#[],#[],#[],decomposition.factor,decomposition.diagonalInverse,frame.rowStart,frame.rowCount,frame.columns⟩
  let acceleration := FlyCNS.C3Acceleration.solveLD solveFrame rhs
  let velocity := frame.velocity.mapIdx fun row value => fused acceleration[row]! m.timestep value
  return ⟨decomposition.factor,decomposition.diagonalInverse,acceleration,velocity,frame.time+m.timestep⟩

end FlyCNS.C3Euler

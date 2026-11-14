import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SparseStep
set_option autoImplicit false
namespace FlyCNS.C3Diagnostics
open FlyCNS.C3Actuation

structure Material where
  bodyMass : Array Float
  gravity : Array Float
  stiffness : Array Float
  jointPosition : Array Nat
  springPosition : Array Float
  rowStart : Array Nat
  rowCount : Array Nat
  columns : Array Nat
  initialPosition : Array Float

structure Reset where
  position : Array Float
  velocity : Array Float
  control : Array Float
  warmstart : Array Float
  applied : Array Float
  bodyApplied : Array Float
  acceleration : Array Float
  time : Float

def reset (m : Material) : Reset :=
  ⟨m.initialPosition,Array.replicate 74 zero,Array.replicate 50 zero,
    Array.replicate 74 zero,Array.replicate 74 zero,Array.replicate (6*m.bodyMass.size) zero,
    Array.replicate 74 zero,zero⟩

def firstBad (values : Array Float) : Option Nat := Id.run do
  for i in [:values.size] do
    if bad values[i]! then return some i
  return none

def potential (m : Material) (position inertiaPosition : Array Float) : Float := Id.run do
  let mut value := zero
  for i in [1:m.bodyMass.size] do
    let dot := fused m.gravity[2]! inertiaPosition[3*i+2]!
      (fused m.gravity[0]! inertiaPosition[3*i]! (m.gravity[1]!*inertiaPosition[3*i+1]!))
    value := fused (-m.bodyMass[i]!) dot value
  let half := Float.ofBits 0x3FE0000000000000
  for j in [1:m.stiffness.size] do
    if m.stiffness[j]! != zero then
      let address := m.jointPosition[j]!
      let x := position[address]!-m.springPosition[address]!
      value := fused (half*m.stiffness[j]!) (x*x) value
  return value

def kinetic (m : Material) (mass velocity : Array Float) : Float :=
  let matrix : FlyCNS.C3Sparse.Matrix := ⟨velocity.size,velocity.size,mass,m.rowStart,m.rowCount,m.columns⟩
  (Float.ofBits 0x3FE0000000000000)*FlyCNS.C3Sparse.dot (FlyCNS.C3Sparse.symmetricMultiply matrix velocity) velocity

end FlyCNS.C3Diagnostics

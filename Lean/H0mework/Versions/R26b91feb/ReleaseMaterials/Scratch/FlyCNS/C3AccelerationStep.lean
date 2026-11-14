import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ActuationStep

/-! C7's complete no-sleep/no-applied-body-force smooth acceleration stage.
The present factorization/passive/bias are upstream original current-position
operators. No acceleration, constraint solution or future state is input. -/

set_option autoImplicit false

namespace FlyCNS.C3Acceleration
open FlyCNS.C3Actuation

structure Frame where
  passive : Array Float
  bias : Array Float
  applied : Array Float
  actuator : Array Float
  factor : Array Float
  diagonalInverse : Array Float
  rowStart : Array Nat
  rowCount : Array Nat
  columns : Array Nat

structure Result where
  force : Array Float
  acceleration : Array Float

def dot (frame : Frame) (x : Array Float) (start length : Nat) : Float := Id.run do
  let mut lanes := Array.replicate 4 zero
  for chunk in [:length/4] do
    for lane in [:4] do
      let index := start+4*chunk+lane
      lanes := lanes.set! lane (fused frame.factor[index]! x[frame.columns[index]!]! lanes[lane]!)
  let mut result := (lanes[0]!+lanes[2]!) + (lanes[1]!+lanes[3]!)
  for index in [start+4*(length/4):start+length] do
    result := fused frame.factor[index]! x[frame.columns[index]!]! result
  return result

def solveLD (frame : Frame) (rhs : Array Float) : Array Float := Id.run do
  let nv := rhs.size
  let mut x := rhs
  for reverse in [:nv] do
    let row := nv-reverse-1
    let value := x[row]!
    if frame.rowCount[row]! != 1 && value.toModel.beq zero.toModel == false then
      for index in [frame.rowStart[row]!:frame.rowStart[row]!+frame.rowCount[row]!-1] do
        let column := frame.columns[index]!
        x := x.set! column (fused (-frame.factor[index]!) value x[column]!)
  for row in [:nv] do x := x.set! row (x[row]!*frame.diagonalInverse[row]!)
  for row in [:nv] do
    if frame.rowCount[row]! > 1 then
      x := x.set! row (x[row]! - dot frame x frame.rowStart[row]! (frame.rowCount[row]!-1))
  return x

def acceleration (frame : Frame) : Result :=
  let rhs := frame.passive.mapIdx fun row value =>
    ((value-frame.bias[row]!)+frame.applied[row]!)+frame.actuator[row]!
  ⟨rhs,solveLD frame rhs⟩

end FlyCNS.C3Acceleration

import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ActuationStep

/-! Concrete C7 sparse factorization, before constraint projection. Its input
is the inertia matrix produced from the current pose, never qLD/diaginv. -/

set_option autoImplicit false

namespace FlyCNS.C3Factor
open FlyCNS.C3Actuation

structure Frame where
  matrix : Array Float
  rowStart : Array Nat
  rowCount : Array Nat
  columns : Array Nat

structure Result where
  factor : Array Float
  diagonalInverse : Array Float

def factor (frame : Frame) : Result := Id.run do
  let nv := frame.rowCount.size
  let mut matrix := frame.matrix
  let mut inverse := Array.replicate nv zero
  for reverse in [:nv] do
    let row := nv-reverse-1
    let start := frame.rowStart[row]!
    let count := frame.rowCount[row]!-1
    let diagonal := start+count
    let value := (UInt64.ofNat 1).toFloat / matrix[diagonal]!
    inverse := inverse.set! row value
    for offset in [:count] do
      let address := diagonal-offset-1
      let previous := frame.columns[address]!
      let scale := -matrix[address]!*value
      for entry in [:frame.rowCount[previous]!] do
        let target := frame.rowStart[previous]!+entry
        matrix := matrix.set! target (fused matrix[start+entry]! scale matrix[target]!)
    for entry in [:count] do
      matrix := matrix.set! (start+entry) (matrix[start+entry]!*value)
  return ⟨matrix,inverse⟩

end FlyCNS.C3Factor

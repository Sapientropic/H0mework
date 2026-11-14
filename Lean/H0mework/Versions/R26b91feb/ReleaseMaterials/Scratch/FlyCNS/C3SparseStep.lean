import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3AccelerationStep

/-! Concrete sparse algebra for the original C7 pyramidal Newton solver.
Rows and fill are generated from the present M/J pattern, not supplied factors.
Float.sqrt has the pinned toolchain's executable IEEE Float.Model definition. -/

set_option autoImplicit false

namespace FlyCNS.C3Sparse
open FlyCNS.C3Actuation

structure Matrix where
  rows : Nat
  cols : Nat
  values : Array Float
  starts : Array Nat
  counts : Array Nat
  columns : Array Nat
  deriving Inhabited

def dotIndexed (a x : Array Float) (indices : Array Nat) (start length : Nat) : Float := Id.run do
  let mut lanes := Array.replicate 4 zero
  for chunk in [:length/4] do
    for lane in [:4] do
      let i := start+4*chunk+lane
      lanes := lanes.set! lane (fused a[i]! x[indices[i]!]! lanes[lane]!)
  let mut result := (lanes[0]!+lanes[2]!) + (lanes[1]!+lanes[3]!)
  for i in [start+4*(length/4):start+length] do
    result := fused a[i]! x[indices[i]!]! result
  return result

def dot (a b : Array Float) : Float := Id.run do
  let mut lanes := Array.replicate 4 zero
  for chunk in [:a.size/4] do
    for lane in [:4] do
      let i := 4*chunk+lane
      lanes := lanes.set! lane (fused a[i]! b[i]! lanes[lane]!)
  let mut result := (lanes[0]!+lanes[2]!) + (lanes[1]!+lanes[3]!)
  let i := 4*(a.size/4)
  let tail := a.size-i
  if tail == 3 then
    result := result + (fused a[i+2]! b[i+2]! (fused a[i]! b[i]! (a[i+1]!*b[i+1]!)))
  else if tail == 2 then
    result := result + (fused a[i]! b[i]! (a[i+1]!*b[i+1]!))
  else if tail == 1 then result := fused a[i]! b[i]! result
  return result

def multiply (m : Matrix) (x : Array Float) : Array Float :=
  (List.range m.rows).toArray.map fun row => dotIndexed m.values x m.columns m.starts[row]! m.counts[row]!

def transpose (m : Matrix) : Matrix := Id.run do
  let mut counts := Array.replicate m.cols 0
  for c in m.columns do counts := counts.set! c (counts[c]!+1)
  let mut starts := Array.replicate m.cols 0
  for r in [1:m.cols] do starts := starts.set! r (starts[r-1]!+counts[r-1]!)
  let mut cursor := starts
  let mut values := Array.replicate m.values.size zero
  let mut columns := Array.replicate m.values.size 0
  for r in [:m.rows] do
    for k in [m.starts[r]!:m.starts[r]!+m.counts[r]!] do
      let c := m.columns[k]!
      let address := cursor[c]!
      values := values.set! address m.values[k]!
      columns := columns.set! address r
      cursor := cursor.set! c (address+1)
  return ⟨m.cols,m.rows,values,starts,counts,columns⟩

def symmetricMultiply (m : Matrix) (x : Array Float) : Array Float := Id.run do
  let mut result := Array.replicate m.rows zero
  for r in [:m.rows] do
    let address := m.starts[r]!+m.counts[r]!-1
    result := result.set! r (m.values[address]!*x[r]!)
    for back in [:m.counts[r]!-1] do
      let k := address-back-1
      let c := m.columns[k]!
      result := result.set! r (fused m.values[k]! x[c]! result[r]!)
      result := result.set! c (fused m.values[k]! x[r]! result[c]!)
  return result

def transposeScatterMultiply (m : Matrix) (x : Array Float) : Array Float := Id.run do
  let mut result := Array.replicate m.cols zero
  for r in [:m.rows] do
    if x[r]! != zero then
      for k in [m.starts[r]!:m.starts[r]!+m.counts[r]!] do
        let c := m.columns[k]!
        result := result.set! c (fused m.values[k]! x[r]! result[c]!)
  return result

def solveLD (m : Matrix) (factor inverse rhs : Array Float) : Array Float :=
  FlyCNS.C3Acceleration.solveLD ⟨#[],#[],#[],#[],factor,inverse,m.starts,m.counts,m.columns⟩ rhs

structure Cholesky where
  matrix : Matrix
  rank : Nat

def minimum : Float := Float.ofBits 0x3CD203AF9EE75616 -- 1e-15, original mjMINVAL

def hessian (mass jacobian : Matrix) (diagonal : Array Float) : Matrix := Id.run do
  let n := mass.rows
  let jt := transpose jacobian
  let mut rows : Array (Array Nat) := Array.replicate n #[]
  let mut nums : Array (Array Float) := Array.replicate n #[]
  for r in [:n] do
    let mut buffer := Array.replicate n zero
    let mut pattern := Array.replicate n false
    for k in [jt.starts[r]!:jt.starts[r]!+jt.counts[r]!] do
      let j := jt.columns[k]!
      let scale := diagonal[j]!*jt.values[k]!
      for index in [jacobian.starts[j]!:jacobian.starts[j]!+jacobian.counts[j]!] do
        let c := jacobian.columns[index]!
        if c <= r then
          pattern := pattern.set! c true
          if diagonal[j]! != zero then buffer := buffer.set! c (fused scale jacobian.values[index]! buffer[c]!)
    for k in [mass.starts[r]!:mass.starts[r]!+mass.counts[r]!] do
      let c := mass.columns[k]!
      buffer := buffer.set! c (if pattern[c]! then buffer[c]!+mass.values[k]! else mass.values[k]!)
      pattern := pattern.set! c true
    for c in [:r+1] do
      if pattern[c]! then
        rows := rows.set! r (rows[r]!.push c)
        nums := nums.set! r (nums[r]!.push buffer[c]!)
  let mut starts := #[]
  let mut counts := #[]
  let mut values := #[]
  let mut columns := #[]
  for r in [:n] do
    starts := starts.push values.size
    counts := counts.push rows[r]!.size
    values := values ++ nums[r]!
    columns := columns ++ rows[r]!
  return ⟨n,n,values,starts,counts,columns⟩

def cholesky (h : Matrix) : Cholesky := Id.run do
  let n := h.rows
  let mut pattern := Array.replicate (n*n) false
  for r in [:n] do
    for k in [h.starts[r]!:h.starts[r]!+h.counts[r]!] do pattern := pattern.set! (r*n+h.columns[k]!) true
  for reverse in [:n] do
    let r := n-reverse-1
    for c in [:r] do
      if pattern[r*n+c]! then
        for j in [:c+1] do
          if pattern[r*n+j]! then pattern := pattern.set! (c*n+j) true
  let mut starts := #[]
  let mut counts := #[]
  let mut columns := #[]
  for r in [:n] do
    starts := starts.push columns.size
    let first := columns.size
    for c in [:r+1] do if pattern[r*n+c]! then columns := columns.push c
    counts := counts.push (columns.size-first)
  let mut result : Matrix := ⟨n,n,Array.replicate columns.size zero,starts,counts,columns⟩
  let mut rank := n
  for reverse in [:n] do
    let r := n-reverse-1
    let mut dense := Array.replicate n zero
    for k in [h.starts[r]!:h.starts[r]!+h.counts[r]!] do dense := dense.set! h.columns[k]! h.values[k]!
    for c in [r+1:n] do
      if pattern[c*n+r]! then
        let index := (List.range result.counts[c]!).find? fun k => result.columns[result.starts[c]!+k]! == r
        let address := result.starts[c]!+index.getD 0
        let lcr := result.values[address]!
        for k in [result.starts[c]!:address+1] do
          let j := result.columns[k]!
          dense := dense.set! j (fused (-lcr) result.values[k]! dense[j]!)
    let mut diagonal := dense[r]!
    if diagonal < minimum then
      diagonal := minimum
      rank := rank-1
    let root := diagonal.sqrt
    let inverse := (Float.ofBits 0x3FF0000000000000)/root
    for k in [result.starts[r]!:result.starts[r]!+result.counts[r]!-1] do
      result := {result with values := result.values.set! k (dense[result.columns[k]!]!*inverse)}
    result := {result with values := result.values.set! (result.starts[r]!+result.counts[r]!-1) root}
  return ⟨result,rank⟩

def cholSolve (m : Matrix) (rhs : Array Float) : Array Float := Id.run do
  let mut x := rhs
  for reverse in [:m.rows] do
    let r := m.rows-reverse-1
    let address := m.starts[r]!+m.counts[r]!-1
    if x[r]! != zero then
      x := x.set! r (x[r]!/m.values[address]!)
      let value := x[r]!
      for k in [m.starts[r]!:address] do
        let c := m.columns[k]!
        x := x.set! c (fused (-m.values[k]!) value x[c]!)
  for r in [:m.rows] do
    let address := m.starts[r]!+m.counts[r]!-1
    if m.counts[r]! > 1 then x := x.set! r (x[r]!-dotIndexed m.values x m.columns m.starts[r]! (m.counts[r]!-1))
    x := x.set! r (x[r]!/m.values[address]!)
  return x

def cholUpdate (m : Matrix) (row : Array Float) (plus : Bool) : Cholesky := Id.run do
  let mut result := m
  let mut dense := row
  let mut rank := m.rows
  for reverse in [:m.rows] do
    let r := m.rows-reverse-1
    if dense[r]! != zero then
      let address := m.starts[r]!+m.counts[r]!-1
      let diagonal := result.values[address]!
      let value := dense[r]!
      let square := value*value
      let mut tmp := fused diagonal diagonal (if plus then square else -square)
      if tmp < minimum then
        tmp := minimum
        rank := rank-1
      let root := tmp.sqrt
      result := {result with values := result.values.set! address root}
      let c := diagonal/root
      let s := -value/root
      let signed := if plus then -s else s
      for k in [m.starts[r]!:address] do
        let j := m.columns[k]!
        let dj := dense[j]!
        let lv := result.values[k]!
        result := {result with values := result.values.set! k (fused c lv (signed*dj))}
        dense := dense.set! j (fused s lv (c*dj))
  return ⟨result,rank⟩

end FlyCNS.C3Sparse
